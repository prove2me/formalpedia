-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1666_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:19:35.724331+00:00
-- url     : https://prove2.me/submissions/854e48b3-9c99-4fb1-b145-ba519627e010

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
theorem support_rectangle_w1666_s3_0 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-786417973/5000000000 : ℝ)*x 0 + (5442887447/10000000000 : ℝ)*x 1 + (5184817351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (786417973/5000000000 : ℝ)^4983 ≤ (9747756023793/100000000000000 : ℝ)^3959 := by
    have hnat : (786417973 : ℕ)^4983*100000000000000^3959 ≤ 9747756023793^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786417973 5000000000 9747756023793 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442887447/10000000000 : ℝ)^4983 ≤ (46505177435757/100000000000000 : ℝ)^3959 := by
    have hnat : (5442887447 : ℕ)^4983*100000000000000^3959 ≤ 46505177435757^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442887447 10000000000 46505177435757 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184817351/10000000000 : ℝ)^4983 ≤ (8749413306847/20000000000000 : ℝ)^3959 := by
    have hnat : (5184817351 : ℕ)^4983*20000000000000^3959 ≤ 8749413306847^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184817351 10000000000 8749413306847 20000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-786417973/5000000000 : ℝ), (5442887447/10000000000 : ℝ), (5184817351/10000000000 : ℝ)] ![(9747756023793/100000000000000 : ℝ), (46505177435757/100000000000000 : ℝ), (8749413306847/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-786417973/5000000000 : ℝ)|^4983 ≤ (9747756023793/100000000000000 : ℝ)^3959
        have hw : |(-786417973/5000000000 : ℝ)|=(786417973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442887447/10000000000 : ℝ)|^4983 ≤ (46505177435757/100000000000000 : ℝ)^3959
        have hw : |(5442887447/10000000000 : ℝ)|=(5442887447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184817351/10000000000 : ℝ)|^4983 ≤ (8749413306847/20000000000000 : ℝ)^3959
        have hw : |(5184817351/10000000000 : ℝ)|=(5184817351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s3_1 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345324747/10000000000 : ℝ)*x 0 + (-852803117/5000000000 : ℝ)*x 1 + (5184817381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345324747/10000000000 : ℝ)^4983 ≤ (9091682714801/20000000000000 : ℝ)^3959 := by
    have hnat : (5345324747 : ℕ)^4983*20000000000000^3959 ≤ 9091682714801^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345324747 10000000000 9091682714801 20000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (852803117/5000000000 : ℝ)^4983 ≤ (10794519559109/100000000000000 : ℝ)^3959 := by
    have hnat : (852803117 : ℕ)^4983*100000000000000^3959 ≤ 10794519559109^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852803117 5000000000 10794519559109 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184817381/10000000000 : ℝ)^4983 ≤ (1367095839151/3125000000000 : ℝ)^3959 := by
    have hnat : (5184817381 : ℕ)^4983*3125000000000^3959 ≤ 1367095839151^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184817381 10000000000 1367095839151 3125000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345324747/10000000000 : ℝ), (-852803117/5000000000 : ℝ), (5184817381/10000000000 : ℝ)] ![(9091682714801/20000000000000 : ℝ), (10794519559109/100000000000000 : ℝ), (1367095839151/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345324747/10000000000 : ℝ)|^4983 ≤ (9091682714801/20000000000000 : ℝ)^3959
        have hw : |(5345324747/10000000000 : ℝ)|=(5345324747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-852803117/5000000000 : ℝ)|^4983 ≤ (10794519559109/100000000000000 : ℝ)^3959
        have hw : |(-852803117/5000000000 : ℝ)|=(852803117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184817381/10000000000 : ℝ)|^4983 ≤ (1367095839151/3125000000000 : ℝ)^3959
        have hw : |(5184817381/10000000000 : ℝ)|=(5184817381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s3_2 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069064953/2000000000 : ℝ)*x 0 + (5184817357/10000000000 : ℝ)*x 1 + (-1705606241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069064953/2000000000 : ℝ)^4983 ≤ (45458413766677/100000000000000 : ℝ)^3959 := by
    have hnat : (1069064953 : ℕ)^4983*100000000000000^3959 ≤ 45458413766677^3959*2000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069064953 2000000000 45458413766677 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184817357/10000000000 : ℝ)^4983 ≤ (21873533298977/50000000000000 : ℝ)^3959 := by
    have hnat : (5184817357 : ℕ)^4983*50000000000000^3959 ≤ 21873533298977^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184817357 10000000000 21873533298977 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1705606241/10000000000 : ℝ)^4983 ≤ (10794519614869/100000000000000 : ℝ)^3959 := by
    have hnat : (1705606241 : ℕ)^4983*100000000000000^3959 ≤ 10794519614869^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705606241 10000000000 10794519614869 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069064953/2000000000 : ℝ), (5184817357/10000000000 : ℝ), (-1705606241/10000000000 : ℝ)] ![(45458413766677/100000000000000 : ℝ), (21873533298977/50000000000000 : ℝ), (10794519614869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069064953/2000000000 : ℝ)|^4983 ≤ (45458413766677/100000000000000 : ℝ)^3959
        have hw : |(1069064953/2000000000 : ℝ)|=(1069064953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184817357/10000000000 : ℝ)|^4983 ≤ (21873533298977/50000000000000 : ℝ)^3959
        have hw : |(5184817357/10000000000 : ℝ)|=(5184817357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1705606241/10000000000 : ℝ)|^4983 ≤ (10794519614869/100000000000000 : ℝ)^3959
        have hw : |(-1705606241/10000000000 : ℝ)|=(1705606241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s3_3 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (260539257/625000000 : ℝ)*x 0 + (1918951437/5000000000 : ℝ)*x 1 + (4519071543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260539257/625000000 : ℝ)^4983 ≤ (3324328521021/10000000000000 : ℝ)^3959 := by
    have hnat : (260539257 : ℕ)^4983*10000000000000^3959 ≤ 3324328521021^3959*625000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260539257 625000000 3324328521021 10000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1918951437/5000000000 : ℝ)^4983 ≤ (149792270443/500000000000 : ℝ)^3959 := by
    have hnat : (1918951437 : ℕ)^4983*500000000000^3959 ≤ 149792270443^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918951437 5000000000 149792270443 500000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4519071543/10000000000 : ℝ)^4983 ≤ (36798260679731/100000000000000 : ℝ)^3959 := by
    have hnat : (4519071543 : ℕ)^4983*100000000000000^3959 ≤ 36798260679731^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519071543 10000000000 36798260679731 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(260539257/625000000 : ℝ), (1918951437/5000000000 : ℝ), (4519071543/10000000000 : ℝ)] ![(3324328521021/10000000000000 : ℝ), (149792270443/500000000000 : ℝ), (36798260679731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(260539257/625000000 : ℝ)|^4983 ≤ (3324328521021/10000000000000 : ℝ)^3959
        have hw : |(260539257/625000000 : ℝ)|=(260539257/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1918951437/5000000000 : ℝ)|^4983 ≤ (149792270443/500000000000 : ℝ)^3959
        have hw : |(1918951437/5000000000 : ℝ)|=(1918951437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4519071543/10000000000 : ℝ)|^4983 ≤ (36798260679731/100000000000000 : ℝ)^3959
        have hw : |(4519071543/10000000000 : ℝ)|=(4519071543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s3_4 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-196612313/1250000000 : ℝ)*x 0 + (2593391909/5000000000 : ℝ)*x 1 + (1088179993/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196612313/1250000000 : ℝ)^4983 ≤ (4874122007333/50000000000000 : ℝ)^3959 := by
    have hnat : (196612313 : ℕ)^4983*50000000000000^3959 ≤ 4874122007333^3959*1250000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196612313 1250000000 4874122007333 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593391909/5000000000 : ℝ)^4983 ≤ (43767951262193/100000000000000 : ℝ)^3959 := by
    have hnat : (2593391909 : ℕ)^4983*100000000000000^3959 ≤ 43767951262193^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593391909 5000000000 43767951262193 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088179993/2000000000 : ℝ)^4983 ≤ (11620951176059/25000000000000 : ℝ)^3959 := by
    have hnat : (1088179993 : ℕ)^4983*25000000000000^3959 ≤ 11620951176059^3959*2000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088179993 2000000000 11620951176059 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-196612313/1250000000 : ℝ), (2593391909/5000000000 : ℝ), (1088179993/2000000000 : ℝ)] ![(4874122007333/50000000000000 : ℝ), (43767951262193/100000000000000 : ℝ), (11620951176059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-196612313/1250000000 : ℝ)|^4983 ≤ (4874122007333/50000000000000 : ℝ)^3959
        have hw : |(-196612313/1250000000 : ℝ)|=(196612313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593391909/5000000000 : ℝ)|^4983 ≤ (43767951262193/100000000000000 : ℝ)^3959
        have hw : |(2593391909/5000000000 : ℝ)|=(2593391909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1088179993/2000000000 : ℝ)|^4983 ≤ (11620951176059/25000000000000 : ℝ)^3959
        have hw : |(1088179993/2000000000 : ℝ)|=(1088179993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s3_5 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638130593/5000000000 : ℝ)*x 0 + (-144952389/1000000000 : ℝ)*x 1 + (340056237/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638130593/5000000000 : ℝ)^4983 ≤ (44720397340797/100000000000000 : ℝ)^3959 := by
    have hnat : (2638130593 : ℕ)^4983*100000000000000^3959 ≤ 44720397340797^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638130593 5000000000 44720397340797 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (144952389/1000000000 : ℝ)^4983 ≤ (8795799806141/100000000000000 : ℝ)^3959 := by
    have hnat : (144952389 : ℕ)^4983*100000000000000^3959 ≤ 8795799806141^3959*1000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144952389 1000000000 8795799806141 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340056237/625000000 : ℝ)^4983 ≤ (23241901421969/50000000000000 : ℝ)^3959 := by
    have hnat : (340056237 : ℕ)^4983*50000000000000^3959 ≤ 23241901421969^3959*625000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340056237 625000000 23241901421969 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638130593/5000000000 : ℝ), (-144952389/1000000000 : ℝ), (340056237/625000000 : ℝ)] ![(44720397340797/100000000000000 : ℝ), (8795799806141/100000000000000 : ℝ), (23241901421969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638130593/5000000000 : ℝ)|^4983 ≤ (44720397340797/100000000000000 : ℝ)^3959
        have hw : |(2638130593/5000000000 : ℝ)|=(2638130593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-144952389/1000000000 : ℝ)|^4983 ≤ (8795799806141/100000000000000 : ℝ)^3959
        have hw : |(-144952389/1000000000 : ℝ)|=(144952389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(340056237/625000000 : ℝ)|^4983 ≤ (23241901421969/50000000000000 : ℝ)^3959
        have hw : |(340056237/625000000 : ℝ)|=(340056237/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s3_6 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659532689/1250000000 : ℝ)*x 0 + (5440899629/10000000000 : ℝ)*x 1 + (-1449523663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659532689/1250000000 : ℝ)^4983 ≤ (44720400818579/100000000000000 : ℝ)^3959 := by
    have hnat : (659532689 : ℕ)^4983*100000000000000^3959 ≤ 44720400818579^3959*1250000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659532689 1250000000 44720400818579 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440899629/10000000000 : ℝ)^4983 ≤ (46483801091173/100000000000000 : ℝ)^3959 := by
    have hnat : (5440899629 : ℕ)^4983*100000000000000^3959 ≤ 46483801091173^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440899629 10000000000 46483801091173 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1449523663/10000000000 : ℝ)^4983 ≤ (2198949518103/25000000000000 : ℝ)^3959 := by
    have hnat : (1449523663 : ℕ)^4983*25000000000000^3959 ≤ 2198949518103^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1449523663 10000000000 2198949518103 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659532689/1250000000 : ℝ), (5440899629/10000000000 : ℝ), (-1449523663/10000000000 : ℝ)] ![(44720400818579/100000000000000 : ℝ), (46483801091173/100000000000000 : ℝ), (2198949518103/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659532689/1250000000 : ℝ)|^4983 ≤ (44720400818579/100000000000000 : ℝ)^3959
        have hw : |(659532689/1250000000 : ℝ)|=(659532689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440899629/10000000000 : ℝ)|^4983 ≤ (46483801091173/100000000000000 : ℝ)^3959
        have hw : |(5440899629/10000000000 : ℝ)|=(5440899629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1449523663/10000000000 : ℝ)|^4983 ≤ (2198949518103/25000000000000 : ℝ)^3959
        have hw : |(-1449523663/10000000000 : ℝ)|=(1449523663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s3_7 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (833758373/2000000000 : ℝ)*x 0 + (4513880073/10000000000 : ℝ)*x 1 + (1921574703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (833758373/2000000000 : ℝ)^4983 ≤ (33244928853759/100000000000000 : ℝ)^3959 := by
    have hnat : (833758373 : ℕ)^4983*100000000000000^3959 ≤ 33244928853759^3959*2000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833758373 2000000000 33244928853759 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4513880073/10000000000 : ℝ)^4983 ≤ (18372530484953/50000000000000 : ℝ)^3959 := by
    have hnat : (4513880073 : ℕ)^4983*50000000000000^3959 ≤ 18372530484953^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513880073 10000000000 18372530484953 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1921574703/5000000000 : ℝ)^4983 ≤ (6002002033461/20000000000000 : ℝ)^3959 := by
    have hnat : (1921574703 : ℕ)^4983*20000000000000^3959 ≤ 6002002033461^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921574703 5000000000 6002002033461 20000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(833758373/2000000000 : ℝ), (4513880073/10000000000 : ℝ), (1921574703/5000000000 : ℝ)] ![(33244928853759/100000000000000 : ℝ), (18372530484953/50000000000000 : ℝ), (6002002033461/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(833758373/2000000000 : ℝ)|^4983 ≤ (33244928853759/100000000000000 : ℝ)^3959
        have hw : |(833758373/2000000000 : ℝ)|=(833758373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4513880073/10000000000 : ℝ)|^4983 ≤ (18372530484953/50000000000000 : ℝ)^3959
        have hw : |(4513880073/10000000000 : ℝ)|=(4513880073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1921574703/5000000000 : ℝ)|^4983 ≤ (6002002033461/20000000000000 : ℝ)^3959
        have hw : |(1921574703/5000000000 : ℝ)|=(1921574703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1666_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181973587/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10697/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10747/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16239/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3259/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10697/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3259/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10697/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3259/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10697/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3259/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10697/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3259/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10697/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3259/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10697/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10697/100000 : ℝ) ^ (4979/1024 : ℝ) ≤ (1905355648763129/100000000000000000000 : ℝ) := by
    have hpowers : (10697/100000 : ℝ)^4979 ≤ (1905355648763129/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10697 : ℕ)^4979*100000000000000000000^1024 ≤ 1905355648763129^1024*100000^4979 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10697 100000 1905355648763129 100000000000000000000 4979 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10697/100000 : ℝ)) (X := (1905355648763129/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3259/20000 : ℝ) ^ (4979/1024 : ℝ) ≤ (14749192520269337/100000000000000000000 : ℝ) := by
    have hpowers : (3259/20000 : ℝ)^4979 ≤ (14749192520269337/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3259 : ℕ)^4979*100000000000000000000^1024 ≤ 14749192520269337^1024*20000^4979 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3259 20000 14749192520269337 100000000000000000000 4979 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3259/20000 : ℝ)) (X := (14749192520269337/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001905355648763129/50000000000000000000 : ℝ) ≤ (10000078371345873/10000000000000000 : ℝ) ^ (4979/1024 : ℝ) := by
    have hpowers : (50001905355648763129/50000000000000000000 : ℝ)^1024 ≤ (10000078371345873/10000000000000000 : ℝ)^4979 := by
      have hnat : (50001905355648763129 : ℕ)^1024*10000000000000000^4979 ≤ 10000078371345873^4979*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001905355648763129 50000000000000000000 10000078371345873 10000000000000000 1024 4979 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000078371345873/10000000000000000 : ℝ)) (X := (50001905355648763129/50000000000000000000 : ℝ)) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50008327274084516233/50000000000000000000 : ℝ) ≤ (625021406318233/625000000000000 : ℝ) ^ (4979/1024 : ℝ) := by
    have hpowers : (50008327274084516233/50000000000000000000 : ℝ)^1024 ≤ (625021406318233/625000000000000 : ℝ)^4979 := by
      have hnat : (50008327274084516233 : ℕ)^1024*625000000000000^4979 ≤ 625021406318233^4979*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008327274084516233 50000000000000000000 625021406318233 625000000000000 1024 4979 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625021406318233/625000000000000 : ℝ)) (X := (50008327274084516233/50000000000000000000 : ℝ)) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50014749192520269337/50000000000000000000 : ℝ) ≤ (10000606630837583/10000000000000000 : ℝ) ^ (4979/1024 : ℝ) := by
    have hpowers : (50014749192520269337/50000000000000000000 : ℝ)^1024 ≤ (10000606630837583/10000000000000000 : ℝ)^4979 := by
      have hnat : (50014749192520269337 : ℕ)^1024*10000000000000000^4979 ≤ 10000606630837583^4979*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014749192520269337 50000000000000000000 10000606630837583 10000000000000000 1024 4979 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000606630837583/10000000000000000 : ℝ)) (X := (50014749192520269337/50000000000000000000 : ℝ)) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1905355648763129/100000000000000000000 : ℝ) ≤ ((3498424245688210949/3498750000000000000 : ℝ)+2*(52825949171/111960000000000 : ℝ)*(10697/100000 : ℝ))^(4979/1024 : ℝ) := by
    rw [show (3498424245688210949/3498750000000000000 : ℝ)+2*(52825949171/111960000000000 : ℝ)*(10697/100000 : ℝ)=(10000078371345873/10000000000000000 : ℝ) by norm_num, show 1+2*(1905355648763129/100000000000000000000 : ℝ)=(50001905355648763129/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14749192520269337/100000000000000000000 : ℝ)+(1905355648763129/100000000000000000000 : ℝ) ≤ ((3498424245688210949/3498750000000000000 : ℝ)+(52825949171/111960000000000 : ℝ)*((3259/20000 : ℝ)+(10697/100000 : ℝ)))^(4979/1024 : ℝ) := by
    rw [show (3498424245688210949/3498750000000000000 : ℝ)+(52825949171/111960000000000 : ℝ)*((3259/20000 : ℝ)+(10697/100000 : ℝ))=(625021406318233/625000000000000 : ℝ) by norm_num, show 1+(14749192520269337/100000000000000000000 : ℝ)+(1905355648763129/100000000000000000000 : ℝ)=(50008327274084516233/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14749192520269337/100000000000000000000 : ℝ) ≤ ((3498424245688210949/3498750000000000000 : ℝ)+2*(52825949171/111960000000000 : ℝ)*(3259/20000 : ℝ))^(4979/1024 : ℝ) := by
    rw [show (3498424245688210949/3498750000000000000 : ℝ)+2*(52825949171/111960000000000 : ℝ)*(3259/20000 : ℝ)=(10000606630837583/10000000000000000 : ℝ) by norm_num, show 1+2*(14749192520269337/100000000000000000000 : ℝ)=(50014749192520269337/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3498424245688210949/3498750000000000000 : ℝ)*(X 1 0+X 2 0)+(52825949171/111960000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4979/1024 : ℝ)) (lo := (10697/100000 : ℝ)) (hi := (3259/20000 : ℝ)) (c := (3498424245688210949/3498750000000000000 : ℝ)) (alpha := (52825949171/111960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3498424245688210949/3498750000000000000 : ℝ)*(X 0 1+X 2 1)+(52825949171/111960000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4979/1024 : ℝ)) (lo := (10697/100000 : ℝ)) (hi := (3259/20000 : ℝ)) (c := (3498424245688210949/3498750000000000000 : ℝ)) (alpha := (52825949171/111960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3498424245688210949/3498750000000000000 : ℝ)*(X 0 2+X 1 2)+(52825949171/111960000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4979/1024 : ℝ)) (lo := (10697/100000 : ℝ)) (hi := (3259/20000 : ℝ)) (c := (3498424245688210949/3498750000000000000 : ℝ)) (alpha := (52825949171/111960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-786417973/5000000000 : ℝ)*X 0 0+(5442887447/10000000000 : ℝ)*X 0 1+(5184817351/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345324747/10000000000 : ℝ)*X 1 0+(-852803117/5000000000 : ℝ)*X 1 1+(5184817381/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069064953/2000000000 : ℝ)*X 2 0+(5184817357/10000000000 : ℝ)*X 2 1+(-1705606241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((260539257/625000000 : ℝ)*X 0 0+(1918951437/5000000000 : ℝ)*X 0 1+(4519071543/10000000000 : ℝ)*X 0 2+(260539257/625000000 : ℝ)*X 1 0+(1918951437/5000000000 : ℝ)*X 1 1+(4519071543/10000000000 : ℝ)*X 1 2+(260539257/625000000 : ℝ)*X 2 0+(1918951437/5000000000 : ℝ)*X 2 1+(4519071543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-196612313/1250000000 : ℝ)*X 0 0+(2593391909/5000000000 : ℝ)*X 0 1+(1088179993/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638130593/5000000000 : ℝ)*X 1 0+(-144952389/1000000000 : ℝ)*X 1 1+(340056237/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((659532689/1250000000 : ℝ)*X 2 0+(5440899629/10000000000 : ℝ)*X 2 1+(-1449523663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((833758373/2000000000 : ℝ)*X 0 0+(4513880073/10000000000 : ℝ)*X 0 1+(1921574703/5000000000 : ℝ)*X 0 2+(833758373/2000000000 : ℝ)*X 1 0+(4513880073/10000000000 : ℝ)*X 1 1+(1921574703/5000000000 : ℝ)*X 1 2+(833758373/2000000000 : ℝ)*X 2 0+(4513880073/10000000000 : ℝ)*X 2 1+(1921574703/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14491658782598126352221483/1457812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (386517719/25000000000000 : ℝ)*(base19) + (1459926307/100000000000000 : ℝ)*(base23) + (53021989/100000000000000 : ℝ)*(lower2) + (245974197/100000000000000 : ℝ)*(upper3) + (85645451/50000000000000 : ℝ)*(upper5) + (133575937874083/5000000000000 : ℝ)*(major0) + (133575937874083/5000000000000 : ℝ)*(major1) + (133575937874083/5000000000000 : ℝ)*(major2) + (1937468378709141/50000000000000 : ℝ)*(sp0) + (774991026234071/20000000000000 : ℝ)*(sp1) + (968738804328731/25000000000000 : ℝ)*(sp2) + (734036178439581/50000000000000 : ℝ)*(sp3) + (4979955737/25000000000000 : ℝ)*(sp4) + (4074743333/50000000000000 : ℝ)*(sp7) + (367020126591457/25000000000000 : ℝ)*(f.failure) + (3874956677241231/100000000000000 : ℝ)*(f.sum) + (2162507461/6997500000000000000000000 : ℝ)*base66 + (2876791709110113/1943750000000000000000000000000 : ℝ)*base67 + (14794242822610113/1943750000000000000000000000000 : ℝ)*base69 + (5219458114453863/1943750000000000000000000000000 : ℝ)*base71 + (5523022451867/1399500000000000000000000000 : ℝ)*base74 + (13231390882908637/1943750000000000000000000000000 : ℝ)*base76 + (4428317508672613/1943750000000000000000000000000 : ℝ)*base77 + (3746086566297613/1943750000000000000000000000000 : ℝ)*base79 + (333576595013/174937500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (13846259/2500000000000000000000 : ℝ)*base89 + (13846259/2500000000000000000000 : ℝ)*base91 + (13846259/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45316719891837369288806771/7289062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (208959341/20000000000000 : ℝ)*(base19) + (1651952837/100000000000000 : ℝ)*(base23) + (34062373/20000000000000 : ℝ)*(upper2) + (66003627/100000000000000 : ℝ)*(upper3) + (153030019/50000000000000 : ℝ)*(upper5) + (1356530534906567/50000000000000 : ℝ)*(major0) + (1356530534906567/50000000000000 : ℝ)*(major1) + (1356530534906567/50000000000000 : ℝ)*(major2) + (13364857087/100000000000000 : ℝ)*(sp1) + (8257224071/50000000000000 : ℝ)*(sp2) + (245950791664577/6250000000000 : ℝ)*(sp4) + (49189978212243/1250000000000 : ℝ)*(sp5) + (983798625058063/25000000000000 : ℝ)*(sp6) + (1490909265756867/100000000000000 : ℝ)*(sp7) + (1490909265756867/100000000000000 : ℝ)*(f.failure) + (245950791664577/6250000000000 : ℝ)*(f.sum) + (35953581503/21867187500000000000000000 : ℝ)*base65 + (26027520653249537/19437500000000000000000000000000 : ℝ)*base67 + (6429528811687037/19437500000000000000000000000000 : ℝ)*base69 + (72522231595937963/19437500000000000000000000000000 : ℝ)*base72 + (295834091711/279900000000000000000000000 : ℝ)*base74 + (234892680041874537/19437500000000000000000000000000 : ℝ)*base75 + (123833958430624537/19437500000000000000000000000000 : ℝ)*base77 + (376680109560374537/19437500000000000000000000000000 : ℝ)*base79 + (8630593827539/2799000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (42128071/10000000000000000000000 : ℝ)*base90 + (42128071/10000000000000000000000 : ℝ)*base92 + (42128071/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1666_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181973587/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10697/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10747/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16239/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1666_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1666_s4_0 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-393215521/2500000000 : ℝ)*x 0 + (5442735127/10000000000 : ℝ)*x 1 + (1296238099/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393215521/2500000000 : ℝ)^4983 ≤ (9747959915657/100000000000000 : ℝ)^3959 := by
    have hnat : (393215521 : ℕ)^4983*100000000000000^3959 ≤ 9747959915657^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393215521 2500000000 9747959915657 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442735127/10000000000 : ℝ)^4983 ≤ (11625884841213/25000000000000 : ℝ)^3959 := by
    have hnat : (5442735127 : ℕ)^4983*25000000000000^3959 ≤ 11625884841213^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442735127 10000000000 11625884841213 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296238099/2500000000 : ℝ)^4983 ≤ (43748500704891/100000000000000 : ℝ)^3959 := by
    have hnat : (1296238099 : ℕ)^4983*100000000000000^3959 ≤ 43748500704891^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296238099 2500000000 43748500704891 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393215521/2500000000 : ℝ), (5442735127/10000000000 : ℝ), (1296238099/2500000000 : ℝ)] ![(9747959915657/100000000000000 : ℝ), (11625884841213/25000000000000 : ℝ), (43748500704891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393215521/2500000000 : ℝ)|^4983 ≤ (9747959915657/100000000000000 : ℝ)^3959
        have hw : |(-393215521/2500000000 : ℝ)|=(393215521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442735127/10000000000 : ℝ)|^4983 ≤ (11625884841213/25000000000000 : ℝ)^3959
        have hw : |(5442735127/10000000000 : ℝ)|=(5442735127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1296238099/2500000000 : ℝ)|^4983 ≤ (43748500704891/100000000000000 : ℝ)^3959
        have hw : |(1296238099/2500000000 : ℝ)|=(1296238099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s4_1 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345274271/10000000000 : ℝ)*x 0 + (-1705485537/10000000000 : ℝ)*x 1 + (1296239697/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345274271/10000000000 : ℝ)^4983 ≤ (22728936640113/50000000000000 : ℝ)^3959 := by
    have hnat : (5345274271 : ℕ)^4983*50000000000000^3959 ≤ 22728936640113^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345274271 10000000000 22728936640113 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1705485537/10000000000 : ℝ)^4983 ≤ (2698389529643/25000000000000 : ℝ)^3959 := by
    have hnat : (1705485537 : ℕ)^4983*25000000000000^3959 ≤ 2698389529643^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705485537 10000000000 2698389529643 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296239697/2500000000 : ℝ)^4983 ≤ (10937142146957/25000000000000 : ℝ)^3959 := by
    have hnat : (1296239697 : ℕ)^4983*25000000000000^3959 ≤ 10937142146957^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296239697 2500000000 10937142146957 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345274271/10000000000 : ℝ), (-1705485537/10000000000 : ℝ), (1296239697/2500000000 : ℝ)] ![(22728936640113/50000000000000 : ℝ), (2698389529643/25000000000000 : ℝ), (10937142146957/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345274271/10000000000 : ℝ)|^4983 ≤ (22728936640113/50000000000000 : ℝ)^3959
        have hw : |(5345274271/10000000000 : ℝ)|=(5345274271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1705485537/10000000000 : ℝ)|^4983 ≤ (2698389529643/25000000000000 : ℝ)^3959
        have hw : |(-1705485537/10000000000 : ℝ)|=(1705485537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1296239697/2500000000 : ℝ)|^4983 ≤ (10937142146957/25000000000000 : ℝ)^3959
        have hw : |(1296239697/2500000000 : ℝ)|=(1296239697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s4_2 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672639027/5000000000 : ℝ)*x 0 + (5184957723/10000000000 : ℝ)*x 1 + (-1705481873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672639027/5000000000 : ℝ)^4983 ≤ (45457913773313/100000000000000 : ℝ)^3959 := by
    have hnat : (2672639027 : ℕ)^4983*100000000000000^3959 ≤ 45457913773313^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672639027 5000000000 45457913773313 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184957723/10000000000 : ℝ)^4983 ≤ (43748557277543/100000000000000 : ℝ)^3959 := by
    have hnat : (5184957723 : ℕ)^4983*100000000000000^3959 ≤ 43748557277543^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184957723 10000000000 43748557277543 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1705481873/10000000000 : ℝ)^4983 ≤ (10793528932387/100000000000000 : ℝ)^3959 := by
    have hnat : (1705481873 : ℕ)^4983*100000000000000^3959 ≤ 10793528932387^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705481873 10000000000 10793528932387 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672639027/5000000000 : ℝ), (5184957723/10000000000 : ℝ), (-1705481873/10000000000 : ℝ)] ![(45457913773313/100000000000000 : ℝ), (43748557277543/100000000000000 : ℝ), (10793528932387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672639027/5000000000 : ℝ)|^4983 ≤ (45457913773313/100000000000000 : ℝ)^3959
        have hw : |(2672639027/5000000000 : ℝ)|=(2672639027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184957723/10000000000 : ℝ)|^4983 ≤ (43748557277543/100000000000000 : ℝ)^3959
        have hw : |(5184957723/10000000000 : ℝ)|=(5184957723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1705481873/10000000000 : ℝ)|^4983 ≤ (10793528932387/100000000000000 : ℝ)^3959
        have hw : |(-1705481873/10000000000 : ℝ)|=(1705481873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s4_3 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1042162561/2500000000 : ℝ)*x 0 + (959571987/2500000000 : ℝ)*x 1 + (56483509/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042162561/2500000000 : ℝ)^4983 ≤ (33243507355509/100000000000000 : ℝ)^3959 := by
    have hnat : (1042162561 : ℕ)^4983*100000000000000^3959 ≤ 33243507355509^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042162561 2500000000 33243507355509 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (959571987/2500000000 : ℝ)^4983 ≤ (14981118737229/50000000000000 : ℝ)^3959 := by
    have hnat : (959571987 : ℕ)^4983*50000000000000^3959 ≤ 14981118737229^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959571987 2500000000 14981118737229 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56483509/125000000 : ℝ)^4983 ≤ (18397127580731/50000000000000 : ℝ)^3959 := by
    have hnat : (56483509 : ℕ)^4983*50000000000000^3959 ≤ 18397127580731^3959*125000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56483509 125000000 18397127580731 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042162561/2500000000 : ℝ), (959571987/2500000000 : ℝ), (56483509/125000000 : ℝ)] ![(33243507355509/100000000000000 : ℝ), (14981118737229/50000000000000 : ℝ), (18397127580731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042162561/2500000000 : ℝ)|^4983 ≤ (33243507355509/100000000000000 : ℝ)^3959
        have hw : |(1042162561/2500000000 : ℝ)|=(1042162561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(959571987/2500000000 : ℝ)|^4983 ≤ (14981118737229/50000000000000 : ℝ)^3959
        have hw : |(959571987/2500000000 : ℝ)|=(959571987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56483509/125000000 : ℝ)|^4983 ≤ (18397127580731/50000000000000 : ℝ)^3959
        have hw : |(56483509/125000000 : ℝ)|=(56483509/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s4_4 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-78646459/500000000 : ℝ)*x 0 + (324182241/625000000 : ℝ)*x 1 + (170023353/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (78646459/500000000 : ℝ)^4983 ≤ (4874241654083/50000000000000 : ℝ)^3959 := by
    have hnat : (78646459 : ℕ)^4983*50000000000000^3959 ≤ 4874241654083^3959*500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78646459 500000000 4874241654083 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324182241/625000000 : ℝ)^4983 ≤ (43769353636103/100000000000000 : ℝ)^3959 := by
    have hnat : (324182241 : ℕ)^4983*100000000000000^3959 ≤ 43769353636103^3959*625000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324182241 625000000 43769353636103 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170023353/312500000 : ℝ)^4983 ≤ (46482163035237/100000000000000 : ℝ)^3959 := by
    have hnat : (170023353 : ℕ)^4983*100000000000000^3959 ≤ 46482163035237^3959*312500000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170023353 312500000 46482163035237 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-78646459/500000000 : ℝ), (324182241/625000000 : ℝ), (170023353/312500000 : ℝ)] ![(4874241654083/50000000000000 : ℝ), (43769353636103/100000000000000 : ℝ), (46482163035237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-78646459/500000000 : ℝ)|^4983 ≤ (4874241654083/50000000000000 : ℝ)^3959
        have hw : |(-78646459/500000000 : ℝ)|=(78646459/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(324182241/625000000 : ℝ)|^4983 ≤ (43769353636103/100000000000000 : ℝ)^3959
        have hw : |(324182241/625000000 : ℝ)|=(324182241/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(170023353/312500000 : ℝ)|^4983 ≤ (46482163035237/100000000000000 : ℝ)^3959
        have hw : |(170023353/312500000 : ℝ)|=(170023353/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s4_5 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638148581/5000000000 : ℝ)*x 0 + (-1449688649/10000000000 : ℝ)*x 1 + (1360186769/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638148581/5000000000 : ℝ)^4983 ≤ (44720781134647/100000000000000 : ℝ)^3959 := by
    have hnat : (2638148581 : ℕ)^4983*100000000000000^3959 ≤ 44720781134647^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638148581 5000000000 44720781134647 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1449688649/10000000000 : ℝ)^4983 ≤ (109963227293/1250000000000 : ℝ)^3959 := by
    have hnat : (1449688649 : ℕ)^4983*1250000000000^3959 ≤ 109963227293^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1449688649 10000000000 109963227293 1250000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360186769/2500000000 : ℝ)^4983 ≤ (23241080334779/50000000000000 : ℝ)^3959 := by
    have hnat : (1360186769 : ℕ)^4983*50000000000000^3959 ≤ 23241080334779^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360186769 2500000000 23241080334779 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638148581/5000000000 : ℝ), (-1449688649/10000000000 : ℝ), (1360186769/2500000000 : ℝ)] ![(44720781134647/100000000000000 : ℝ), (109963227293/1250000000000 : ℝ), (23241080334779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638148581/5000000000 : ℝ)|^4983 ≤ (44720781134647/100000000000000 : ℝ)^3959
        have hw : |(2638148581/5000000000 : ℝ)|=(2638148581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1449688649/10000000000 : ℝ)|^4983 ≤ (109963227293/1250000000000 : ℝ)^3959
        have hw : |(-1449688649/10000000000 : ℝ)|=(1449688649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360186769/2500000000 : ℝ)|^4983 ≤ (23241080334779/50000000000000 : ℝ)^3959
        have hw : |(1360186769/2500000000 : ℝ)|=(1360186769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s4_6 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055259363/2000000000 : ℝ)*x 0 + (5440747219/10000000000 : ℝ)*x 1 + (-362422233/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055259363/2000000000 : ℝ)^4983 ≤ (44720777432829/100000000000000 : ℝ)^3959 := by
    have hnat : (1055259363 : ℕ)^4983*100000000000000^3959 ≤ 44720777432829^3959*2000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055259363 2000000000 44720777432829 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440747219/10000000000 : ℝ)^4983 ≤ (46482162207249/100000000000000 : ℝ)^3959 := by
    have hnat : (5440747219 : ℕ)^4983*100000000000000^3959 ≤ 46482162207249^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440747219 10000000000 46482162207249 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (362422233/2500000000 : ℝ)^4983 ≤ (8797060344937/100000000000000 : ℝ)^3959 := by
    have hnat : (362422233 : ℕ)^4983*100000000000000^3959 ≤ 8797060344937^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362422233 2500000000 8797060344937 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055259363/2000000000 : ℝ), (5440747219/10000000000 : ℝ), (-362422233/2500000000 : ℝ)] ![(44720777432829/100000000000000 : ℝ), (46482162207249/100000000000000 : ℝ), (8797060344937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055259363/2000000000 : ℝ)|^4983 ≤ (44720777432829/100000000000000 : ℝ)^3959
        have hw : |(1055259363/2000000000 : ℝ)|=(1055259363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440747219/10000000000 : ℝ)|^4983 ≤ (46482162207249/100000000000000 : ℝ)^3959
        have hw : |(5440747219/10000000000 : ℝ)|=(5440747219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-362422233/2500000000 : ℝ)|^4983 ≤ (8797060344937/100000000000000 : ℝ)^3959
        have hw : |(-362422233/2500000000 : ℝ)|=(362422233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s4_7 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (833762383/2000000000 : ℝ)*x 0 + (4513502571/10000000000 : ℝ)*x 1 + (3843522461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (833762383/2000000000 : ℝ)^4983 ≤ (8311282525863/25000000000000 : ℝ)^3959 := by
    have hnat : (833762383 : ℕ)^4983*25000000000000^3959 ≤ 8311282525863^3959*2000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833762383 2000000000 8311282525863 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4513502571/10000000000 : ℝ)^4983 ≤ (36741193126339/100000000000000 : ℝ)^3959 := by
    have hnat : (4513502571 : ℕ)^4983*100000000000000^3959 ≤ 36741193126339^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513502571 10000000000 36741193126339 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3843522461/10000000000 : ℝ)^4983 ≤ (30013676759221/100000000000000 : ℝ)^3959 := by
    have hnat : (3843522461 : ℕ)^4983*100000000000000^3959 ≤ 30013676759221^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3843522461 10000000000 30013676759221 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(833762383/2000000000 : ℝ), (4513502571/10000000000 : ℝ), (3843522461/10000000000 : ℝ)] ![(8311282525863/25000000000000 : ℝ), (36741193126339/100000000000000 : ℝ), (30013676759221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(833762383/2000000000 : ℝ)|^4983 ≤ (8311282525863/25000000000000 : ℝ)^3959
        have hw : |(833762383/2000000000 : ℝ)|=(833762383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4513502571/10000000000 : ℝ)|^4983 ≤ (36741193126339/100000000000000 : ℝ)^3959
        have hw : |(4513502571/10000000000 : ℝ)|=(4513502571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3843522461/10000000000 : ℝ)|^4983 ≤ (30013676759221/100000000000000 : ℝ)^3959
        have hw : |(3843522461/10000000000 : ℝ)|=(3843522461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s4_8 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1345633993/2000000000 : ℝ)*x 0 + (2744957191/10000000000 : ℝ)*x 1 + (2742458931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345633993/2000000000 : ℝ)^4983 ≤ (759088325083/1250000000000 : ℝ)^3959 := by
    have hnat : (1345633993 : ℕ)^4983*1250000000000^3959 ≤ 759088325083^3959*2000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345633993 2000000000 759088325083 1250000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2744957191/10000000000 : ℝ)^4983 ≤ (19647719214941/100000000000000 : ℝ)^3959 := by
    have hnat : (2744957191 : ℕ)^4983*100000000000000^3959 ≤ 19647719214941^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744957191 10000000000 19647719214941 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2742458931/10000000000 : ℝ)^4983 ≤ (1962521476227/10000000000000 : ℝ)^3959 := by
    have hnat : (2742458931 : ℕ)^4983*10000000000000^3959 ≤ 1962521476227^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742458931 10000000000 1962521476227 10000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1345633993/2000000000 : ℝ), (2744957191/10000000000 : ℝ), (2742458931/10000000000 : ℝ)] ![(759088325083/1250000000000 : ℝ), (19647719214941/100000000000000 : ℝ), (1962521476227/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1345633993/2000000000 : ℝ)|^4983 ≤ (759088325083/1250000000000 : ℝ)^3959
        have hw : |(-1345633993/2000000000 : ℝ)|=(1345633993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2744957191/10000000000 : ℝ)|^4983 ≤ (19647719214941/100000000000000 : ℝ)^3959
        have hw : |(2744957191/10000000000 : ℝ)|=(2744957191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2742458931/10000000000 : ℝ)|^4983 ≤ (1962521476227/10000000000000 : ℝ)^3959
        have hw : |(2742458931/10000000000 : ℝ)|=(2742458931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s4_9 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4159757059/5000000000 : ℝ)*x 0 + (-458808463/10000000000 : ℝ)*x 1 + (1314205479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4159757059/5000000000 : ℝ)^4983 ≤ (3966442946001/5000000000000 : ℝ)^3959 := by
    have hnat : (4159757059 : ℕ)^4983*5000000000000^3959 ≤ 3966442946001^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159757059 5000000000 3966442946001 5000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458808463/10000000000 : ℝ)^4983 ≤ (82702912917/4000000000000 : ℝ)^3959 := by
    have hnat : (458808463 : ℕ)^4983*4000000000000^3959 ≤ 82702912917^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458808463 10000000000 82702912917 4000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314205479/5000000000 : ℝ)^4983 ≤ (9301784118557/50000000000000 : ℝ)^3959 := by
    have hnat : (1314205479 : ℕ)^4983*50000000000000^3959 ≤ 9301784118557^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314205479 5000000000 9301784118557 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4159757059/5000000000 : ℝ), (-458808463/10000000000 : ℝ), (1314205479/5000000000 : ℝ)] ![(3966442946001/5000000000000 : ℝ), (82702912917/4000000000000 : ℝ), (9301784118557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4159757059/5000000000 : ℝ)|^4983 ≤ (3966442946001/5000000000000 : ℝ)^3959
        have hw : |(4159757059/5000000000 : ℝ)|=(4159757059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-458808463/10000000000 : ℝ)|^4983 ≤ (82702912917/4000000000000 : ℝ)^3959
        have hw : |(-458808463/10000000000 : ℝ)|=(458808463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1314205479/5000000000 : ℝ)|^4983 ≤ (9301784118557/50000000000000 : ℝ)^3959
        have hw : |(1314205479/5000000000 : ℝ)|=(1314205479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s4_10 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (261254687/312500000 : ℝ)*x 0 + (2420493693/10000000000 : ℝ)*x 1 + (-170790141/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261254687/312500000 : ℝ)^4983 ≤ (79816861442491/100000000000000 : ℝ)^3959 := by
    have hnat : (261254687 : ℕ)^4983*100000000000000^3959 ≤ 79816861442491^3959*312500000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261254687 312500000 79816861442491 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2420493693/10000000000 : ℝ)^4983 ≤ (838532682219/5000000000000 : ℝ)^3959 := by
    have hnat : (2420493693 : ℕ)^4983*5000000000000^3959 ≤ 838532682219^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2420493693 10000000000 838532682219 5000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170790141/2500000000 : ℝ)^4983 ≤ (1706242451541/50000000000000 : ℝ)^3959 := by
    have hnat : (170790141 : ℕ)^4983*50000000000000^3959 ≤ 1706242451541^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170790141 2500000000 1706242451541 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261254687/312500000 : ℝ), (2420493693/10000000000 : ℝ), (-170790141/2500000000 : ℝ)] ![(79816861442491/100000000000000 : ℝ), (838532682219/5000000000000 : ℝ), (1706242451541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261254687/312500000 : ℝ)|^4983 ≤ (79816861442491/100000000000000 : ℝ)^3959
        have hw : |(261254687/312500000 : ℝ)|=(261254687/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2420493693/10000000000 : ℝ)|^4983 ≤ (838532682219/5000000000000 : ℝ)^3959
        have hw : |(2420493693/10000000000 : ℝ)|=(2420493693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-170790141/2500000000 : ℝ)|^4983 ≤ (1706242451541/50000000000000 : ℝ)^3959
        have hw : |(-170790141/2500000000 : ℝ)|=(170790141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_s4_11 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (899223401/1250000000 : ℝ)*x 0 + (441317629/2000000000 : ℝ)*x 1 + (2673905717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (899223401/1250000000 : ℝ)^4983 ≤ (4128948980509/6250000000000 : ℝ)^3959 := by
    have hnat : (899223401 : ℕ)^4983*6250000000000^3959 ≤ 4128948980509^3959*1250000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899223401 1250000000 4128948980509 6250000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441317629/2000000000 : ℝ)^4983 ≤ (2985410216089/20000000000000 : ℝ)^3959 := by
    have hnat : (441317629 : ℕ)^4983*20000000000000^3959 ≤ 2985410216089^3959*2000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441317629 2000000000 2985410216089 20000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2673905717/10000000000 : ℝ)^4983 ≤ (19009765217197/100000000000000 : ℝ)^3959 := by
    have hnat : (2673905717 : ℕ)^4983*100000000000000^3959 ≤ 19009765217197^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673905717 10000000000 19009765217197 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(899223401/1250000000 : ℝ), (441317629/2000000000 : ℝ), (2673905717/10000000000 : ℝ)] ![(4128948980509/6250000000000 : ℝ), (2985410216089/20000000000000 : ℝ), (19009765217197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(899223401/1250000000 : ℝ)|^4983 ≤ (4128948980509/6250000000000 : ℝ)^3959
        have hw : |(899223401/1250000000 : ℝ)|=(899223401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(441317629/2000000000 : ℝ)|^4983 ≤ (2985410216089/20000000000000 : ℝ)^3959
        have hw : |(441317629/2000000000 : ℝ)|=(441317629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2673905717/10000000000 : ℝ)|^4983 ≤ (19009765217197/100000000000000 : ℝ)^3959
        have hw : |(2673905717/10000000000 : ℝ)|=(2673905717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1666_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181973587/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10747/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (43/400 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4059/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10747/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10747/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10747/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10747/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10747/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10747/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10747/100000 : ℝ) ^ (4979/1024 : ℝ) ≤ (243631513060933/12500000000000000000 : ℝ) := by
    have hpowers : (10747/100000 : ℝ)^4979 ≤ (243631513060933/12500000000000000000 : ℝ)^1024 := by
      have hnat : (10747 : ℕ)^4979*12500000000000000000^1024 ≤ 243631513060933^1024*100000^4979 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10747 100000 243631513060933 12500000000000000000 4979 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10747/100000 : ℝ)) (X := (243631513060933/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16239/100000 : ℝ) ^ (4979/1024 : ℝ) ≤ (14504364174063391/100000000000000000000 : ℝ) := by
    have hpowers : (16239/100000 : ℝ)^4979 ≤ (14504364174063391/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16239 : ℕ)^4979*100000000000000000000^1024 ≤ 14504364174063391^1024*100000^4979 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16239 100000 14504364174063391 100000000000000000000 4979 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16239/100000 : ℝ)) (X := (14504364174063391/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250243631513060933/6250000000000000000 : ℝ) ≤ (2000016033729313/2000000000000000 : ℝ) ^ (4979/1024 : ℝ) := by
    have hpowers : (6250243631513060933/6250000000000000000 : ℝ)^1024 ≤ (2000016033729313/2000000000000000 : ℝ)^4979 := by
      have hnat : (6250243631513060933 : ℕ)^1024*2000000000000000^4979 ≤ 2000016033729313^4979*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250243631513060933 6250000000000000000 2000016033729313 2000000000000000 1024 4979 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000016033729313/2000000000000000 : ℝ)) (X := (6250243631513060933/6250000000000000000 : ℝ)) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20003290683255710171/20000000000000000000 : ℝ) ≤ (5000169182540467/5000000000000000 : ℝ) ^ (4979/1024 : ℝ) := by
    have hpowers : (20003290683255710171/20000000000000000000 : ℝ)^1024 ≤ (5000169182540467/5000000000000000 : ℝ)^4979 := by
      have hnat : (20003290683255710171 : ℕ)^1024*5000000000000000^4979 ≤ 5000169182540467^4979*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20003290683255710171 20000000000000000000 5000169182540467 5000000000000000 1024 4979 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000169182540467/5000000000000000 : ℝ)) (X := (20003290683255710171/20000000000000000000 : ℝ)) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50014504364174063391/50000000000000000000 : ℝ) ≤ (10000596561515303/10000000000000000 : ℝ) ^ (4979/1024 : ℝ) := by
    have hpowers : (50014504364174063391/50000000000000000000 : ℝ)^1024 ≤ (10000596561515303/10000000000000000 : ℝ)^4979 := by
      have hnat : (50014504364174063391 : ℕ)^1024*10000000000000000^4979 ≤ 10000596561515303^4979*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014504364174063391 50000000000000000000 10000596561515303 10000000000000000 1024 4979 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000596561515303/10000000000000000 : ℝ)) (X := (50014504364174063391/50000000000000000000 : ℝ)) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(243631513060933/12500000000000000000 : ℝ) ≤ ((27457445306023303847/27460000000000000000 : ℝ)+2*(258196434369/549200000000000 : ℝ)*(10747/100000 : ℝ))^(4979/1024 : ℝ) := by
    rw [show (27457445306023303847/27460000000000000000 : ℝ)+2*(258196434369/549200000000000 : ℝ)*(10747/100000 : ℝ)=(2000016033729313/2000000000000000 : ℝ) by norm_num, show 1+2*(243631513060933/12500000000000000000 : ℝ)=(6250243631513060933/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14504364174063391/100000000000000000000 : ℝ)+(243631513060933/12500000000000000000 : ℝ) ≤ ((27457445306023303847/27460000000000000000 : ℝ)+(258196434369/549200000000000 : ℝ)*((16239/100000 : ℝ)+(10747/100000 : ℝ)))^(4979/1024 : ℝ) := by
    rw [show (27457445306023303847/27460000000000000000 : ℝ)+(258196434369/549200000000000 : ℝ)*((16239/100000 : ℝ)+(10747/100000 : ℝ))=(5000169182540467/5000000000000000 : ℝ) by norm_num, show 1+(14504364174063391/100000000000000000000 : ℝ)+(243631513060933/12500000000000000000 : ℝ)=(20003290683255710171/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14504364174063391/100000000000000000000 : ℝ) ≤ ((27457445306023303847/27460000000000000000 : ℝ)+2*(258196434369/549200000000000 : ℝ)*(16239/100000 : ℝ))^(4979/1024 : ℝ) := by
    rw [show (27457445306023303847/27460000000000000000 : ℝ)+2*(258196434369/549200000000000 : ℝ)*(16239/100000 : ℝ)=(10000596561515303/10000000000000000 : ℝ) by norm_num, show 1+2*(14504364174063391/100000000000000000000 : ℝ)=(50014504364174063391/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27457445306023303847/27460000000000000000 : ℝ)*(X 1 0+X 2 0)+(258196434369/549200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4979/1024 : ℝ)) (lo := (10747/100000 : ℝ)) (hi := (16239/100000 : ℝ)) (c := (27457445306023303847/27460000000000000000 : ℝ)) (alpha := (258196434369/549200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27457445306023303847/27460000000000000000 : ℝ)*(X 0 1+X 2 1)+(258196434369/549200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4979/1024 : ℝ)) (lo := (10747/100000 : ℝ)) (hi := (16239/100000 : ℝ)) (c := (27457445306023303847/27460000000000000000 : ℝ)) (alpha := (258196434369/549200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27457445306023303847/27460000000000000000 : ℝ)*(X 0 2+X 1 2)+(258196434369/549200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4979/1024 : ℝ)) (lo := (10747/100000 : ℝ)) (hi := (16239/100000 : ℝ)) (c := (27457445306023303847/27460000000000000000 : ℝ)) (alpha := (258196434369/549200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-393215521/2500000000 : ℝ)*X 0 0+(5442735127/10000000000 : ℝ)*X 0 1+(1296238099/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345274271/10000000000 : ℝ)*X 1 0+(-1705485537/10000000000 : ℝ)*X 1 1+(1296239697/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672639027/5000000000 : ℝ)*X 2 0+(5184957723/10000000000 : ℝ)*X 2 1+(-1705481873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1042162561/2500000000 : ℝ)*X 0 0+(959571987/2500000000 : ℝ)*X 0 1+(56483509/125000000 : ℝ)*X 0 2+(1042162561/2500000000 : ℝ)*X 1 0+(959571987/2500000000 : ℝ)*X 1 1+(56483509/125000000 : ℝ)*X 1 2+(1042162561/2500000000 : ℝ)*X 2 0+(959571987/2500000000 : ℝ)*X 2 1+(56483509/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-78646459/500000000 : ℝ)*X 0 0+(324182241/625000000 : ℝ)*X 0 1+(170023353/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638148581/5000000000 : ℝ)*X 1 0+(-1449688649/10000000000 : ℝ)*X 1 1+(1360186769/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055259363/2000000000 : ℝ)*X 2 0+(5440747219/10000000000 : ℝ)*X 2 1+(-362422233/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((833762383/2000000000 : ℝ)*X 0 0+(4513502571/10000000000 : ℝ)*X 0 1+(3843522461/10000000000 : ℝ)*X 0 2+(833762383/2000000000 : ℝ)*X 1 0+(4513502571/10000000000 : ℝ)*X 1 1+(3843522461/10000000000 : ℝ)*X 1 2+(833762383/2000000000 : ℝ)*X 2 0+(4513502571/10000000000 : ℝ)*X 2 1+(3843522461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1345633993/2000000000 : ℝ)*X 0 0+(2744957191/10000000000 : ℝ)*X 0 1+(2742458931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s4_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((4159757059/5000000000 : ℝ)*X 1 0+(-458808463/10000000000 : ℝ)*X 1 1+(1314205479/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s4_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((261254687/312500000 : ℝ)*X 2 0+(2420493693/10000000000 : ℝ)*X 2 1+(-170790141/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s4_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((899223401/1250000000 : ℝ)*X 0 0+(441317629/2000000000 : ℝ)*X 0 1+(2673905717/10000000000 : ℝ)*X 0 2+(899223401/1250000000 : ℝ)*X 1 0+(441317629/2000000000 : ℝ)*X 1 1+(2673905717/10000000000 : ℝ)*X 1 2+(899223401/1250000000 : ℝ)*X 2 0+(441317629/2000000000 : ℝ)*X 2 1+(2673905717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_s4_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4204322184384413357103256827/686500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (616345809/25000000000000 : ℝ)*(lower2) + (531637001/100000000000000 : ℝ)*(lower3) + (1337254392573851/50000000000000 : ℝ)*(major0) + (1337254392573851/50000000000000 : ℝ)*(major1) + (1337254392573851/50000000000000 : ℝ)*(major2) + (3879226194465649/100000000000000 : ℝ)*(sp0) + (969822079124983/25000000000000 : ℝ)*(sp1) + (48491063499593/1250000000000 : ℝ)*(sp2) + (183715268356227/12500000000000 : ℝ)*(sp3) + (67163273669/100000000000000 : ℝ)*(sp4) + (391244699/100000000000000 : ℝ)*(sp8) + (2716242043/50000000000000 : ℝ)*(sp9) + (8669016577/100000000000000 : ℝ)*(sp10) + (735159351/50000000000000 : ℝ)*(sp11) + (1469723617168519/100000000000000 : ℝ)*(f.failure) + (3879293748984017/100000000000000 : ℝ)*(f.sum) + (158380885704249/13730000000000000000000000000 : ℝ)*base65 + (822957060368854797/1373000000000000000000000000000000 : ℝ)*base67 + (11797917644387854797/1373000000000000000000000000000000 : ℝ)*base69 + (9319409363890854797/1373000000000000000000000000000000 : ℝ)*base71 + (55930887856139/13730000000000000000000000000 : ℝ)*base73 + (3825090616776854797/1373000000000000000000000000000000 : ℝ)*base75 + (24437964344506854797/1373000000000000000000000000000000 : ℝ)*base77 + (8530622924763854797/1373000000000000000000000000000000 : ℝ)*base79 + (40841889023639/13730000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (14092347/10000000000000000000000 : ℝ)*base90 + (14092347/10000000000000000000000 : ℝ)*base92 + (14092347/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3643960889652834178898687433/343250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (844042537/50000000000000 : ℝ)*(base19) + (277831877/20000000000000 : ℝ)*(base23) + (326115713/100000000000000 : ℝ)*(lower1) + (11120779/50000000000000 : ℝ)*(upper2) + (98217559/50000000000000 : ℝ)*(upper3) + (294873793/100000000000000 : ℝ)*(upper5) + (1358046469543587/50000000000000 : ℝ)*(major0) + (1358046469543587/50000000000000 : ℝ)*(major1) + (1358046469543587/50000000000000 : ℝ)*(major2) + (6271531427/100000000000000 : ℝ)*(sp1) + (3939610154514851/100000000000000 : ℝ)*(sp4) + (78792043897967/2000000000000 : ℝ)*(sp5) + (1969804382677733/50000000000000 : ℝ)*(sp6) + (1492575369790987/100000000000000 : ℝ)*(sp7) + (1492575369790987/100000000000000 : ℝ)*(f.failure) + (3939610154514851/100000000000000 : ℝ)*(f.sum) + (7915511968647/13730000000000000000000000000 : ℝ)*base66 + (7307545062682429189/1373000000000000000000000000000000 : ℝ)*base67 + (23841907589827570811/1373000000000000000000000000000000 : ℝ)*base70 + (1979340545285429189/1373000000000000000000000000000000 : ℝ)*base71 + (12955883874163/13730000000000000000000000000 : ℝ)*base73 + (5332334837032429189/1373000000000000000000000000000000 : ℝ)*base75 + (7328351694156429189/1373000000000000000000000000000000 : ℝ)*base77 + (1065102258628429189/1373000000000000000000000000000000 : ℝ)*base79 + (358305095080747/13730000000000000000000000000 : ℝ)*base82 + (55339631/10000000000000000000000 : ℝ)*base90 + (55339631/10000000000000000000000 : ℝ)*base92 + (55339631/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1666_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181973587/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10747/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (43/400 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4059/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1666_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1666_box_0 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-132048609/1000000000 : ℝ)*x 0 + (1080831509/2000000000 : ℝ)*x 1 + (2702079879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132048609/1000000000 : ℝ)^4983 ≤ (3910935086601/50000000000000 : ℝ)^3959 := by
    have hnat : (132048609 : ℕ)^4983*50000000000000^3959 ≤ 3910935086601^3959*1000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132048609 1000000000 3910935086601 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080831509/2000000000 : ℝ)^4983 ≤ (921781060553/2000000000000 : ℝ)^3959 := by
    have hnat : (1080831509 : ℕ)^4983*2000000000000^3959 ≤ 921781060553^3959*2000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080831509 2000000000 921781060553 2000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702079879/5000000000 : ℝ)^4983 ≤ (2880567298921/6250000000000 : ℝ)^3959 := by
    have hnat : (2702079879 : ℕ)^4983*6250000000000^3959 ≤ 2880567298921^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702079879 5000000000 2880567298921 6250000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132048609/1000000000 : ℝ), (1080831509/2000000000 : ℝ), (2702079879/5000000000 : ℝ)] ![(3910935086601/50000000000000 : ℝ), (921781060553/2000000000000 : ℝ), (2880567298921/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132048609/1000000000 : ℝ)|^4983 ≤ (3910935086601/50000000000000 : ℝ)^3959
        have hw : |(-132048609/1000000000 : ℝ)|=(132048609/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080831509/2000000000 : ℝ)|^4983 ≤ (921781060553/2000000000000 : ℝ)^3959
        have hw : |(1080831509/2000000000 : ℝ)|=(1080831509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702079879/5000000000 : ℝ)|^4983 ≤ (2880567298921/6250000000000 : ℝ)^3959
        have hw : |(2702079879/5000000000 : ℝ)|=(2702079879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_box_1 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250783391/10000000000 : ℝ)*x 0 + (-1536113229/10000000000 : ℝ)*x 1 + (1351039623/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250783391/10000000000 : ℝ)^4983 ≤ (11112192266761/25000000000000 : ℝ)^3959 := by
    have hnat : (5250783391 : ℕ)^4983*25000000000000^3959 ≤ 11112192266761^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250783391 10000000000 11112192266761 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1536113229/10000000000 : ℝ)^4983 ≤ (4731083862247/50000000000000 : ℝ)^3959 := by
    have hnat : (1536113229 : ℕ)^4983*50000000000000^3959 ≤ 4731083862247^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1536113229 10000000000 4731083862247 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351039623/2500000000 : ℝ)^4983 ≤ (23044531596533/50000000000000 : ℝ)^3959 := by
    have hnat : (1351039623 : ℕ)^4983*50000000000000^3959 ≤ 23044531596533^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351039623 2500000000 23044531596533 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250783391/10000000000 : ℝ), (-1536113229/10000000000 : ℝ), (1351039623/2500000000 : ℝ)] ![(11112192266761/25000000000000 : ℝ), (4731083862247/50000000000000 : ℝ), (23044531596533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250783391/10000000000 : ℝ)|^4983 ≤ (11112192266761/25000000000000 : ℝ)^3959
        have hw : |(5250783391/10000000000 : ℝ)|=(5250783391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1536113229/10000000000 : ℝ)|^4983 ≤ (4731083862247/50000000000000 : ℝ)^3959
        have hw : |(-1536113229/10000000000 : ℝ)|=(1536113229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351039623/2500000000 : ℝ)|^4983 ≤ (23044531596533/50000000000000 : ℝ)^3959
        have hw : |(1351039623/2500000000 : ℝ)|=(1351039623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_box_2 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250783421/10000000000 : ℝ)*x 0 + (5404159201/10000000000 : ℝ)*x 1 + (-768056103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250783421/10000000000 : ℝ)^4983 ≤ (8889753877337/20000000000000 : ℝ)^3959 := by
    have hnat : (5250783421 : ℕ)^4983*20000000000000^3959 ≤ 8889753877337^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250783421 10000000000 8889753877337 20000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404159201/10000000000 : ℝ)^4983 ≤ (4608907080371/10000000000000 : ℝ)^3959 := by
    have hnat : (5404159201 : ℕ)^4983*10000000000000^3959 ≤ 4608907080371^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404159201 10000000000 4608907080371 10000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (768056103/5000000000 : ℝ)^4983 ≤ (9462159793121/100000000000000 : ℝ)^3959 := by
    have hnat : (768056103 : ℕ)^4983*100000000000000^3959 ≤ 9462159793121^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768056103 5000000000 9462159793121 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250783421/10000000000 : ℝ), (5404159201/10000000000 : ℝ), (-768056103/5000000000 : ℝ)] ![(8889753877337/20000000000000 : ℝ), (4608907080371/10000000000000 : ℝ), (9462159793121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250783421/10000000000 : ℝ)|^4983 ≤ (8889753877337/20000000000000 : ℝ)^3959
        have hw : |(5250783421/10000000000 : ℝ)|=(5250783421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404159201/10000000000 : ℝ)|^4983 ≤ (4608907080371/10000000000000 : ℝ)^3959
        have hw : |(5404159201/10000000000 : ℝ)|=(5404159201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-768056103/5000000000 : ℝ)|^4983 ≤ (9462159793121/100000000000000 : ℝ)^3959
        have hw : |(-768056103/5000000000 : ℝ)|=(768056103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_box_3 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4444440649/10000000000 : ℝ)*x 0 + (4042519327/10000000000 : ℝ)*x 1 + (4042521709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4444440649/10000000000 : ℝ)^4983 ≤ (36035005536589/100000000000000 : ℝ)^3959 := by
    have hnat : (4444440649 : ℕ)^4983*100000000000000^3959 ≤ 36035005536589^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4444440649 10000000000 36035005536589 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4042519327/10000000000 : ℝ)^4983 ≤ (15991242683249/50000000000000 : ℝ)^3959 := by
    have hnat : (4042519327 : ℕ)^4983*50000000000000^3959 ≤ 15991242683249^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4042519327 10000000000 15991242683249 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4042521709/10000000000 : ℝ)^4983 ≤ (31982509086093/100000000000000 : ℝ)^3959 := by
    have hnat : (4042521709 : ℕ)^4983*100000000000000^3959 ≤ 31982509086093^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4042521709 10000000000 31982509086093 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4444440649/10000000000 : ℝ), (4042519327/10000000000 : ℝ), (4042521709/10000000000 : ℝ)] ![(36035005536589/100000000000000 : ℝ), (15991242683249/50000000000000 : ℝ), (31982509086093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4444440649/10000000000 : ℝ)|^4983 ≤ (36035005536589/100000000000000 : ℝ)^3959
        have hw : |(4444440649/10000000000 : ℝ)|=(4444440649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4042519327/10000000000 : ℝ)|^4983 ≤ (15991242683249/50000000000000 : ℝ)^3959
        have hw : |(4042519327/10000000000 : ℝ)|=(4042519327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4042521709/10000000000 : ℝ)|^4983 ≤ (31982509086093/100000000000000 : ℝ)^3959
        have hw : |(4042521709/10000000000 : ℝ)|=(4042521709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_box_4 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-367157669/2000000000 : ℝ)*x 0 + (1304017233/2500000000 : ℝ)*x 1 + (5216068697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (367157669/2000000000 : ℝ)^4983 ≤ (11841574762197/100000000000000 : ℝ)^3959 := by
    have hnat : (367157669 : ℕ)^4983*100000000000000^3959 ≤ 11841574762197^3959*2000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367157669 2000000000 11841574762197 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304017233/2500000000 : ℝ)^4983 ≤ (4407921385737/10000000000000 : ℝ)^3959 := by
    have hnat : (1304017233 : ℕ)^4983*10000000000000^3959 ≤ 4407921385737^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304017233 2500000000 4407921385737 10000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216068697/10000000000 : ℝ)^4983 ≤ (44079211357809/100000000000000 : ℝ)^3959 := by
    have hnat : (5216068697 : ℕ)^4983*100000000000000^3959 ≤ 44079211357809^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216068697 10000000000 44079211357809 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-367157669/2000000000 : ℝ), (1304017233/2500000000 : ℝ), (5216068697/10000000000 : ℝ)] ![(11841574762197/100000000000000 : ℝ), (4407921385737/10000000000000 : ℝ), (44079211357809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-367157669/2000000000 : ℝ)|^4983 ≤ (11841574762197/100000000000000 : ℝ)^3959
        have hw : |(-367157669/2000000000 : ℝ)|=(367157669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304017233/2500000000 : ℝ)|^4983 ≤ (4407921385737/10000000000000 : ℝ)^3959
        have hw : |(1304017233/2500000000 : ℝ)|=(1304017233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216068697/10000000000 : ℝ)|^4983 ≤ (44079211357809/100000000000000 : ℝ)^3959
        have hw : |(5216068697/10000000000 : ℝ)|=(5216068697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_box_5 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379610103/10000000000 : ℝ)*x 0 + (-161720039/1000000000 : ℝ)*x 1 + (5216068999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379610103/10000000000 : ℝ)^4983 ≤ (45825707511611/100000000000000 : ℝ)^3959 := by
    have hnat : (5379610103 : ℕ)^4983*100000000000000^3959 ≤ 45825707511611^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379610103 10000000000 45825707511611 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161720039/1000000000 : ℝ)^4983 ≤ (5047538950189/50000000000000 : ℝ)^3959 := by
    have hnat : (161720039 : ℕ)^4983*50000000000000^3959 ≤ 5047538950189^3959*1000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161720039 1000000000 5047538950189 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216068999/10000000000 : ℝ)^4983 ≤ (44079214570011/100000000000000 : ℝ)^3959 := by
    have hnat : (5216068999 : ℕ)^4983*100000000000000^3959 ≤ 44079214570011^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216068999 10000000000 44079214570011 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379610103/10000000000 : ℝ), (-161720039/1000000000 : ℝ), (5216068999/10000000000 : ℝ)] ![(45825707511611/100000000000000 : ℝ), (5047538950189/50000000000000 : ℝ), (44079214570011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379610103/10000000000 : ℝ)|^4983 ≤ (45825707511611/100000000000000 : ℝ)^3959
        have hw : |(5379610103/10000000000 : ℝ)|=(5379610103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-161720039/1000000000 : ℝ)|^4983 ≤ (5047538950189/50000000000000 : ℝ)^3959
        have hw : |(-161720039/1000000000 : ℝ)|=(161720039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216068999/10000000000 : ℝ)|^4983 ≤ (44079214570011/100000000000000 : ℝ)^3959
        have hw : |(5216068999/10000000000 : ℝ)|=(5216068999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_box_6 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379610517/10000000000 : ℝ)*x 0 + (2608034257/5000000000 : ℝ)*x 1 + (-808600241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379610517/10000000000 : ℝ)^4983 ≤ (11456427987599/25000000000000 : ℝ)^3959 := by
    have hnat : (5379610517 : ℕ)^4983*25000000000000^3959 ≤ 11456427987599^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379610517 10000000000 11456427987599 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608034257/5000000000 : ℝ)^4983 ≤ (44079209411343/100000000000000 : ℝ)^3959 := by
    have hnat : (2608034257 : ℕ)^4983*100000000000000^3959 ≤ 44079209411343^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608034257 5000000000 44079209411343 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (808600241/5000000000 : ℝ)^4983 ≤ (10095078623213/100000000000000 : ℝ)^3959 := by
    have hnat : (808600241 : ℕ)^4983*100000000000000^3959 ≤ 10095078623213^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808600241 5000000000 10095078623213 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379610517/10000000000 : ℝ), (2608034257/5000000000 : ℝ), (-808600241/5000000000 : ℝ)] ![(11456427987599/25000000000000 : ℝ), (44079209411343/100000000000000 : ℝ), (10095078623213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379610517/10000000000 : ℝ)|^4983 ≤ (11456427987599/25000000000000 : ℝ)^3959
        have hw : |(5379610517/10000000000 : ℝ)|=(5379610517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608034257/5000000000 : ℝ)|^4983 ≤ (44079209411343/100000000000000 : ℝ)^3959
        have hw : |(2608034257/5000000000 : ℝ)|=(2608034257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-808600241/5000000000 : ℝ)|^4983 ≤ (10095078623213/100000000000000 : ℝ)^3959
        have hw : |(-808600241/5000000000 : ℝ)|=(808600241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_box_7 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (777219681/2000000000 : ℝ)*x 0 + (1080343269/2500000000 : ℝ)*x 1 + (135042909/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (777219681/2000000000 : ℝ)^4983 ≤ (15216369954767/50000000000000 : ℝ)^3959 := by
    have hnat : (777219681 : ℕ)^4983*50000000000000^3959 ≤ 15216369954767^3959*2000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777219681 2000000000 15216369954767 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080343269/2500000000 : ℝ)^4983 ≤ (17391814988373/50000000000000 : ℝ)^3959 := by
    have hnat : (1080343269 : ℕ)^4983*50000000000000^3959 ≤ 17391814988373^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080343269 2500000000 17391814988373 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135042909/312500000 : ℝ)^4983 ≤ (434795376229/1250000000000 : ℝ)^3959 := by
    have hnat : (135042909 : ℕ)^4983*1250000000000^3959 ≤ 434795376229^3959*312500000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135042909 312500000 434795376229 1250000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(777219681/2000000000 : ℝ), (1080343269/2500000000 : ℝ), (135042909/312500000 : ℝ)] ![(15216369954767/50000000000000 : ℝ), (17391814988373/50000000000000 : ℝ), (434795376229/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(777219681/2000000000 : ℝ)|^4983 ≤ (15216369954767/50000000000000 : ℝ)^3959
        have hw : |(777219681/2000000000 : ℝ)|=(777219681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080343269/2500000000 : ℝ)|^4983 ≤ (17391814988373/50000000000000 : ℝ)^3959
        have hw : |(1080343269/2500000000 : ℝ)|=(1080343269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135042909/312500000 : ℝ)|^4983 ≤ (434795376229/1250000000000 : ℝ)^3959
        have hw : |(135042909/312500000 : ℝ)|=(135042909/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_box_8 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1725751501/10000000000 : ℝ)*x 0 + (1270108379/2500000000 : ℝ)*x 1 + (2716707983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1725751501/10000000000 : ℝ)^4983 ≤ (5477618666349/50000000000000 : ℝ)^3959 := by
    have hnat : (1725751501 : ℕ)^4983*50000000000000^3959 ≤ 5477618666349^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1725751501 10000000000 5477618666349 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270108379/2500000000 : ℝ)^4983 ≤ (8528284061181/20000000000000 : ℝ)^3959 := by
    have hnat : (1270108379 : ℕ)^4983*20000000000000^3959 ≤ 8528284061181^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270108379 2500000000 8528284061181 20000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716707983/5000000000 : ℝ)^4983 ≤ (1856133693937/4000000000000 : ℝ)^3959 := by
    have hnat : (2716707983 : ℕ)^4983*4000000000000^3959 ≤ 1856133693937^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716707983 5000000000 1856133693937 4000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1725751501/10000000000 : ℝ), (1270108379/2500000000 : ℝ), (2716707983/5000000000 : ℝ)] ![(5477618666349/50000000000000 : ℝ), (8528284061181/20000000000000 : ℝ), (1856133693937/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1725751501/10000000000 : ℝ)|^4983 ≤ (5477618666349/50000000000000 : ℝ)^3959
        have hw : |(-1725751501/10000000000 : ℝ)|=(1725751501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1270108379/2500000000 : ℝ)|^4983 ≤ (8528284061181/20000000000000 : ℝ)^3959
        have hw : |(1270108379/2500000000 : ℝ)|=(1270108379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716707983/5000000000 : ℝ)|^4983 ≤ (1856133693937/4000000000000 : ℝ)^3959
        have hw : |(2716707983/5000000000 : ℝ)|=(2716707983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_box_9 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (523074789/1000000000 : ℝ)*x 0 + (-761541559/5000000000 : ℝ)*x 1 + (5433415933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523074789/1000000000 : ℝ)^4983 ≤ (44235402356837/100000000000000 : ℝ)^3959 := by
    have hnat : (523074789 : ℕ)^4983*100000000000000^3959 ≤ 44235402356837^3959*1000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523074789 1000000000 44235402356837 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (761541559/5000000000 : ℝ)^4983 ≤ (9361255629039/100000000000000 : ℝ)^3959 := by
    have hnat : (761541559 : ℕ)^4983*100000000000000^3959 ≤ 9361255629039^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      761541559 5000000000 9361255629039 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433415933/10000000000 : ℝ)^4983 ≤ (46403341993697/100000000000000 : ℝ)^3959 := by
    have hnat : (5433415933 : ℕ)^4983*100000000000000^3959 ≤ 46403341993697^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433415933 10000000000 46403341993697 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523074789/1000000000 : ℝ), (-761541559/5000000000 : ℝ), (5433415933/10000000000 : ℝ)] ![(44235402356837/100000000000000 : ℝ), (9361255629039/100000000000000 : ℝ), (46403341993697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523074789/1000000000 : ℝ)|^4983 ≤ (44235402356837/100000000000000 : ℝ)^3959
        have hw : |(523074789/1000000000 : ℝ)|=(523074789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-761541559/5000000000 : ℝ)|^4983 ≤ (9361255629039/100000000000000 : ℝ)^3959
        have hw : |(-761541559/5000000000 : ℝ)|=(761541559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433415933/10000000000 : ℝ)|^4983 ≤ (46403341993697/100000000000000 : ℝ)^3959
        have hw : |(5433415933/10000000000 : ℝ)|=(5433415933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_box_10 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615373841/5000000000 : ℝ)*x 0 + (1086683251/2000000000 : ℝ)*x 1 + (-1523082957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615373841/5000000000 : ℝ)^4983 ≤ (44235400142851/100000000000000 : ℝ)^3959 := by
    have hnat : (2615373841 : ℕ)^4983*100000000000000^3959 ≤ 44235400142851^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615373841 5000000000 44235400142851 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086683251/2000000000 : ℝ)^4983 ≤ (46403345454983/100000000000000 : ℝ)^3959 := by
    have hnat : (1086683251 : ℕ)^4983*100000000000000^3959 ≤ 46403345454983^3959*2000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086683251 2000000000 46403345454983 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1523082957/10000000000 : ℝ)^4983 ≤ (1872250876709/20000000000000 : ℝ)^3959 := by
    have hnat : (1523082957 : ℕ)^4983*20000000000000^3959 ≤ 1872250876709^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1523082957 10000000000 1872250876709 20000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615373841/5000000000 : ℝ), (1086683251/2000000000 : ℝ), (-1523082957/10000000000 : ℝ)] ![(44235400142851/100000000000000 : ℝ), (46403345454983/100000000000000 : ℝ), (1872250876709/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615373841/5000000000 : ℝ)|^4983 ≤ (44235400142851/100000000000000 : ℝ)^3959
        have hw : |(2615373841/5000000000 : ℝ)|=(2615373841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086683251/2000000000 : ℝ)|^4983 ≤ (46403345454983/100000000000000 : ℝ)^3959
        have hw : |(1086683251/2000000000 : ℝ)|=(1086683251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1523082957/10000000000 : ℝ)|^4983 ≤ (1872250876709/20000000000000 : ℝ)^3959
        have hw : |(-1523082957/10000000000 : ℝ)|=(1523082957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_box_11 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1132230559/2500000000 : ℝ)*x 0 + (999766163/2500000000 : ℝ)*x 1 + (159962601/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1132230559/2500000000 : ℝ)^4983 ≤ (1153101541731/3125000000000 : ℝ)^3959 := by
    have hnat : (1132230559 : ℕ)^4983*3125000000000^3959 ≤ 1153101541731^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132230559 2500000000 1153101541731 3125000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999766163/2500000000 : ℝ)^4983 ≤ (7887593368651/25000000000000 : ℝ)^3959 := by
    have hnat : (999766163 : ℕ)^4983*25000000000000^3959 ≤ 7887593368651^3959*2500000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999766163 2500000000 7887593368651 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (159962601/400000000 : ℝ)^4983 ≤ (31550377178513/100000000000000 : ℝ)^3959 := by
    have hnat : (159962601 : ℕ)^4983*100000000000000^3959 ≤ 31550377178513^3959*400000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159962601 400000000 31550377178513 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1132230559/2500000000 : ℝ), (999766163/2500000000 : ℝ), (159962601/400000000 : ℝ)] ![(1153101541731/3125000000000 : ℝ), (7887593368651/25000000000000 : ℝ), (31550377178513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1132230559/2500000000 : ℝ)|^4983 ≤ (1153101541731/3125000000000 : ℝ)^3959
        have hw : |(1132230559/2500000000 : ℝ)|=(1132230559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(999766163/2500000000 : ℝ)|^4983 ≤ (7887593368651/25000000000000 : ℝ)^3959
        have hw : |(999766163/2500000000 : ℝ)|=(999766163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(159962601/400000000 : ℝ)|^4983 ≤ (31550377178513/100000000000000 : ℝ)^3959
        have hw : |(159962601/400000000 : ℝ)|=(159962601/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_box_12 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-714286201/5000000000 : ℝ)*x 0 + (221389073/400000000 : ℝ)*x 1 + (5196289773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (714286201/5000000000 : ℝ)^4983 ≤ (8636081492481/100000000000000 : ℝ)^3959 := by
    have hnat : (714286201 : ℕ)^4983*100000000000000^3959 ≤ 8636081492481^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      714286201 5000000000 8636081492481 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221389073/400000000 : ℝ)^4983 ≤ (23747490506299/50000000000000 : ℝ)^3959 := by
    have hnat : (221389073 : ℕ)^4983*50000000000000^3959 ≤ 23747490506299^3959*400000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221389073 400000000 23747490506299 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5196289773/10000000000 : ℝ)^4983 ≤ (21934468737717/50000000000000 : ℝ)^3959 := by
    have hnat : (5196289773 : ℕ)^4983*50000000000000^3959 ≤ 21934468737717^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196289773 10000000000 21934468737717 50000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-714286201/5000000000 : ℝ), (221389073/400000000 : ℝ), (5196289773/10000000000 : ℝ)] ![(8636081492481/100000000000000 : ℝ), (23747490506299/50000000000000 : ℝ), (21934468737717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-714286201/5000000000 : ℝ)|^4983 ≤ (8636081492481/100000000000000 : ℝ)^3959
        have hw : |(-714286201/5000000000 : ℝ)|=(714286201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(221389073/400000000 : ℝ)|^4983 ≤ (23747490506299/50000000000000 : ℝ)^3959
        have hw : |(221389073/400000000 : ℝ)|=(221389073/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5196289773/10000000000 : ℝ)|^4983 ≤ (21934468737717/50000000000000 : ℝ)^3959
        have hw : |(5196289773/10000000000 : ℝ)|=(5196289773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_box_13 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (337073013/625000000 : ℝ)*x 0 + (-812725233/5000000000 : ℝ)*x 1 + (5196289871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337073013/625000000 : ℝ)^4983 ≤ (45971120834211/100000000000000 : ℝ)^3959 := by
    have hnat : (337073013 : ℕ)^4983*100000000000000^3959 ≤ 45971120834211^3959*625000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337073013 625000000 45971120834211 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (812725233/5000000000 : ℝ)^4983 ≤ (1015994063319/10000000000000 : ℝ)^3959 := by
    have hnat : (812725233 : ℕ)^4983*10000000000000^3959 ≤ 1015994063319^3959*5000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      812725233 5000000000 1015994063319 10000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5196289871/10000000000 : ℝ)^4983 ≤ (2193446925839/5000000000000 : ℝ)^3959 := by
    have hnat : (5196289871 : ℕ)^4983*5000000000000^3959 ≤ 2193446925839^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196289871 10000000000 2193446925839 5000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337073013/625000000 : ℝ), (-812725233/5000000000 : ℝ), (5196289871/10000000000 : ℝ)] ![(45971120834211/100000000000000 : ℝ), (1015994063319/10000000000000 : ℝ), (2193446925839/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337073013/625000000 : ℝ)|^4983 ≤ (45971120834211/100000000000000 : ℝ)^3959
        have hw : |(337073013/625000000 : ℝ)|=(337073013/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-812725233/5000000000 : ℝ)|^4983 ≤ (1015994063319/10000000000000 : ℝ)^3959
        have hw : |(-812725233/5000000000 : ℝ)|=(812725233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5196289871/10000000000 : ℝ)|^4983 ≤ (2193446925839/5000000000000 : ℝ)^3959
        have hw : |(5196289871/10000000000 : ℝ)|=(5196289871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_box_14 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5393167907/10000000000 : ℝ)*x 0 + (5196290059/10000000000 : ℝ)*x 1 + (-1625450623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5393167907/10000000000 : ℝ)^4983 ≤ (11492779401219/25000000000000 : ℝ)^3959 := by
    have hnat : (5393167907 : ℕ)^4983*25000000000000^3959 ≤ 11492779401219^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393167907 10000000000 11492779401219 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5196290059/10000000000 : ℝ)^4983 ≤ (8773788102893/20000000000000 : ℝ)^3959 := by
    have hnat : (5196290059 : ℕ)^4983*20000000000000^3959 ≤ 8773788102893^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196290059 10000000000 8773788102893 20000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1625450623/10000000000 : ℝ)^4983 ≤ (2539985467087/25000000000000 : ℝ)^3959 := by
    have hnat : (1625450623 : ℕ)^4983*25000000000000^3959 ≤ 2539985467087^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1625450623 10000000000 2539985467087 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5393167907/10000000000 : ℝ), (5196290059/10000000000 : ℝ), (-1625450623/10000000000 : ℝ)] ![(11492779401219/25000000000000 : ℝ), (8773788102893/20000000000000 : ℝ), (2539985467087/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5393167907/10000000000 : ℝ)|^4983 ≤ (11492779401219/25000000000000 : ℝ)^3959
        have hw : |(5393167907/10000000000 : ℝ)|=(5393167907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5196290059/10000000000 : ℝ)|^4983 ≤ (8773788102893/20000000000000 : ℝ)^3959
        have hw : |(5196290059/10000000000 : ℝ)|=(5196290059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1625450623/10000000000 : ℝ)|^4983 ≤ (2539985467087/25000000000000 : ℝ)^3959
        have hw : |(-1625450623/10000000000 : ℝ)|=(1625450623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1666_box_15 (p : ℝ) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3825755287/10000000000 : ℝ)*x 0 + (87012853/200000000 : ℝ)*x 1 + (435064259/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3825755287/10000000000 : ℝ)^4983 ≤ (29839153420813/100000000000000 : ℝ)^3959 := by
    have hnat : (3825755287 : ℕ)^4983*100000000000000^3959 ≤ 29839153420813^3959*10000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3825755287 10000000000 29839153420813 100000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87012853/200000000 : ℝ)^4983 ≤ (8770105896799/25000000000000 : ℝ)^3959 := by
    have hnat : (87012853 : ℕ)^4983*25000000000000^3959 ≤ 8770105896799^3959*200000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87012853 200000000 8770105896799 25000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (435064259/1000000000 : ℝ)^4983 ≤ (7016084595653/20000000000000 : ℝ)^3959 := by
    have hnat : (435064259 : ℕ)^4983*20000000000000^3959 ≤ 7016084595653^3959*1000000000^4983 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435064259 1000000000 7016084595653 20000000000000 4983 3959 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4983/1024 : ℝ)) 4983 3959 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3825755287/10000000000 : ℝ), (87012853/200000000 : ℝ), (435064259/1000000000 : ℝ)] ![(29839153420813/100000000000000 : ℝ), (8770105896799/25000000000000 : ℝ), (7016084595653/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3825755287/10000000000 : ℝ)|^4983 ≤ (29839153420813/100000000000000 : ℝ)^3959
        have hw : |(3825755287/10000000000 : ℝ)|=(3825755287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(87012853/200000000 : ℝ)|^4983 ≤ (8770105896799/25000000000000 : ℝ)^3959
        have hw : |(87012853/200000000 : ℝ)|=(87012853/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(435064259/1000000000 : ℝ)|^4983 ≤ (7016084595653/20000000000000 : ℝ)^3959
        have hw : |(435064259/1000000000 : ℝ)|=(435064259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1666_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181973587/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4059/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (43/400 : ℝ)*pair X i i ≤ pair X i h) :
    -(65137/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29399/50000 : ℝ) ∧ (81483/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (88377/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4059/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (43/400 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4059/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (43/400 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4059/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (43/400 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4059/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (43/400 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4059/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (43/400 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4059/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (43/400 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (43/400 : ℝ) ^ (4979/1024 : ℝ) ≤ (975849490688751/50000000000000000000 : ℝ) := by
    have hpowers : (43/400 : ℝ)^4979 ≤ (975849490688751/50000000000000000000 : ℝ)^1024 := by
      have hnat : (43 : ℕ)^4979*50000000000000000000^1024 ≤ 975849490688751^1024*400^4979 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43 400 975849490688751 50000000000000000000 4979 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43/400 : ℝ)) (X := (975849490688751/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4059/25000 : ℝ) ^ (4979/1024 : ℝ) ≤ (14491340068790707/100000000000000000000 : ℝ) := by
    have hpowers : (4059/25000 : ℝ)^4979 ≤ (14491340068790707/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4059 : ℕ)^4979*100000000000000000000^1024 ≤ 14491340068790707^1024*25000^4979 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4059 25000 14491340068790707 100000000000000000000 4979 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4059/25000 : ℝ)) (X := (14491340068790707/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000975849490688751/25000000000000000000 : ℝ) ≤ (10000080277516537/10000000000000000 : ℝ) ^ (4979/1024 : ℝ) := by
    have hpowers : (25000975849490688751/25000000000000000000 : ℝ)^1024 ≤ (10000080277516537/10000000000000000 : ℝ)^4979 := by
      have hnat : (25000975849490688751 : ℕ)^1024*10000000000000000^4979 ≤ 10000080277516537^4979*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000975849490688751 25000000000000000000 10000080277516537 10000000000000000 1024 4979 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000080277516537/10000000000000000 : ℝ)) (X := (25000975849490688751/25000000000000000000 : ℝ)) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100016443039050168209/100000000000000000000 : ℝ) ≤ (2500084537921701/2500000000000000 : ℝ) ^ (4979/1024 : ℝ) := by
    have hpowers : (100016443039050168209/100000000000000000000 : ℝ)^1024 ≤ (2500084537921701/2500000000000000 : ℝ)^4979 := by
      have hnat : (100016443039050168209 : ℕ)^1024*2500000000000000^4979 ≤ 2500084537921701^4979*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100016443039050168209 100000000000000000000 2500084537921701 2500000000000000 1024 4979 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500084537921701/2500000000000000 : ℝ)) (X := (100016443039050168209/100000000000000000000 : ℝ)) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50014491340068790707/50000000000000000000 : ℝ) ≤ (10000596025857071/10000000000000000 : ℝ) ^ (4979/1024 : ℝ) := by
    have hpowers : (50014491340068790707/50000000000000000000 : ℝ)^1024 ≤ (10000596025857071/10000000000000000 : ℝ)^4979 := by
      have hnat : (50014491340068790707 : ℕ)^1024*10000000000000000^4979 ≤ 10000596025857071^4979*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014491340068790707 50000000000000000000 10000596025857071 10000000000000000 1024 4979 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000596025857071/10000000000000000 : ℝ)) (X := (50014491340068790707/50000000000000000000 : ℝ)) (by norm_num) 4979 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(975849490688751/50000000000000000000 : ℝ) ≤ ((27427448053897490741/27430000000000000000 : ℝ)+2*(257874170267/548600000000000 : ℝ)*(43/400 : ℝ))^(4979/1024 : ℝ) := by
    rw [show (27427448053897490741/27430000000000000000 : ℝ)+2*(257874170267/548600000000000 : ℝ)*(43/400 : ℝ)=(10000080277516537/10000000000000000 : ℝ) by norm_num, show 1+2*(975849490688751/50000000000000000000 : ℝ)=(25000975849490688751/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14491340068790707/100000000000000000000 : ℝ)+(975849490688751/50000000000000000000 : ℝ) ≤ ((27427448053897490741/27430000000000000000 : ℝ)+(257874170267/548600000000000 : ℝ)*((4059/25000 : ℝ)+(43/400 : ℝ)))^(4979/1024 : ℝ) := by
    rw [show (27427448053897490741/27430000000000000000 : ℝ)+(257874170267/548600000000000 : ℝ)*((4059/25000 : ℝ)+(43/400 : ℝ))=(2500084537921701/2500000000000000 : ℝ) by norm_num, show 1+(14491340068790707/100000000000000000000 : ℝ)+(975849490688751/50000000000000000000 : ℝ)=(100016443039050168209/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14491340068790707/100000000000000000000 : ℝ) ≤ ((27427448053897490741/27430000000000000000 : ℝ)+2*(257874170267/548600000000000 : ℝ)*(4059/25000 : ℝ))^(4979/1024 : ℝ) := by
    rw [show (27427448053897490741/27430000000000000000 : ℝ)+2*(257874170267/548600000000000 : ℝ)*(4059/25000 : ℝ)=(10000596025857071/10000000000000000 : ℝ) by norm_num, show 1+2*(14491340068790707/100000000000000000000 : ℝ)=(50014491340068790707/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27427448053897490741/27430000000000000000 : ℝ)*(X 1 0+X 2 0)+(257874170267/548600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4979/1024 : ℝ)) (lo := (43/400 : ℝ)) (hi := (4059/25000 : ℝ)) (c := (27427448053897490741/27430000000000000000 : ℝ)) (alpha := (257874170267/548600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27427448053897490741/27430000000000000000 : ℝ)*(X 0 1+X 2 1)+(257874170267/548600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4979/1024 : ℝ)) (lo := (43/400 : ℝ)) (hi := (4059/25000 : ℝ)) (c := (27427448053897490741/27430000000000000000 : ℝ)) (alpha := (257874170267/548600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27427448053897490741/27430000000000000000 : ℝ)*(X 0 2+X 1 2)+(257874170267/548600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4979/1024 : ℝ)) (lo := (43/400 : ℝ)) (hi := (4059/25000 : ℝ)) (c := (27427448053897490741/27430000000000000000 : ℝ)) (alpha := (257874170267/548600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-132048609/1000000000 : ℝ)*X 0 0+(1080831509/2000000000 : ℝ)*X 0 1+(2702079879/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5250783391/10000000000 : ℝ)*X 1 0+(-1536113229/10000000000 : ℝ)*X 1 1+(1351039623/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5250783421/10000000000 : ℝ)*X 2 0+(5404159201/10000000000 : ℝ)*X 2 1+(-768056103/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4444440649/10000000000 : ℝ)*X 0 0+(4042519327/10000000000 : ℝ)*X 0 1+(4042521709/10000000000 : ℝ)*X 0 2+(4444440649/10000000000 : ℝ)*X 1 0+(4042519327/10000000000 : ℝ)*X 1 1+(4042521709/10000000000 : ℝ)*X 1 2+(4444440649/10000000000 : ℝ)*X 2 0+(4042519327/10000000000 : ℝ)*X 2 1+(4042521709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-367157669/2000000000 : ℝ)*X 0 0+(1304017233/2500000000 : ℝ)*X 0 1+(5216068697/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5379610103/10000000000 : ℝ)*X 1 0+(-161720039/1000000000 : ℝ)*X 1 1+(5216068999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5379610517/10000000000 : ℝ)*X 2 0+(2608034257/5000000000 : ℝ)*X 2 1+(-808600241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((777219681/2000000000 : ℝ)*X 0 0+(1080343269/2500000000 : ℝ)*X 0 1+(135042909/312500000 : ℝ)*X 0 2+(777219681/2000000000 : ℝ)*X 1 0+(1080343269/2500000000 : ℝ)*X 1 1+(135042909/312500000 : ℝ)*X 1 2+(777219681/2000000000 : ℝ)*X 2 0+(1080343269/2500000000 : ℝ)*X 2 1+(135042909/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1725751501/10000000000 : ℝ)*X 0 0+(1270108379/2500000000 : ℝ)*X 0 1+(2716707983/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((523074789/1000000000 : ℝ)*X 1 0+(-761541559/5000000000 : ℝ)*X 1 1+(5433415933/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2615373841/5000000000 : ℝ)*X 2 0+(1086683251/2000000000 : ℝ)*X 2 1+(-1523082957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1132230559/2500000000 : ℝ)*X 0 0+(999766163/2500000000 : ℝ)*X 0 1+(159962601/400000000 : ℝ)*X 0 2+(1132230559/2500000000 : ℝ)*X 1 0+(999766163/2500000000 : ℝ)*X 1 1+(159962601/400000000 : ℝ)*X 1 2+(1132230559/2500000000 : ℝ)*X 2 0+(999766163/2500000000 : ℝ)*X 2 1+(159962601/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-714286201/5000000000 : ℝ)*X 0 0+(221389073/400000000 : ℝ)*X 0 1+(5196289773/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((337073013/625000000 : ℝ)*X 1 0+(-812725233/5000000000 : ℝ)*X 1 1+(5196289871/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5393167907/10000000000 : ℝ)*X 2 0+(5196290059/10000000000 : ℝ)*X 2 1+(-1625450623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3825755287/10000000000 : ℝ)*X 0 0+(87012853/200000000 : ℝ)*X 0 1+(435064259/1000000000 : ℝ)*X 0 2+(3825755287/10000000000 : ℝ)*X 1 0+(87012853/200000000 : ℝ)*X 1 1+(435064259/1000000000 : ℝ)*X 1 2+(3825755287/10000000000 : ℝ)*X 2 0+(87012853/200000000 : ℝ)*X 2 1+(435064259/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1666_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65137/100000 : ℝ) ≤ (-446659139597327932186028230509183/685750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1155757/100000000000000 : ℝ)*(lower2) + (509943/2000000000000 : ℝ)*(upper4) + (28247961/100000000000000 : ℝ)*(upper5) + (1789216727772521/100000000000000 : ℝ)*(major0) + (1789216727772521/100000000000000 : ℝ)*(major1) + (1789216727772521/100000000000000 : ℝ)*(major2) + (2663676579/50000000000000 : ℝ)*(sp2) + (708645657/100000000000000 : ℝ)*(sp3) + (1308456677711577/50000000000000 : ℝ)*(sp4) + (261690648504817/10000000000000 : ℝ)*(sp5) + (104676431514329/4000000000000 : ℝ)*(sp6) + (491614048973107/50000000000000 : ℝ)*(sp7) + (2759788229/100000000000000 : ℝ)*(sp8) + (2407540803/25000000000000 : ℝ)*(sp13) + (983228806591871/100000000000000 : ℝ)*(f.failure) + (1308458057605691/50000000000000 : ℝ)*(f.sum) + (152149832697387/27430000000000000000000000000 : ℝ)*base65 + (7952888203877921939/2743000000000000000000000000000000 : ℝ)*base68 + (29889952886436078061/2743000000000000000000000000000000 : ℝ)*base69 + (46748171749740078061/2743000000000000000000000000000000 : ℝ)*base71 + (171099710188623/27430000000000000000000000000 : ℝ)*base74 + (40436148959446078061/2743000000000000000000000000000000 : ℝ)*base75 + (29274931939649078061/2743000000000000000000000000000000 : ℝ)*base77 + (9235299175134078061/2743000000000000000000000000000000 : ℝ)*base79 + (32720505735897/27430000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (89088723/10000000000000000000000 : ℝ)*base90 + (89088723/10000000000000000000000 : ℝ)*base92 + (89088723/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29399/50000 : ℝ) ≤ (403224117630939086806795263977937/685750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13076419/50000000000000 : ℝ)*(lower1) + (188254603/100000000000000 : ℝ)*(lower3) + (39357373/100000000000000 : ℝ)*(upper4) + (289503233/100000000000000 : ℝ)*(upper5) + (940942356288027/50000000000000 : ℝ)*(major0) + (940942356288027/50000000000000 : ℝ)*(major1) + (940942356288027/50000000000000 : ℝ)*(major2) + (542001578949071/20000000000000 : ℝ)*(sp0) + (2710016601453901/100000000000000 : ℝ)*(sp1) + (677503544370557/25000000000000 : ℝ)*(sp2) + (206826927981321/20000000000000 : ℝ)*(sp3) + (1211985837/50000000000000 : ℝ)*(sp6) + (9016123991/50000000000000 : ℝ)*(sp11) + (4353354273/50000000000000 : ℝ)*(sp12) + (258538168038647/25000000000000 : ℝ)*(f.failure) + (2710016601453901/100000000000000 : ℝ)*(f.sum) + (5072727160673/1714375000000000000000000000 : ℝ)*base65 + (12143533679606108007/1371500000000000000000000000000000 : ℝ)*base67 + (14475831669647608007/1371500000000000000000000000000000 : ℝ)*base69 + (17852284941430108007/1371500000000000000000000000000000 : ℝ)*base71 + (12966996482659/13715000000000000000000000000 : ℝ)*base73 + (4305126232651608007/1371500000000000000000000000000000 : ℝ)*base75 + (11211373380347608007/1371500000000000000000000000000000 : ℝ)*base77 + (6713007646667608007/1371500000000000000000000000000000 : ℝ)*base79 + (8615927628753/1714375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (783211/2500000000000000000000 : ℝ)*base90 + (783211/2500000000000000000000 : ℝ)*base92 + (783211/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (81483/100000 : ℝ) ≤ (279392271357855343137741788525427/342875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13003643/100000000000000 : ℝ)*(upper0) + (827161/5000000000000 : ℝ)*(lower1) + (342239/12500000000000 : ℝ)*(upper2) + (19945243/100000000000000 : ℝ)*(lower3) + (492972252799451/25000000000000 : ℝ)*(major0) + (492972252799451/25000000000000 : ℝ)*(major1) + (492972252799451/25000000000000 : ℝ)*(major2) + (2032692667/100000000000000 : ℝ)*(sp0) + (5608833419/20000000000000 : ℝ)*(sp2) + (286014293/4000000000000 : ℝ)*(sp3) + (708250376358563/25000000000000 : ℝ)*(sp8) + (70825088453173/2500000000000 : ℝ)*(sp9) + (113319019758393/4000000000000 : ℝ)*(sp10) + (1083605611091293/100000000000000 : ℝ)*(sp11) + (541806380724309/50000000000000 : ℝ)*(f.failure) + (70825088453173/2500000000000 : ℝ)*(f.sum) + (53702495198269/13715000000000000000000000000 : ℝ)*base65 + (2671929089149733191/685750000000000000000000000000000 : ℝ)*base67 + (1492336288367233191/685750000000000000000000000000000 : ℝ)*base69 + (2598050070636516809/685750000000000000000000000000000 : ℝ)*base72 + (109629824476869/13715000000000000000000000000 : ℝ)*base73 + (2767108273340733191/685750000000000000000000000000000 : ℝ)*base75 + (168718186095266809/685750000000000000000000000000000 : ℝ)*base78 + (5916737676452483191/685750000000000000000000000000000 : ℝ)*base79 + (128168761598509/13715000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (33173617/5000000000000000000000 : ℝ)*base90 + (33173617/5000000000000000000000 : ℝ)*base92 + (33173617/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-88377/100000 : ℝ) ≤ (-23308796159068583751441973570719/26375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7256999/50000000000000 : ℝ)*(lower0) + (51898067/100000000000000 : ℝ)*(upper3) + (66961371/100000000000000 : ℝ)*(lower4) + (1008398814064411/50000000000000 : ℝ)*(major0) + (1008398814064411/50000000000000 : ℝ)*(major1) + (1008398814064411/50000000000000 : ℝ)*(major2) + (2559879/250000000000 : ℝ)*(sp0) + (22360075491/100000000000000 : ℝ)*(sp5) + (6150932333/100000000000000 : ℝ)*(sp6) + (10286359967/100000000000000 : ℝ)*(sp7) + (738690254821279/25000000000000 : ℝ)*(sp12) + (369342460395153/12500000000000 : ℝ)*(sp13) + (1477377946152191/50000000000000 : ℝ)*(sp14) + (110828112085883/10000000000000 : ℝ)*(sp15) + (1108291407218797/100000000000000 : ℝ)*(f.failure) + (738690510809179/25000000000000 : ℝ)*(f.sum) + (28217455118221/6857500000000000000000000000 : ℝ)*base65 + (9243728052241031449/1371500000000000000000000000000000 : ℝ)*base68 + (6211838819739031449/1371500000000000000000000000000000 : ℝ)*base70 + (3993533226378031449/1371500000000000000000000000000000 : ℝ)*base72 + (73728127609367/13715000000000000000000000000 : ℝ)*base73 + (1458678099606531449/1371500000000000000000000000000000 : ℝ)*base76 + (974261653983031449/1371500000000000000000000000000000 : ℝ)*base78 + (4483145023258968551/1371500000000000000000000000000000 : ℝ)*base79 + (42748038453377/13715000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (16085161/10000000000000000000000 : ℝ)*base90 + (16085161/10000000000000000000000 : ℝ)*base92 + (16085161/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1666_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181973587/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4059/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (43/400 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65137/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29399/50000 : ℝ) else (81483/100000 : ℝ) ≤ X j i ∧ X j i ≤ (88377/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1666_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1666_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181973587/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10697/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65137/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29399/50000 : ℝ) else (81483/100000 : ℝ) ≤ X j i ∧ X j i ≤ (88377/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1666_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1666_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1666_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4979/1024 : ℝ) ≤ p) (hpb : p ≤ (4983/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181973587/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10697/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65137/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29399/50000 : ℝ) else (81483/100000 : ℝ) ≤ X j i ∧ X j i ≤ (88377/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1666_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
