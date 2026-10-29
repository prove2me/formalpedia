-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1419_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:50:52.005321+00:00
-- url     : https://prove2.me/submissions/f4898b9b-11ad-44aa-af70-818d37ed57fd

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
theorem support_rectangle_w1419_s0_0 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1764489277/10000000000 : ℝ)*x 0 + (5964318639/10000000000 : ℝ)*x 1 + (4828945279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1764489277/10000000000 : ℝ)^4379 ≤ (2597855747583/25000000000000 : ℝ)^3355 := by
    have hnat : (1764489277 : ℕ)^4379*25000000000000^3355 ≤ 2597855747583^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1764489277 10000000000 2597855747583 25000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5964318639/10000000000 : ℝ)^4379 ≤ (1273498392209/2500000000000 : ℝ)^3355 := by
    have hnat : (5964318639 : ℕ)^4379*2500000000000^3355 ≤ 1273498392209^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5964318639 10000000000 1273498392209 2500000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4828945279/10000000000 : ℝ)^4379 ≤ (1933432065437/5000000000000 : ℝ)^3355 := by
    have hnat : (4828945279 : ℕ)^4379*5000000000000^3355 ≤ 1933432065437^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4828945279 10000000000 1933432065437 5000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1764489277/10000000000 : ℝ), (5964318639/10000000000 : ℝ), (4828945279/10000000000 : ℝ)] ![(2597855747583/25000000000000 : ℝ), (1273498392209/2500000000000 : ℝ), (1933432065437/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1764489277/10000000000 : ℝ)|^4379 ≤ (2597855747583/25000000000000 : ℝ)^3355
        have hw : |(-1764489277/10000000000 : ℝ)|=(1764489277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5964318639/10000000000 : ℝ)|^4379 ≤ (1273498392209/2500000000000 : ℝ)^3355
        have hw : |(5964318639/10000000000 : ℝ)|=(5964318639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4828945279/10000000000 : ℝ)|^4379 ≤ (1933432065437/5000000000000 : ℝ)^3355
        have hw : |(4828945279/10000000000 : ℝ)|=(4828945279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s0_1 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1098642409/2000000000 : ℝ)*x 0 + (-1203151817/5000000000 : ℝ)*x 1 + (1207236413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098642409/2000000000 : ℝ)^4379 ≤ (5719093480217/12500000000000 : ℝ)^3355 := by
    have hnat : (1098642409 : ℕ)^4379*12500000000000^3355 ≤ 5719093480217^3355*2000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098642409 2000000000 5719093480217 12500000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1203151817/5000000000 : ℝ)^4379 ≤ (3894651734603/25000000000000 : ℝ)^3355 := by
    have hnat : (1203151817 : ℕ)^4379*25000000000000^3355 ≤ 3894651734603^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203151817 5000000000 3894651734603 25000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1207236413/2500000000 : ℝ)^4379 ≤ (38668645207243/100000000000000 : ℝ)^3355 := by
    have hnat : (1207236413 : ℕ)^4379*100000000000000^3355 ≤ 38668645207243^3355*2500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207236413 2500000000 38668645207243 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1098642409/2000000000 : ℝ), (-1203151817/5000000000 : ℝ), (1207236413/2500000000 : ℝ)] ![(5719093480217/12500000000000 : ℝ), (3894651734603/25000000000000 : ℝ), (38668645207243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1098642409/2000000000 : ℝ)|^4379 ≤ (5719093480217/12500000000000 : ℝ)^3355
        have hw : |(1098642409/2000000000 : ℝ)|=(1098642409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1203151817/5000000000 : ℝ)|^4379 ≤ (3894651734603/25000000000000 : ℝ)^3355
        have hw : |(-1203151817/5000000000 : ℝ)|=(1203151817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1207236413/2500000000 : ℝ)|^4379 ≤ (38668645207243/100000000000000 : ℝ)^3355
        have hw : |(1207236413/2500000000 : ℝ)|=(1207236413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s0_2 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1098642473/2000000000 : ℝ)*x 0 + (603618187/1250000000 : ℝ)*x 1 + (-300787927/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098642473/2000000000 : ℝ)^4379 ≤ (22876375660243/50000000000000 : ℝ)^3355 := by
    have hnat : (1098642473 : ℕ)^4379*50000000000000^3355 ≤ 22876375660243^3355*2000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098642473 2000000000 22876375660243 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (603618187/1250000000 : ℝ)^4379 ≤ (3866864357677/10000000000000 : ℝ)^3355 := by
    have hnat : (603618187 : ℕ)^4379*10000000000000^3355 ≤ 3866864357677^3355*1250000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603618187 1250000000 3866864357677 10000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (300787927/1250000000 : ℝ)^4379 ≤ (3115721019259/20000000000000 : ℝ)^3355 := by
    have hnat : (300787927 : ℕ)^4379*20000000000000^3355 ≤ 3115721019259^3355*1250000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300787927 1250000000 3115721019259 20000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1098642473/2000000000 : ℝ), (603618187/1250000000 : ℝ), (-300787927/1250000000 : ℝ)] ![(22876375660243/50000000000000 : ℝ), (3866864357677/10000000000000 : ℝ), (3115721019259/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1098642473/2000000000 : ℝ)|^4379 ≤ (22876375660243/50000000000000 : ℝ)^3355
        have hw : |(1098642473/2000000000 : ℝ)|=(1098642473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(603618187/1250000000 : ℝ)|^4379 ≤ (3866864357677/10000000000000 : ℝ)^3355
        have hw : |(603618187/1250000000 : ℝ)|=(603618187/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-300787927/1250000000 : ℝ)|^4379 ≤ (3115721019259/20000000000000 : ℝ)^3355
        have hw : |(-300787927/1250000000 : ℝ)|=(300787927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s0_3 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1041859619/2500000000 : ℝ)*x 0 + (3103617053/10000000000 : ℝ)*x 1 + (555081347/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041859619/2500000000 : ℝ)^4379 ≤ (31904148466709/100000000000000 : ℝ)^3355 := by
    have hnat : (1041859619 : ℕ)^4379*100000000000000^3355 ≤ 31904148466709^3355*2500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041859619 2500000000 31904148466709 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3103617053/10000000000 : ℝ)^4379 ≤ (1085795677279/5000000000000 : ℝ)^3355 := by
    have hnat : (3103617053 : ℕ)^4379*5000000000000^3355 ≤ 1085795677279^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3103617053 10000000000 1085795677279 5000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (555081347/1000000000 : ℝ)^4379 ≤ (1449373061281/3125000000000 : ℝ)^3355 := by
    have hnat : (555081347 : ℕ)^4379*3125000000000^3355 ≤ 1449373061281^3355*1000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555081347 1000000000 1449373061281 3125000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1041859619/2500000000 : ℝ), (3103617053/10000000000 : ℝ), (555081347/1000000000 : ℝ)] ![(31904148466709/100000000000000 : ℝ), (1085795677279/5000000000000 : ℝ), (1449373061281/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1041859619/2500000000 : ℝ)|^4379 ≤ (31904148466709/100000000000000 : ℝ)^3355
        have hw : |(1041859619/2500000000 : ℝ)|=(1041859619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3103617053/10000000000 : ℝ)|^4379 ≤ (1085795677279/5000000000000 : ℝ)^3355
        have hw : |(3103617053/10000000000 : ℝ)|=(3103617053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(555081347/1000000000 : ℝ)|^4379 ≤ (1449373061281/3125000000000 : ℝ)^3355
        have hw : |(555081347/1000000000 : ℝ)|=(555081347/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s0_4 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1768555029/10000000000 : ℝ)*x 0 + (607252111/1250000000 : ℝ)*x 1 + (237368357/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1768555029/10000000000 : ℝ)^4379 ≤ (2084537216233/20000000000000 : ℝ)^3355 := by
    have hnat : (1768555029 : ℕ)^4379*20000000000000^3355 ≤ 2084537216233^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768555029 10000000000 2084537216233 20000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (607252111/1250000000 : ℝ)^4379 ≤ (38972769294629/100000000000000 : ℝ)^3355 := by
    have hnat : (607252111 : ℕ)^4379*100000000000000^3355 ≤ 38972769294629^3355*1250000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      607252111 1250000000 38972769294629 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237368357/400000000 : ℝ)^4379 ≤ (506045446153/1000000000000 : ℝ)^3355 := by
    have hnat : (237368357 : ℕ)^4379*1000000000000^3355 ≤ 506045446153^3355*400000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237368357 400000000 506045446153 1000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1768555029/10000000000 : ℝ), (607252111/1250000000 : ℝ), (237368357/400000000 : ℝ)] ![(2084537216233/20000000000000 : ℝ), (38972769294629/100000000000000 : ℝ), (506045446153/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1768555029/10000000000 : ℝ)|^4379 ≤ (2084537216233/20000000000000 : ℝ)^3355
        have hw : |(-1768555029/10000000000 : ℝ)|=(1768555029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(607252111/1250000000 : ℝ)|^4379 ≤ (38972769294629/100000000000000 : ℝ)^3355
        have hw : |(607252111/1250000000 : ℝ)|=(607252111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(237368357/400000000 : ℝ)|^4379 ≤ (506045446153/1000000000000 : ℝ)^3355
        have hw : |(237368357/400000000 : ℝ)|=(237368357/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s0_5 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (647921259/1250000000 : ℝ)*x 0 + (-260207961/2000000000 : ℝ)*x 1 + (5934209011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (647921259/1250000000 : ℝ)^4379 ≤ (21206904289447/50000000000000 : ℝ)^3355 := by
    have hnat : (647921259 : ℕ)^4379*50000000000000^3355 ≤ 21206904289447^3355*1250000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647921259 1250000000 21206904289447 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260207961/2000000000 : ℝ)^4379 ≤ (1396329167433/20000000000000 : ℝ)^3355 := by
    have hnat : (260207961 : ℕ)^4379*20000000000000^3355 ≤ 1396329167433^3355*2000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260207961 2000000000 1396329167433 20000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5934209011/10000000000 : ℝ)^4379 ≤ (50604545572511/100000000000000 : ℝ)^3355 := by
    have hnat : (5934209011 : ℕ)^4379*100000000000000^3355 ≤ 50604545572511^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5934209011 10000000000 50604545572511 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(647921259/1250000000 : ℝ), (-260207961/2000000000 : ℝ), (5934209011/10000000000 : ℝ)] ![(21206904289447/50000000000000 : ℝ), (1396329167433/20000000000000 : ℝ), (50604545572511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(647921259/1250000000 : ℝ)|^4379 ≤ (21206904289447/50000000000000 : ℝ)^3355
        have hw : |(647921259/1250000000 : ℝ)|=(647921259/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-260207961/2000000000 : ℝ)|^4379 ≤ (1396329167433/20000000000000 : ℝ)^3355
        have hw : |(-260207961/2000000000 : ℝ)|=(260207961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5934209011/10000000000 : ℝ)|^4379 ≤ (50604545572511/100000000000000 : ℝ)^3355
        have hw : |(5934209011/10000000000 : ℝ)|=(5934209011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s0_6 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5183370089/10000000000 : ℝ)*x 0 + (2967104417/5000000000 : ℝ)*x 1 + (-65052003/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183370089/10000000000 : ℝ)^4379 ≤ (42413808760457/100000000000000 : ℝ)^3355 := by
    have hnat : (5183370089 : ℕ)^4379*100000000000000^3355 ≤ 42413808760457^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183370089 10000000000 42413808760457 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2967104417/5000000000 : ℝ)^4379 ≤ (25302271801219/50000000000000 : ℝ)^3355 := by
    have hnat : (2967104417 : ℕ)^4379*50000000000000^3355 ≤ 25302271801219^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2967104417 5000000000 25302271801219 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65052003/500000000 : ℝ)^4379 ≤ (8727059529/125000000000 : ℝ)^3355 := by
    have hnat : (65052003 : ℕ)^4379*125000000000^3355 ≤ 8727059529^3355*500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65052003 500000000 8727059529 125000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183370089/10000000000 : ℝ), (2967104417/5000000000 : ℝ), (-65052003/500000000 : ℝ)] ![(42413808760457/100000000000000 : ℝ), (25302271801219/50000000000000 : ℝ), (8727059529/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183370089/10000000000 : ℝ)|^4379 ≤ (42413808760457/100000000000000 : ℝ)^3355
        have hw : |(5183370089/10000000000 : ℝ)|=(5183370089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2967104417/5000000000 : ℝ)|^4379 ≤ (25302271801219/50000000000000 : ℝ)^3355
        have hw : |(2967104417/5000000000 : ℝ)|=(2967104417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65052003/500000000 : ℝ)|^4379 ≤ (8727059529/125000000000 : ℝ)^3355
        have hw : |(-65052003/500000000 : ℝ)|=(65052003/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s0_7 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4176203747/10000000000 : ℝ)*x 0 + (5488152101/10000000000 : ℝ)*x 1 + (126740647/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4176203747/10000000000 : ℝ)^4379 ≤ (31991760757803/100000000000000 : ℝ)^3355 := by
    have hnat : (4176203747 : ℕ)^4379*100000000000000^3355 ≤ 31991760757803^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4176203747 10000000000 31991760757803 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5488152101/10000000000 : ℝ)^4379 ≤ (22848874225219/50000000000000 : ℝ)^3355 := by
    have hnat : (5488152101 : ℕ)^4379*50000000000000^3355 ≤ 22848874225219^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488152101 10000000000 22848874225219 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126740647/400000000 : ℝ)^4379 ≤ (5577622696147/25000000000000 : ℝ)^3355 := by
    have hnat : (126740647 : ℕ)^4379*25000000000000^3355 ≤ 5577622696147^3355*400000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126740647 400000000 5577622696147 25000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4176203747/10000000000 : ℝ), (5488152101/10000000000 : ℝ), (126740647/400000000 : ℝ)] ![(31991760757803/100000000000000 : ℝ), (22848874225219/50000000000000 : ℝ), (5577622696147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4176203747/10000000000 : ℝ)|^4379 ≤ (31991760757803/100000000000000 : ℝ)^3355
        have hw : |(4176203747/10000000000 : ℝ)|=(4176203747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5488152101/10000000000 : ℝ)|^4379 ≤ (22848874225219/50000000000000 : ℝ)^3355
        have hw : |(5488152101/10000000000 : ℝ)|=(5488152101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(126740647/400000000 : ℝ)|^4379 ≤ (5577622696147/25000000000000 : ℝ)^3355
        have hw : |(126740647/400000000 : ℝ)|=(126740647/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1419_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78885271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1977/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26327/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (2189/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2189 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2189*1^512 ≤ 0^512*1^2189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2189 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2189/512 : ℝ) ≤ (397814870553948851/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2189 ≤ (397814870553948851/20000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2189*20000000000000000000^512 ≤ 397814870553948851^512*5^2189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 397814870553948851 20000000000000000000 2189 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (397814870553948851/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2189/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2189 := by
      have hnat : (1 : ℕ)^512*1^2189 ≤ 1^2189*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20397814870553948851/20000000000000000000 : ℝ) ≤ (1004617342517269/1000000000000000 : ℝ) ^ (2189/512 : ℝ) := by
    have hpowers : (20397814870553948851/20000000000000000000 : ℝ)^512 ≤ (1004617342517269/1000000000000000 : ℝ)^2189 := by
      have hnat : (20397814870553948851 : ℕ)^512*1000000000000000^2189 ≤ 1004617342517269^2189*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20397814870553948851 20000000000000000000 1004617342517269 1000000000000000 512 2189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1004617342517269/1000000000000000 : ℝ)) (X := (20397814870553948851/20000000000000000000 : ℝ)) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10397814870553948851/10000000000000000000 : ℝ) ≤ (504617342517269/500000000000000 : ℝ) ^ (2189/512 : ℝ) := by
    have hpowers : (10397814870553948851/10000000000000000000 : ℝ)^512 ≤ (504617342517269/500000000000000 : ℝ)^2189 := by
      have hnat : (10397814870553948851 : ℕ)^512*500000000000000^2189 ≤ 504617342517269^2189*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10397814870553948851 10000000000000000000 504617342517269 500000000000000 512 2189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (504617342517269/500000000000000 : ℝ)) (X := (10397814870553948851/10000000000000000000 : ℝ)) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(4617342517269/400000000000000 : ℝ)*(0 : ℝ))^(2189/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(4617342517269/400000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(397814870553948851/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(4617342517269/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2189/512 : ℝ) := by
    rw [show (1 : ℝ)+(4617342517269/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1004617342517269/1000000000000000 : ℝ) by norm_num, show 1+(397814870553948851/20000000000000000000 : ℝ)+(0 : ℝ)=(20397814870553948851/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(397814870553948851/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(4617342517269/400000000000000 : ℝ)*(2/5 : ℝ))^(2189/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(4617342517269/400000000000000 : ℝ)*(2/5 : ℝ)=(504617342517269/500000000000000 : ℝ) by norm_num, show 1+2*(397814870553948851/20000000000000000000 : ℝ)=(10397814870553948851/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(4617342517269/400000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2189/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4617342517269/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(4617342517269/400000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2189/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4617342517269/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(4617342517269/400000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2189/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4617342517269/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1764489277/10000000000 : ℝ)*X 0 0+(5964318639/10000000000 : ℝ)*X 0 1+(4828945279/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1098642409/2000000000 : ℝ)*X 1 0+(-1203151817/5000000000 : ℝ)*X 1 1+(1207236413/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1098642473/2000000000 : ℝ)*X 2 0+(603618187/1250000000 : ℝ)*X 2 1+(-300787927/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1041859619/2500000000 : ℝ)*X 0 0+(3103617053/10000000000 : ℝ)*X 0 1+(555081347/1000000000 : ℝ)*X 0 2+(1041859619/2500000000 : ℝ)*X 1 0+(3103617053/10000000000 : ℝ)*X 1 1+(555081347/1000000000 : ℝ)*X 1 2+(1041859619/2500000000 : ℝ)*X 2 0+(3103617053/10000000000 : ℝ)*X 2 1+(555081347/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1768555029/10000000000 : ℝ)*X 0 0+(607252111/1250000000 : ℝ)*X 0 1+(237368357/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((647921259/1250000000 : ℝ)*X 1 0+(-260207961/2000000000 : ℝ)*X 1 1+(5934209011/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5183370089/10000000000 : ℝ)*X 2 0+(2967104417/5000000000 : ℝ)*X 2 1+(-65052003/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4176203747/10000000000 : ℝ)*X 0 0+(5488152101/10000000000 : ℝ)*X 0 1+(126740647/400000000 : ℝ)*X 0 2+(4176203747/10000000000 : ℝ)*X 1 0+(5488152101/10000000000 : ℝ)*X 1 1+(126740647/400000000 : ℝ)*X 1 2+(4176203747/10000000000 : ℝ)*X 2 0+(5488152101/10000000000 : ℝ)*X 2 1+(126740647/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (66957272303572360017609/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (211845753/25000000000000 : ℝ)*(base19) + (848577299/100000000000000 : ℝ)*(base23) + (50006629/50000000000000 : ℝ)*(upper3) + (5505737/20000000000000 : ℝ)*(upper4) + (12897529/10000000000000 : ℝ)*(upper5) + (644703831707287/100000000000000 : ℝ)*(major0) + (644703831707287/100000000000000 : ℝ)*(major1) + (644703831707287/100000000000000 : ℝ)*(major2) + (220192587534371/25000000000000 : ℝ)*(sp0) + (880772859654557/100000000000000 : ℝ)*(sp1) + (88077285846027/10000000000000 : ℝ)*(sp2) + (408632337265487/100000000000000 : ℝ)*(sp3) + (671380017/20000000000000 : ℝ)*(sp4) + (1507516061/100000000000000 : ℝ)*(sp7) + (102158461195387/25000000000000 : ℝ)*(f.failure) + (880773707037569/100000000000000 : ℝ)*(f.sum) + (77515886280797/20000000000000000000000000000 : ℝ)*base66 + (110200801519203/40000000000000000000000000000 : ℝ)*base67 + (27914821599203/40000000000000000000000000000 : ℝ)*base69 + (58229347120797/40000000000000000000000000000 : ℝ)*base72 + (62029126040797/20000000000000000000000000000 : ℝ)*base74 + (262149241479203/40000000000000000000000000000 : ℝ)*base75 + (222822673479203/40000000000000000000000000000 : ℝ)*base77 + (109439034959203/40000000000000000000000000000 : ℝ)*base79 + (92809734260797/20000000000000000000000000000 : ℝ)*base82 + (55123/1250000000000000000000 : ℝ)*base90 + (55123/1250000000000000000000 : ℝ)*base92 + (55123/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20090641514935926771819/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (181029103/20000000000000 : ℝ)*(base19) + (911610097/100000000000000 : ℝ)*(base23) + (33550417/25000000000000 : ℝ)*(base32) + (72089061/50000000000000 : ℝ)*(upper3) + (30999229/50000000000000 : ℝ)*(upper5) + (680151834372683/100000000000000 : ℝ)*(major0) + (680151834372683/100000000000000 : ℝ)*(major1) + (680151834372683/100000000000000 : ℝ)*(major2) + (1048737651/50000000000000 : ℝ)*(sp1) + (2154637533/100000000000000 : ℝ)*(sp2) + (929201615684801/100000000000000 : ℝ)*(sp4) + (58074913316499/6250000000000 : ℝ)*(sp5) + (929198549437171/100000000000000 : ℝ)*(sp6) + (107775446230321/25000000000000 : ℝ)*(sp7) + (53887739890369/12500000000000 : ℝ)*(f.failure) + (929201615684801/100000000000000 : ℝ)*(f.sum) + (7013970982727/20000000000000000000000000000 : ℝ)*base65 + (58197230482727/40000000000000000000000000000 : ℝ)*base67 + (150610004362727/40000000000000000000000000000 : ℝ)*base69 + (281524685922727/40000000000000000000000000000 : ℝ)*base71 + (53527032557273/20000000000000000000000000000 : ℝ)*base74 + (156146092242727/40000000000000000000000000000 : ℝ)*base75 + (185853712882727/40000000000000000000000000000 : ℝ)*base77 + (161151202722727/40000000000000000000000000000 : ℝ)*base79 + (19442995122727/20000000000000000000000000000 : ℝ)*base81 + (104999/625000000000000000000 : ℝ)*base89 + (104999/625000000000000000000 : ℝ)*base91 + (104999/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1419_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78885271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1977/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26327/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1419_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1419_s1_0 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1938267151/10000000000 : ℝ)*x 0 + (280462503/500000000 : ℝ)*x 1 + (1268156293/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1938267151/10000000000 : ℝ)^4379 ≤ (5873416678359/50000000000000 : ℝ)^3355 := by
    have hnat : (1938267151 : ℕ)^4379*50000000000000^3355 ≤ 5873416678359^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938267151 10000000000 5873416678359 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280462503/500000000 : ℝ)^4379 ≤ (47018254796687/100000000000000 : ℝ)^3355 := by
    have hnat : (280462503 : ℕ)^4379*100000000000000^3355 ≤ 47018254796687^3355*500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280462503 500000000 47018254796687 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1268156293/2500000000 : ℝ)^4379 ≤ (41234911827561/100000000000000 : ℝ)^3355 := by
    have hnat : (1268156293 : ℕ)^4379*100000000000000^3355 ≤ 41234911827561^3355*2500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268156293 2500000000 41234911827561 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1938267151/10000000000 : ℝ), (280462503/500000000 : ℝ), (1268156293/2500000000 : ℝ)] ![(5873416678359/50000000000000 : ℝ), (47018254796687/100000000000000 : ℝ), (41234911827561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1938267151/10000000000 : ℝ)|^4379 ≤ (5873416678359/50000000000000 : ℝ)^3355
        have hw : |(-1938267151/10000000000 : ℝ)|=(1938267151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280462503/500000000 : ℝ)|^4379 ≤ (47018254796687/100000000000000 : ℝ)^3355
        have hw : |(280462503/500000000 : ℝ)|=(280462503/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1268156293/2500000000 : ℝ)|^4379 ≤ (41234911827561/100000000000000 : ℝ)^3355
        have hw : |(1268156293/2500000000 : ℝ)|=(1268156293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s1_1 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2698907411/5000000000 : ℝ)*x 0 + (-2222838733/10000000000 : ℝ)*x 1 + (2536311209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698907411/5000000000 : ℝ)^4379 ≤ (2235921766393/5000000000000 : ℝ)^3355 := by
    have hnat : (2698907411 : ℕ)^4379*5000000000000^3355 ≤ 2235921766393^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698907411 5000000000 2235921766393 5000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2222838733/10000000000 : ℝ)^4379 ≤ (14046682047717/100000000000000 : ℝ)^3355 := by
    have hnat : (2222838733 : ℕ)^4379*100000000000000^3355 ≤ 14046682047717^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2222838733 10000000000 14046682047717 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2536311209/5000000000 : ℝ)^4379 ≤ (41234882607669/100000000000000 : ℝ)^3355 := by
    have hnat : (2536311209 : ℕ)^4379*100000000000000^3355 ≤ 41234882607669^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536311209 5000000000 41234882607669 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698907411/5000000000 : ℝ), (-2222838733/10000000000 : ℝ), (2536311209/5000000000 : ℝ)] ![(2235921766393/5000000000000 : ℝ), (14046682047717/100000000000000 : ℝ), (41234882607669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698907411/5000000000 : ℝ)|^4379 ≤ (2235921766393/5000000000000 : ℝ)^3355
        have hw : |(2698907411/5000000000 : ℝ)|=(2698907411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2222838733/10000000000 : ℝ)|^4379 ≤ (14046682047717/100000000000000 : ℝ)^3355
        have hw : |(-2222838733/10000000000 : ℝ)|=(2222838733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2536311209/5000000000 : ℝ)|^4379 ≤ (41234882607669/100000000000000 : ℝ)^3355
        have hw : |(2536311209/5000000000 : ℝ)|=(2536311209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s1_2 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5397813119/10000000000 : ℝ)*x 0 + (5072624919/10000000000 : ℝ)*x 1 + (-555709437/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5397813119/10000000000 : ℝ)^4379 ≤ (44718416913117/100000000000000 : ℝ)^3355 := by
    have hnat : (5397813119 : ℕ)^4379*100000000000000^3355 ≤ 44718416913117^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397813119 10000000000 44718416913117 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5072624919/10000000000 : ℝ)^4379 ≤ (10308727285809/25000000000000 : ℝ)^3355 := by
    have hnat : (5072624919 : ℕ)^4379*25000000000000^3355 ≤ 10308727285809^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5072624919 10000000000 10308727285809 25000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (555709437/2500000000 : ℝ)^4379 ≤ (7023336961723/50000000000000 : ℝ)^3355 := by
    have hnat : (555709437 : ℕ)^4379*50000000000000^3355 ≤ 7023336961723^3355*2500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555709437 2500000000 7023336961723 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5397813119/10000000000 : ℝ), (5072624919/10000000000 : ℝ), (-555709437/2500000000 : ℝ)] ![(44718416913117/100000000000000 : ℝ), (10308727285809/25000000000000 : ℝ), (7023336961723/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5397813119/10000000000 : ℝ)|^4379 ≤ (44718416913117/100000000000000 : ℝ)^3355
        have hw : |(5397813119/10000000000 : ℝ)|=(5397813119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5072624919/10000000000 : ℝ)|^4379 ≤ (10308727285809/25000000000000 : ℝ)^3355
        have hw : |(5072624919/10000000000 : ℝ)|=(5072624919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-555709437/2500000000 : ℝ)|^4379 ≤ (7023336961723/50000000000000 : ℝ)^3355
        have hw : |(-555709437/2500000000 : ℝ)|=(555709437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s1_3 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069614549/2500000000 : ℝ)*x 0 + (747033587/2000000000 : ℝ)*x 1 + (1222955771/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069614549/2500000000 : ℝ)^4379 ≤ (33017960236203/100000000000000 : ℝ)^3355 := by
    have hnat : (1069614549 : ℕ)^4379*100000000000000^3355 ≤ 33017960236203^3355*2500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069614549 2500000000 33017960236203 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (747033587/2000000000 : ℝ)^4379 ≤ (6913728326351/25000000000000 : ℝ)^3355 := by
    have hnat : (747033587 : ℕ)^4379*25000000000000^3355 ≤ 6913728326351^3355*2000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      747033587 2000000000 6913728326351 25000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1222955771/2500000000 : ℝ)^4379 ≤ (7865425288491/20000000000000 : ℝ)^3355 := by
    have hnat : (1222955771 : ℕ)^4379*20000000000000^3355 ≤ 7865425288491^3355*2500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222955771 2500000000 7865425288491 20000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069614549/2500000000 : ℝ), (747033587/2000000000 : ℝ), (1222955771/2500000000 : ℝ)] ![(33017960236203/100000000000000 : ℝ), (6913728326351/25000000000000 : ℝ), (7865425288491/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069614549/2500000000 : ℝ)|^4379 ≤ (33017960236203/100000000000000 : ℝ)^3355
        have hw : |(1069614549/2500000000 : ℝ)|=(1069614549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(747033587/2000000000 : ℝ)|^4379 ≤ (6913728326351/25000000000000 : ℝ)^3355
        have hw : |(747033587/2000000000 : ℝ)|=(747033587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1222955771/2500000000 : ℝ)|^4379 ≤ (7865425288491/20000000000000 : ℝ)^3355
        have hw : |(1222955771/2500000000 : ℝ)|=(1222955771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s1_4 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1938678351/10000000000 : ℝ)*x 0 + (5078965229/10000000000 : ℝ)*x 1 + (280140101/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1938678351/10000000000 : ℝ)^4379 ≤ (2937521538051/25000000000000 : ℝ)^3355 := by
    have hnat : (1938678351 : ℕ)^4379*25000000000000^3355 ≤ 2937521538051^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938678351 10000000000 2937521538051 25000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5078965229/10000000000 : ℝ)^4379 ≤ (2581387034757/6250000000000 : ℝ)^3355 := by
    have hnat : (5078965229 : ℕ)^4379*6250000000000^3355 ≤ 2581387034757^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078965229 10000000000 2581387034757 6250000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280140101/500000000 : ℝ)^4379 ≤ (46947721264533/100000000000000 : ℝ)^3355 := by
    have hnat : (280140101 : ℕ)^4379*100000000000000^3355 ≤ 46947721264533^3355*500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280140101 500000000 46947721264533 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1938678351/10000000000 : ℝ), (5078965229/10000000000 : ℝ), (280140101/500000000 : ℝ)] ![(2937521538051/25000000000000 : ℝ), (2581387034757/6250000000000 : ℝ), (46947721264533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1938678351/10000000000 : ℝ)|^4379 ≤ (2937521538051/25000000000000 : ℝ)^3355
        have hw : |(-1938678351/10000000000 : ℝ)|=(1938678351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5078965229/10000000000 : ℝ)|^4379 ≤ (2581387034757/6250000000000 : ℝ)^3355
        have hw : |(5078965229/10000000000 : ℝ)|=(5078965229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280140101/500000000 : ℝ)|^4379 ≤ (46947721264533/100000000000000 : ℝ)^3355
        have hw : |(280140101/500000000 : ℝ)|=(280140101/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s1_5 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657214057/1250000000 : ℝ)*x 0 + (-1692658961/10000000000 : ℝ)*x 1 + (5602802029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657214057/1250000000 : ℝ)^4379 ≤ (43209528743009/100000000000000 : ℝ)^3355 := by
    have hnat : (657214057 : ℕ)^4379*100000000000000^3355 ≤ 43209528743009^3355*1250000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657214057 1250000000 43209528743009 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1692658961/10000000000 : ℝ)^4379 ≤ (4921374937509/50000000000000 : ℝ)^3355 := by
    have hnat : (1692658961 : ℕ)^4379*50000000000000^3355 ≤ 4921374937509^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1692658961 10000000000 4921374937509 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5602802029/10000000000 : ℝ)^4379 ≤ (9389544272593/20000000000000 : ℝ)^3355 := by
    have hnat : (5602802029 : ℕ)^4379*20000000000000^3355 ≤ 9389544272593^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5602802029 10000000000 9389544272593 20000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657214057/1250000000 : ℝ), (-1692658961/10000000000 : ℝ), (5602802029/10000000000 : ℝ)] ![(43209528743009/100000000000000 : ℝ), (4921374937509/50000000000000 : ℝ), (9389544272593/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657214057/1250000000 : ℝ)|^4379 ≤ (43209528743009/100000000000000 : ℝ)^3355
        have hw : |(657214057/1250000000 : ℝ)|=(657214057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1692658961/10000000000 : ℝ)|^4379 ≤ (4921374937509/50000000000000 : ℝ)^3355
        have hw : |(-1692658961/10000000000 : ℝ)|=(1692658961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5602802029/10000000000 : ℝ)|^4379 ≤ (9389544272593/20000000000000 : ℝ)^3355
        have hw : |(5602802029/10000000000 : ℝ)|=(5602802029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s1_6 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525771243/1000000000 : ℝ)*x 0 + (2801400997/5000000000 : ℝ)*x 1 + (-211582381/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525771243/1000000000 : ℝ)^4379 ≤ (8641905692823/20000000000000 : ℝ)^3355 := by
    have hnat : (525771243 : ℕ)^4379*20000000000000^3355 ≤ 8641905692823^3355*1000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525771243 1000000000 8641905692823 20000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2801400997/5000000000 : ℝ)^4379 ≤ (2934232561261/6250000000000 : ℝ)^3355 := by
    have hnat : (2801400997 : ℕ)^4379*6250000000000^3355 ≤ 2934232561261^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2801400997 5000000000 2934232561261 6250000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211582381/1250000000 : ℝ)^4379 ≤ (9842750535329/100000000000000 : ℝ)^3355 := by
    have hnat : (211582381 : ℕ)^4379*100000000000000^3355 ≤ 9842750535329^3355*1250000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211582381 1250000000 9842750535329 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525771243/1000000000 : ℝ), (2801400997/5000000000 : ℝ), (-211582381/1250000000 : ℝ)] ![(8641905692823/20000000000000 : ℝ), (2934232561261/6250000000000 : ℝ), (9842750535329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525771243/1000000000 : ℝ)|^4379 ≤ (8641905692823/20000000000000 : ℝ)^3355
        have hw : |(525771243/1000000000 : ℝ)|=(525771243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2801400997/5000000000 : ℝ)|^4379 ≤ (2934232561261/6250000000000 : ℝ)^3355
        have hw : |(2801400997/5000000000 : ℝ)|=(2801400997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-211582381/1250000000 : ℝ)|^4379 ≤ (9842750535329/100000000000000 : ℝ)^3355
        have hw : |(-211582381/1250000000 : ℝ)|=(211582381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s1_7 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4279344011/10000000000 : ℝ)*x 0 + (4878155093/10000000000 : ℝ)*x 1 + (3749071409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4279344011/10000000000 : ℝ)^4379 ≤ (33026883055939/100000000000000 : ℝ)^3355 := by
    have hnat : (4279344011 : ℕ)^4379*100000000000000^3355 ≤ 33026883055939^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4279344011 10000000000 33026883055939 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4878155093/10000000000 : ℝ)^4379 ≤ (7836753602431/20000000000000 : ℝ)^3355 := by
    have hnat : (4878155093 : ℕ)^4379*20000000000000^3355 ≤ 7836753602431^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4878155093 10000000000 7836753602431 20000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3749071409/10000000000 : ℝ)^4379 ≤ (13894674460383/50000000000000 : ℝ)^3355 := by
    have hnat : (3749071409 : ℕ)^4379*50000000000000^3355 ≤ 13894674460383^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3749071409 10000000000 13894674460383 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4279344011/10000000000 : ℝ), (4878155093/10000000000 : ℝ), (3749071409/10000000000 : ℝ)] ![(33026883055939/100000000000000 : ℝ), (7836753602431/20000000000000 : ℝ), (13894674460383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4279344011/10000000000 : ℝ)|^4379 ≤ (33026883055939/100000000000000 : ℝ)^3355
        have hw : |(4279344011/10000000000 : ℝ)|=(4279344011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4878155093/10000000000 : ℝ)|^4379 ≤ (7836753602431/20000000000000 : ℝ)^3355
        have hw : |(4878155093/10000000000 : ℝ)|=(4878155093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3749071409/10000000000 : ℝ)|^4379 ≤ (13894674460383/50000000000000 : ℝ)^3355
        have hw : |(3749071409/10000000000 : ℝ)|=(3749071409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1419_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78885271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26327/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1977/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (7569/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18913/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26327/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1977/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26327/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1977/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26327/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1977/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26327/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1977/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26327/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1977/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26327/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1977/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1977/100000 : ℝ) ^ (2189/512 : ℝ) ≤ (5185168677917/100000000000000000000 : ℝ) := by
    have hpowers : (1977/100000 : ℝ)^2189 ≤ (5185168677917/100000000000000000000 : ℝ)^512 := by
      have hnat : (1977 : ℕ)^2189*100000000000000000000^512 ≤ 5185168677917^512*100000^2189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1977 100000 5185168677917 100000000000000000000 2189 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1977/100000 : ℝ)) (X := (5185168677917/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hpowhi : (26327/100000 : ℝ) ^ (2189/512 : ℝ) ≤ (83162871095677551/25000000000000000000 : ℝ) := by
    have hpowers : (26327/100000 : ℝ)^2189 ≤ (83162871095677551/25000000000000000000 : ℝ)^512 := by
      have hnat : (26327 : ℕ)^2189*25000000000000000000^512 ≤ 83162871095677551^512*100000^2189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26327 100000 83162871095677551 25000000000000000000 2189 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26327/100000 : ℝ)) (X := (83162871095677551/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000005185168677917/50000000000000000000 : ℝ) ≤ (5000000121279409/5000000000000000 : ℝ) ^ (2189/512 : ℝ) := by
    have hpowers : (50000005185168677917/50000000000000000000 : ℝ)^512 ≤ (5000000121279409/5000000000000000 : ℝ)^2189 := by
      have hnat : (50000005185168677917 : ℕ)^512*5000000000000000^2189 ≤ 5000000121279409^2189*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000005185168677917 50000000000000000000 5000000121279409 5000000000000000 512 2189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000121279409/5000000000000000 : ℝ)) (X := (50000005185168677917/50000000000000000000 : ℝ)) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100332656669551388121/100000000000000000000 : ℝ) ≤ (1000777083640353/1000000000000000 : ℝ) ^ (2189/512 : ℝ) := by
    have hpowers : (100332656669551388121/100000000000000000000 : ℝ)^512 ≤ (1000777083640353/1000000000000000 : ℝ)^2189 := by
      have hnat : (100332656669551388121 : ℕ)^512*1000000000000000^2189 ≤ 1000777083640353^2189*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100332656669551388121 100000000000000000000 1000777083640353 1000000000000000 512 2189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000777083640353/1000000000000000 : ℝ)) (X := (100332656669551388121/100000000000000000000 : ℝ)) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12583162871095677551/12500000000000000000 : ℝ) ≤ (5007770715124121/5000000000000000 : ℝ) ^ (2189/512 : ℝ) := by
    have hpowers : (12583162871095677551/12500000000000000000 : ℝ)^512 ≤ (5007770715124121/5000000000000000 : ℝ)^2189 := by
      have hnat : (12583162871095677551 : ℕ)^512*5000000000000000^2189 ≤ 5007770715124121^2189*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12583162871095677551 12500000000000000000 5007770715124121 5000000000000000 512 2189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007770715124121/5000000000000000 : ℝ)) (X := (12583162871095677551/12500000000000000000 : ℝ)) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5185168677917/100000000000000000000 : ℝ) ≤ ((60867320244561306763/60875000000000000000 : ℝ)+2*(971324230589/304375000000000 : ℝ)*(1977/100000 : ℝ))^(2189/512 : ℝ) := by
    rw [show (60867320244561306763/60875000000000000000 : ℝ)+2*(971324230589/304375000000000 : ℝ)*(1977/100000 : ℝ)=(5000000121279409/5000000000000000 : ℝ) by norm_num, show 1+2*(5185168677917/100000000000000000000 : ℝ)=(50000005185168677917/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(83162871095677551/25000000000000000000 : ℝ)+(5185168677917/100000000000000000000 : ℝ) ≤ ((60867320244561306763/60875000000000000000 : ℝ)+(971324230589/304375000000000 : ℝ)*((26327/100000 : ℝ)+(1977/100000 : ℝ)))^(2189/512 : ℝ) := by
    rw [show (60867320244561306763/60875000000000000000 : ℝ)+(971324230589/304375000000000 : ℝ)*((26327/100000 : ℝ)+(1977/100000 : ℝ))=(1000777083640353/1000000000000000 : ℝ) by norm_num, show 1+(83162871095677551/25000000000000000000 : ℝ)+(5185168677917/100000000000000000000 : ℝ)=(100332656669551388121/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(83162871095677551/25000000000000000000 : ℝ) ≤ ((60867320244561306763/60875000000000000000 : ℝ)+2*(971324230589/304375000000000 : ℝ)*(26327/100000 : ℝ))^(2189/512 : ℝ) := by
    rw [show (60867320244561306763/60875000000000000000 : ℝ)+2*(971324230589/304375000000000 : ℝ)*(26327/100000 : ℝ)=(5007770715124121/5000000000000000 : ℝ) by norm_num, show 1+2*(83162871095677551/25000000000000000000 : ℝ)=(12583162871095677551/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (60867320244561306763/60875000000000000000 : ℝ)*(X 1 0+X 2 0)+(971324230589/304375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2189/512 : ℝ)) (lo := (1977/100000 : ℝ)) (hi := (26327/100000 : ℝ)) (c := (60867320244561306763/60875000000000000000 : ℝ)) (alpha := (971324230589/304375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (60867320244561306763/60875000000000000000 : ℝ)*(X 0 1+X 2 1)+(971324230589/304375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2189/512 : ℝ)) (lo := (1977/100000 : ℝ)) (hi := (26327/100000 : ℝ)) (c := (60867320244561306763/60875000000000000000 : ℝ)) (alpha := (971324230589/304375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (60867320244561306763/60875000000000000000 : ℝ)*(X 0 2+X 1 2)+(971324230589/304375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2189/512 : ℝ)) (lo := (1977/100000 : ℝ)) (hi := (26327/100000 : ℝ)) (c := (60867320244561306763/60875000000000000000 : ℝ)) (alpha := (971324230589/304375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1938267151/10000000000 : ℝ)*X 0 0+(280462503/500000000 : ℝ)*X 0 1+(1268156293/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2698907411/5000000000 : ℝ)*X 1 0+(-2222838733/10000000000 : ℝ)*X 1 1+(2536311209/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5397813119/10000000000 : ℝ)*X 2 0+(5072624919/10000000000 : ℝ)*X 2 1+(-555709437/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1069614549/2500000000 : ℝ)*X 0 0+(747033587/2000000000 : ℝ)*X 0 1+(1222955771/2500000000 : ℝ)*X 0 2+(1069614549/2500000000 : ℝ)*X 1 0+(747033587/2000000000 : ℝ)*X 1 1+(1222955771/2500000000 : ℝ)*X 1 2+(1069614549/2500000000 : ℝ)*X 2 0+(747033587/2000000000 : ℝ)*X 2 1+(1222955771/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1938678351/10000000000 : ℝ)*X 0 0+(5078965229/10000000000 : ℝ)*X 0 1+(280140101/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((657214057/1250000000 : ℝ)*X 1 0+(-1692658961/10000000000 : ℝ)*X 1 1+(5602802029/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((525771243/1000000000 : ℝ)*X 2 0+(2801400997/5000000000 : ℝ)*X 2 1+(-211582381/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4279344011/10000000000 : ℝ)*X 0 0+(4878155093/10000000000 : ℝ)*X 0 1+(3749071409/10000000000 : ℝ)*X 0 2+(4279344011/10000000000 : ℝ)*X 1 0+(4878155093/10000000000 : ℝ)*X 1 1+(3749071409/10000000000 : ℝ)*X 1 2+(4279344011/10000000000 : ℝ)*X 2 0+(4878155093/10000000000 : ℝ)*X 2 1+(3749071409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (207318183520562290125879/60875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93052421/100000000000000 : ℝ)*(base1) + (1133179689/100000000000000 : ℝ)*(base19) + (513099459/100000000000000 : ℝ)*(base23) + (229116059/50000000000000 : ℝ)*(upper5) + (341007593345057/25000000000000 : ℝ)*(major0) + (341007593345057/25000000000000 : ℝ)*(major1) + (341007593345057/25000000000000 : ℝ)*(major2) + (232936847977869/12500000000000 : ℝ)*(sp0) + (186349351896199/10000000000000 : ℝ)*(sp1) + (1863492900306383/100000000000000 : ℝ)*(sp2) + (172913075995847/20000000000000 : ℝ)*(sp3) + (38628851/100000000000000 : ℝ)*(sp5) + (1277364689/100000000000000 : ℝ)*(sp6) + (234718507/50000000000000 : ℝ)*(sp7) + (86456594246867/10000000000000 : ℝ)*(f.failure) + (1863494690770531/100000000000000 : ℝ)*(f.sum) + (5567916038959/30437500000000000000000000000 : ℝ)*base65 + (7826129027339304509/1521875000000000000000000000000000 : ℝ)*base68 + (4196947291967429509/1521875000000000000000000000000000 : ℝ)*base70 + (272608070282570491/1521875000000000000000000000000000 : ℝ)*base71 + (160708070392791/30437500000000000000000000000 : ℝ)*base74 + (13124908015266945491/1521875000000000000000000000000000 : ℝ)*base75 + (4024122762916945491/1521875000000000000000000000000000 : ℝ)*base77 + (3564225721404929509/1521875000000000000000000000000000 : ℝ)*base80 + (17605931722041/30437500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4195957/500000000000000000000 : ℝ)*base89 + (4195957/500000000000000000000 : ℝ)*base91 + (4195957/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (921883118194985392641815421/190234375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19782097/50000000000000 : ℝ)*(base1) + (128077973/12500000000000 : ℝ)*(base19) + (1009753607/100000000000000 : ℝ)*(base23) + (59084907/50000000000000 : ℝ)*(upper3) + (25896923/25000000000000 : ℝ)*(upper5) + (174666591542611/12500000000000 : ℝ)*(major0) + (174666591542611/12500000000000 : ℝ)*(major1) + (174666591542611/12500000000000 : ℝ)*(major2) + (1176690311/20000000000000 : ℝ)*(sp1) + (5679744493/100000000000000 : ℝ)*(sp2) + (76359652131789/4000000000000 : ℝ)*(sp4) + (1908984355655193/100000000000000 : ℝ)*(sp5) + (190898457423243/10000000000000 : ℝ)*(sp6) + (885673999852421/100000000000000 : ℝ)*(sp7) + (177134807883323/20000000000000 : ℝ)*(f.failure) + (1908991263730531/100000000000000 : ℝ)*(f.sum) + (35194138461407/15218750000000000000000000000 : ℝ)*base65 + (4682219898723403193/760937500000000000000000000000000 : ℝ)*base67 + (3083011953634340693/760937500000000000000000000000000 : ℝ)*base69 + (2993330020946840693/760937500000000000000000000000000 : ℝ)*base71 + (95204694310253/60875000000000000000000000000 : ℝ)*base73 + (3148611196942221807/760937500000000000000000000000000 : ℝ)*base76 + (9515799892879653193/760937500000000000000000000000000 : ℝ)*base77 + (6847719073732778193/760937500000000000000000000000000 : ℝ)*base79 + (195546970555253/60875000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (8764467/1000000000000000000000 : ℝ)*base90 + (8764467/1000000000000000000000 : ℝ)*base92 + (8764467/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1419_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78885271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26327/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1977/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7569/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18913/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1419_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1419_s2_0 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-197214907/1000000000 : ℝ)*x 0 + (85319289/156250000 : ℝ)*x 1 + (2599821797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197214907/1000000000 : ℝ)^4379 ≤ (11733944849/97656250000 : ℝ)^3355 := by
    have hnat : (197214907 : ℕ)^4379*97656250000^3355 ≤ 11733944849^3355*1000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197214907 1000000000 11733944849 97656250000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85319289/156250000 : ℝ)^4379 ≤ (22698372478321/50000000000000 : ℝ)^3355 := by
    have hnat : (85319289 : ℕ)^4379*50000000000000^3355 ≤ 22698372478321^3355*156250000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85319289 156250000 22698372478321 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2599821797/5000000000 : ℝ)^4379 ≤ (21293847748583/50000000000000 : ℝ)^3355 := by
    have hnat : (2599821797 : ℕ)^4379*50000000000000^3355 ≤ 21293847748583^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599821797 5000000000 21293847748583 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-197214907/1000000000 : ℝ), (85319289/156250000 : ℝ), (2599821797/5000000000 : ℝ)] ![(11733944849/97656250000 : ℝ), (22698372478321/50000000000000 : ℝ), (21293847748583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-197214907/1000000000 : ℝ)|^4379 ≤ (11733944849/97656250000 : ℝ)^3355
        have hw : |(-197214907/1000000000 : ℝ)|=(197214907/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(85319289/156250000 : ℝ)|^4379 ≤ (22698372478321/50000000000000 : ℝ)^3355
        have hw : |(85319289/156250000 : ℝ)|=(85319289/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2599821797/5000000000 : ℝ)|^4379 ≤ (21293847748583/50000000000000 : ℝ)^3355
        have hw : |(2599821797/5000000000 : ℝ)|=(2599821797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s2_1 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072155407/2000000000 : ℝ)*x 0 + (-32912259/156250000 : ℝ)*x 1 + (1299910883/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072155407/2000000000 : ℝ)^4379 ≤ (44318361319257/100000000000000 : ℝ)^3355 := by
    have hnat : (1072155407 : ℕ)^4379*100000000000000^3355 ≤ 44318361319257^3355*2000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072155407 2000000000 44318361319257 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32912259/156250000 : ℝ)^4379 ≤ (6546971917459/50000000000000 : ℝ)^3355 := by
    have hnat : (32912259 : ℕ)^4379*50000000000000^3355 ≤ 6546971917459^3355*156250000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32912259 156250000 6546971917459 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1299910883/2500000000 : ℝ)^4379 ≤ (21293847417181/50000000000000 : ℝ)^3355 := by
    have hnat : (1299910883 : ℕ)^4379*50000000000000^3355 ≤ 21293847417181^3355*2500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299910883 2500000000 21293847417181 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072155407/2000000000 : ℝ), (-32912259/156250000 : ℝ), (1299910883/2500000000 : ℝ)] ![(44318361319257/100000000000000 : ℝ), (6546971917459/50000000000000 : ℝ), (21293847417181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072155407/2000000000 : ℝ)|^4379 ≤ (44318361319257/100000000000000 : ℝ)^3355
        have hw : |(1072155407/2000000000 : ℝ)|=(1072155407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32912259/156250000 : ℝ)|^4379 ≤ (6546971917459/50000000000000 : ℝ)^3355
        have hw : |(-32912259/156250000 : ℝ)|=(32912259/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1299910883/2500000000 : ℝ)|^4379 ≤ (21293847417181/50000000000000 : ℝ)^3355
        have hw : |(1299910883/2500000000 : ℝ)|=(1299910883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s2_2 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (670097089/1250000000 : ℝ)*x 0 + (649955487/1250000000 : ℝ)*x 1 + (-1053192263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670097089/1250000000 : ℝ)^4379 ≤ (1384948682311/3125000000000 : ℝ)^3355 := by
    have hnat : (670097089 : ℕ)^4379*3125000000000^3355 ≤ 1384948682311^3355*1250000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670097089 1250000000 1384948682311 3125000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (649955487/1250000000 : ℝ)^4379 ≤ (42587698725659/100000000000000 : ℝ)^3355 := by
    have hnat : (649955487 : ℕ)^4379*100000000000000^3355 ≤ 42587698725659^3355*1250000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649955487 1250000000 42587698725659 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053192263/5000000000 : ℝ)^4379 ≤ (13093943429237/100000000000000 : ℝ)^3355 := by
    have hnat : (1053192263 : ℕ)^4379*100000000000000^3355 ≤ 13093943429237^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053192263 5000000000 13093943429237 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670097089/1250000000 : ℝ), (649955487/1250000000 : ℝ), (-1053192263/5000000000 : ℝ)] ![(1384948682311/3125000000000 : ℝ), (42587698725659/100000000000000 : ℝ), (13093943429237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670097089/1250000000 : ℝ)|^4379 ≤ (1384948682311/3125000000000 : ℝ)^3355
        have hw : |(670097089/1250000000 : ℝ)|=(670097089/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(649955487/1250000000 : ℝ)|^4379 ≤ (42587698725659/100000000000000 : ℝ)^3355
        have hw : |(649955487/1250000000 : ℝ)|=(649955487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1053192263/5000000000 : ℝ)|^4379 ≤ (13093943429237/100000000000000 : ℝ)^3355
        have hw : |(-1053192263/5000000000 : ℝ)|=(1053192263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s2_3 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4302349751/10000000000 : ℝ)*x 0 + (1007392541/2500000000 : ℝ)*x 1 + (4591681593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302349751/10000000000 : ℝ)^4379 ≤ (3325881722367/10000000000000 : ℝ)^3355 := by
    have hnat : (4302349751 : ℕ)^4379*10000000000000^3355 ≤ 3325881722367^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302349751 10000000000 3325881722367 10000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007392541/2500000000 : ℝ)^4379 ≤ (7633388027707/25000000000000 : ℝ)^3355 := by
    have hnat : (1007392541 : ℕ)^4379*25000000000000^3355 ≤ 7633388027707^3355*2500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007392541 2500000000 7633388027707 25000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4591681593/10000000000 : ℝ)^4379 ≤ (18103815324831/50000000000000 : ℝ)^3355 := by
    have hnat : (4591681593 : ℕ)^4379*50000000000000^3355 ≤ 18103815324831^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4591681593 10000000000 18103815324831 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302349751/10000000000 : ℝ), (1007392541/2500000000 : ℝ), (4591681593/10000000000 : ℝ)] ![(3325881722367/10000000000000 : ℝ), (7633388027707/25000000000000 : ℝ), (18103815324831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302349751/10000000000 : ℝ)|^4379 ≤ (3325881722367/10000000000000 : ℝ)^3355
        have hw : |(4302349751/10000000000 : ℝ)|=(4302349751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1007392541/2500000000 : ℝ)|^4379 ≤ (7633388027707/25000000000000 : ℝ)^3355
        have hw : |(1007392541/2500000000 : ℝ)|=(1007392541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4591681593/10000000000 : ℝ)|^4379 ≤ (18103815324831/50000000000000 : ℝ)^3355
        have hw : |(4591681593/10000000000 : ℝ)|=(4591681593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s2_4 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-986098303/5000000000 : ℝ)*x 0 + (1040230103/2000000000 : ℝ)*x 1 + (109178299/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (986098303/5000000000 : ℝ)^4379 ≤ (3003984385503/25000000000000 : ℝ)^3355 := by
    have hnat : (986098303 : ℕ)^4379*25000000000000^3355 ≤ 3003984385503^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986098303 5000000000 3003984385503 25000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040230103/2000000000 : ℝ)^4379 ≤ (665684465029/1562500000000 : ℝ)^3355 := by
    have hnat : (1040230103 : ℕ)^4379*1562500000000^3355 ≤ 665684465029^3355*2000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040230103 2000000000 665684465029 1562500000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109178299/200000000 : ℝ)^4379 ≤ (45380256677187/100000000000000 : ℝ)^3355 := by
    have hnat : (109178299 : ℕ)^4379*100000000000000^3355 ≤ 45380256677187^3355*200000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109178299 200000000 45380256677187 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-986098303/5000000000 : ℝ), (1040230103/2000000000 : ℝ), (109178299/200000000 : ℝ)] ![(3003984385503/25000000000000 : ℝ), (665684465029/1562500000000 : ℝ), (45380256677187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-986098303/5000000000 : ℝ)|^4379 ≤ (3003984385503/25000000000000 : ℝ)^3355
        have hw : |(-986098303/5000000000 : ℝ)|=(986098303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1040230103/2000000000 : ℝ)|^4379 ≤ (665684465029/1562500000000 : ℝ)^3355
        have hw : |(1040230103/2000000000 : ℝ)|=(1040230103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(109178299/200000000 : ℝ)|^4379 ≤ (45380256677187/100000000000000 : ℝ)^3355
        have hw : |(109178299/200000000 : ℝ)|=(109178299/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s2_5 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646513561/5000000000 : ℝ)*x 0 + (-923556513/5000000000 : ℝ)*x 1 + (5458915227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646513561/5000000000 : ℝ)^4379 ≤ (435887253729/1000000000000 : ℝ)^3355 := by
    have hnat : (2646513561 : ℕ)^4379*1000000000000^3355 ≤ 435887253729^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646513561 5000000000 435887253729 1000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (923556513/5000000000 : ℝ)^4379 ≤ (11031014927471/100000000000000 : ℝ)^3355 := by
    have hnat : (923556513 : ℕ)^4379*100000000000000^3355 ≤ 11031014927471^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923556513 5000000000 11031014927471 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5458915227/10000000000 : ℝ)^4379 ≤ (45380259682729/100000000000000 : ℝ)^3355 := by
    have hnat : (5458915227 : ℕ)^4379*100000000000000^3355 ≤ 45380259682729^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458915227 10000000000 45380259682729 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646513561/5000000000 : ℝ), (-923556513/5000000000 : ℝ), (5458915227/10000000000 : ℝ)] ![(435887253729/1000000000000 : ℝ), (11031014927471/100000000000000 : ℝ), (45380259682729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646513561/5000000000 : ℝ)|^4379 ≤ (435887253729/1000000000000 : ℝ)^3355
        have hw : |(2646513561/5000000000 : ℝ)|=(2646513561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-923556513/5000000000 : ℝ)|^4379 ≤ (11031014927471/100000000000000 : ℝ)^3355
        have hw : |(-923556513/5000000000 : ℝ)|=(923556513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5458915227/10000000000 : ℝ)|^4379 ≤ (45380259682729/100000000000000 : ℝ)^3355
        have hw : |(5458915227/10000000000 : ℝ)|=(5458915227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s2_6 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058605417/2000000000 : ℝ)*x 0 + (2729457607/5000000000 : ℝ)*x 1 + (-369422619/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058605417/2000000000 : ℝ)^4379 ≤ (43588724975201/100000000000000 : ℝ)^3355 := by
    have hnat : (1058605417 : ℕ)^4379*100000000000000^3355 ≤ 43588724975201^3355*2000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058605417 2000000000 43588724975201 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2729457607/5000000000 : ℝ)^4379 ≤ (1815210381667/4000000000000 : ℝ)^3355 := by
    have hnat : (2729457607 : ℕ)^4379*4000000000000^3355 ≤ 1815210381667^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729457607 5000000000 1815210381667 4000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (369422619/2000000000 : ℝ)^4379 ≤ (344719233291/3125000000000 : ℝ)^3355 := by
    have hnat : (369422619 : ℕ)^4379*3125000000000^3355 ≤ 344719233291^3355*2000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369422619 2000000000 344719233291 3125000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058605417/2000000000 : ℝ), (2729457607/5000000000 : ℝ), (-369422619/2000000000 : ℝ)] ![(43588724975201/100000000000000 : ℝ), (1815210381667/4000000000000 : ℝ), (344719233291/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058605417/2000000000 : ℝ)|^4379 ≤ (43588724975201/100000000000000 : ℝ)^3355
        have hw : |(1058605417/2000000000 : ℝ)|=(1058605417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2729457607/5000000000 : ℝ)|^4379 ≤ (1815210381667/4000000000000 : ℝ)^3355
        have hw : |(2729457607/5000000000 : ℝ)|=(2729457607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-369422619/2000000000 : ℝ)|^4379 ≤ (344719233291/3125000000000 : ℝ)^3355
        have hw : |(-369422619/2000000000 : ℝ)|=(369422619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s2_7 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4302451951/10000000000 : ℝ)*x 0 + (917686739/2000000000 : ℝ)*x 1 + (2016422547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302451951/10000000000 : ℝ)^4379 ≤ (16629924203613/50000000000000 : ℝ)^3355 := by
    have hnat : (4302451951 : ℕ)^4379*50000000000000^3355 ≤ 16629924203613^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302451951 10000000000 16629924203613 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (917686739/2000000000 : ℝ)^4379 ≤ (9043551511743/25000000000000 : ℝ)^3355 := by
    have hnat : (917686739 : ℕ)^4379*25000000000000^3355 ≤ 9043551511743^3355*2000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917686739 2000000000 9043551511743 25000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2016422547/5000000000 : ℝ)^4379 ≤ (30565945538301/100000000000000 : ℝ)^3355 := by
    have hnat : (2016422547 : ℕ)^4379*100000000000000^3355 ≤ 30565945538301^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016422547 5000000000 30565945538301 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302451951/10000000000 : ℝ), (917686739/2000000000 : ℝ), (2016422547/5000000000 : ℝ)] ![(16629924203613/50000000000000 : ℝ), (9043551511743/25000000000000 : ℝ), (30565945538301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302451951/10000000000 : ℝ)|^4379 ≤ (16629924203613/50000000000000 : ℝ)^3355
        have hw : |(4302451951/10000000000 : ℝ)|=(4302451951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(917686739/2000000000 : ℝ)|^4379 ≤ (9043551511743/25000000000000 : ℝ)^3355
        have hw : |(917686739/2000000000 : ℝ)|=(917686739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2016422547/5000000000 : ℝ)|^4379 ≤ (30565945538301/100000000000000 : ℝ)^3355
        have hw : |(2016422547/5000000000 : ℝ)|=(2016422547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1419_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78885271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18913/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7569/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10313/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15831/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18913/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7569/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18913/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7569/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18913/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7569/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18913/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7569/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18913/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7569/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18913/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7569/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7569/100000 : ℝ) ^ (2189/512 : ℝ) ≤ (806160915296189/50000000000000000000 : ℝ) := by
    have hpowers : (7569/100000 : ℝ)^2189 ≤ (806160915296189/50000000000000000000 : ℝ)^512 := by
      have hnat : (7569 : ℕ)^2189*50000000000000000000^512 ≤ 806160915296189^512*100000^2189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7569 100000 806160915296189 50000000000000000000 2189 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7569/100000 : ℝ)) (X := (806160915296189/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hpowhi : (18913/100000 : ℝ) ^ (2189/512 : ℝ) ≤ (40442528043340411/50000000000000000000 : ℝ) := by
    have hpowers : (18913/100000 : ℝ)^2189 ≤ (40442528043340411/50000000000000000000 : ℝ)^512 := by
      have hnat : (18913 : ℕ)^2189*50000000000000000000^512 ≤ 40442528043340411^512*100000^2189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18913 100000 40442528043340411 50000000000000000000 2189 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18913/100000 : ℝ)) (X := (40442528043340411/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000806160915296189/25000000000000000000 : ℝ) ≤ (1000007542243771/1000000000000000 : ℝ) ^ (2189/512 : ℝ) := by
    have hpowers : (25000806160915296189/25000000000000000000 : ℝ)^512 ≤ (1000007542243771/1000000000000000 : ℝ)^2189 := by
      have hnat : (25000806160915296189 : ℕ)^512*1000000000000000^2189 ≤ 1000007542243771^2189*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000806160915296189 25000000000000000000 1000007542243771 1000000000000000 512 2189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000007542243771/1000000000000000 : ℝ)) (X := (25000806160915296189/25000000000000000000 : ℝ)) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (250206243444793183/250000000000000000 : ℝ) ≤ (2500482244360873/2500000000000000 : ℝ) ^ (2189/512 : ℝ) := by
    have hpowers : (250206243444793183/250000000000000000 : ℝ)^512 ≤ (2500482244360873/2500000000000000 : ℝ)^2189 := by
      have hnat : (250206243444793183 : ℕ)^512*2500000000000000^2189 ≤ 2500482244360873^2189*250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250206243444793183 250000000000000000 2500482244360873 2500000000000000 512 2189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500482244360873/2500000000000000 : ℝ)) (X := (250206243444793183/250000000000000000 : ℝ)) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25040442528043340411/25000000000000000000 : ℝ) ≤ (5001891266224637/5000000000000000 : ℝ) ^ (2189/512 : ℝ) := by
    have hpowers : (25040442528043340411/25000000000000000000 : ℝ)^512 ≤ (5001891266224637/5000000000000000 : ℝ)^2189 := by
      have hnat : (25040442528043340411 : ℕ)^512*5000000000000000^2189 ≤ 5001891266224637^2189*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25040442528043340411 25000000000000000000 5001891266224637 5000000000000000 512 2189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001891266224637/5000000000000000 : ℝ)) (X := (25040442528043340411/25000000000000000000 : ℝ)) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(806160915296189/50000000000000000000 : ℝ) ≤ ((28353199119113963581/28360000000000000000 : ℝ)+2*(926777502891/567200000000000 : ℝ)*(7569/100000 : ℝ))^(2189/512 : ℝ) := by
    rw [show (28353199119113963581/28360000000000000000 : ℝ)+2*(926777502891/567200000000000 : ℝ)*(7569/100000 : ℝ)=(1000007542243771/1000000000000000 : ℝ) by norm_num, show 1+2*(806160915296189/50000000000000000000 : ℝ)=(25000806160915296189/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40442528043340411/50000000000000000000 : ℝ)+(806160915296189/50000000000000000000 : ℝ) ≤ ((28353199119113963581/28360000000000000000 : ℝ)+(926777502891/567200000000000 : ℝ)*((18913/100000 : ℝ)+(7569/100000 : ℝ)))^(2189/512 : ℝ) := by
    rw [show (28353199119113963581/28360000000000000000 : ℝ)+(926777502891/567200000000000 : ℝ)*((18913/100000 : ℝ)+(7569/100000 : ℝ))=(2500482244360873/2500000000000000 : ℝ) by norm_num, show 1+(40442528043340411/50000000000000000000 : ℝ)+(806160915296189/50000000000000000000 : ℝ)=(250206243444793183/250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40442528043340411/50000000000000000000 : ℝ) ≤ ((28353199119113963581/28360000000000000000 : ℝ)+2*(926777502891/567200000000000 : ℝ)*(18913/100000 : ℝ))^(2189/512 : ℝ) := by
    rw [show (28353199119113963581/28360000000000000000 : ℝ)+2*(926777502891/567200000000000 : ℝ)*(18913/100000 : ℝ)=(5001891266224637/5000000000000000 : ℝ) by norm_num, show 1+2*(40442528043340411/50000000000000000000 : ℝ)=(25040442528043340411/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28353199119113963581/28360000000000000000 : ℝ)*(X 1 0+X 2 0)+(926777502891/567200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2189/512 : ℝ)) (lo := (7569/100000 : ℝ)) (hi := (18913/100000 : ℝ)) (c := (28353199119113963581/28360000000000000000 : ℝ)) (alpha := (926777502891/567200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28353199119113963581/28360000000000000000 : ℝ)*(X 0 1+X 2 1)+(926777502891/567200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2189/512 : ℝ)) (lo := (7569/100000 : ℝ)) (hi := (18913/100000 : ℝ)) (c := (28353199119113963581/28360000000000000000 : ℝ)) (alpha := (926777502891/567200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28353199119113963581/28360000000000000000 : ℝ)*(X 0 2+X 1 2)+(926777502891/567200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2189/512 : ℝ)) (lo := (7569/100000 : ℝ)) (hi := (18913/100000 : ℝ)) (c := (28353199119113963581/28360000000000000000 : ℝ)) (alpha := (926777502891/567200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-197214907/1000000000 : ℝ)*X 0 0+(85319289/156250000 : ℝ)*X 0 1+(2599821797/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1072155407/2000000000 : ℝ)*X 1 0+(-32912259/156250000 : ℝ)*X 1 1+(1299910883/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((670097089/1250000000 : ℝ)*X 2 0+(649955487/1250000000 : ℝ)*X 2 1+(-1053192263/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4302349751/10000000000 : ℝ)*X 0 0+(1007392541/2500000000 : ℝ)*X 0 1+(4591681593/10000000000 : ℝ)*X 0 2+(4302349751/10000000000 : ℝ)*X 1 0+(1007392541/2500000000 : ℝ)*X 1 1+(4591681593/10000000000 : ℝ)*X 1 2+(4302349751/10000000000 : ℝ)*X 2 0+(1007392541/2500000000 : ℝ)*X 2 1+(4591681593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-986098303/5000000000 : ℝ)*X 0 0+(1040230103/2000000000 : ℝ)*X 0 1+(109178299/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646513561/5000000000 : ℝ)*X 1 0+(-923556513/5000000000 : ℝ)*X 1 1+(5458915227/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058605417/2000000000 : ℝ)*X 2 0+(2729457607/5000000000 : ℝ)*X 2 1+(-369422619/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4302451951/10000000000 : ℝ)*X 0 0+(917686739/2000000000 : ℝ)*X 0 1+(2016422547/5000000000 : ℝ)*X 0 2+(4302451951/10000000000 : ℝ)*X 1 0+(917686739/2000000000 : ℝ)*X 1 1+(2016422547/5000000000 : ℝ)*X 1 2+(4302451951/10000000000 : ℝ)*X 2 0+(917686739/2000000000 : ℝ)*X 2 1+(2016422547/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4347692320282663776264505803/354500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (195479039/10000000000000 : ℝ)*(base19) + (289914323/20000000000000 : ℝ)*(base23) + (18372627/12500000000000 : ℝ)*(lower2) + (352726997/100000000000000 : ℝ)*(upper3) + (1055153/800000000000 : ℝ)*(upper5) + (701695781678579/25000000000000 : ℝ)*(major0) + (701695781678579/25000000000000 : ℝ)*(major1) + (701695781678579/25000000000000 : ℝ)*(major2) + (958628883545563/25000000000000 : ℝ)*(sp0) + (958633812607469/25000000000000 : ℝ)*(sp1) + (958633938912163/25000000000000 : ℝ)*(sp2) + (1779016411972267/100000000000000 : ℝ)*(sp3) + (10835519007/50000000000000 : ℝ)*(sp4) + (6113713141/50000000000000 : ℝ)*(sp7) + (1779028639398549/100000000000000 : ℝ)*(f.failure) + (3834537205220267/100000000000000 : ℝ)*(f.sum) + (42973039854861/7090000000000000000000000000 : ℝ)*base66 + (1780280859828281399/709000000000000000000000000000000 : ℝ)*base67 + (8956290467305281399/709000000000000000000000000000000 : ℝ)*base69 + (43177365882718601/709000000000000000000000000000000 : ℝ)*base72 + (35416345050291/7090000000000000000000000000 : ℝ)*base74 + (6347341305109281399/709000000000000000000000000000000 : ℝ)*base75 + (2139757411758718601/709000000000000000000000000000000 : ℝ)*base78 + (3325910792918281399/709000000000000000000000000000000 : ℝ)*base79 + (18643758603059/7090000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (14871779/5000000000000000000000 : ℝ)*base89 + (14871779/5000000000000000000000 : ℝ)*base91 + (14871779/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4119106676260122508476881829/354500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (195576669/12500000000000 : ℝ)*(base19) + (1750896959/100000000000000 : ℝ)*(base23) + (277408367/100000000000000 : ℝ)*(upper3) + (48386521/50000000000000 : ℝ)*(lower4) + (223159113/100000000000000 : ℝ)*(upper5) + (1419850422202203/50000000000000 : ℝ)*(major0) + (1419850422202203/50000000000000 : ℝ)*(major1) + (1419850422202203/50000000000000 : ℝ)*(major2) + (4169820397/20000000000000 : ℝ)*(sp1) + (1452351497/6250000000000 : ℝ)*(sp2) + (969877090761927/25000000000000 : ℝ)*(sp4) + (969871487333093/25000000000000 : ℝ)*(sp5) + (969870843631699/25000000000000 : ℝ)*(sp6) + (899946469222501/50000000000000 : ℝ)*(sp7) + (899946469222501/50000000000000 : ℝ)*(f.failure) + (969877090761927/25000000000000 : ℝ)*(f.sum) + (34743394460847/14180000000000000000000000000 : ℝ)*base66 + (10310948794776381057/1418000000000000000000000000000000 : ℝ)*base68 + (9083021453980381057/1418000000000000000000000000000000 : ℝ)*base70 + (9038711751694381057/1418000000000000000000000000000000 : ℝ)*base72 + (9582413412433/14180000000000000000000000000 : ℝ)*base73 + (22616420351132381057/1418000000000000000000000000000000 : ℝ)*base76 + (5096241756055618943/1418000000000000000000000000000000 : ℝ)*base77 + (188558228064381057/1418000000000000000000000000000000 : ℝ)*base80 + (18327524877993/14180000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (682771/2500000000000000000000 : ℝ)*base89 + (682771/2500000000000000000000 : ℝ)*base91 + (682771/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1419_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78885271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18913/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7569/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10313/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15831/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1419_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1419_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78885271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10313/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15831/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1419_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1419_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1419_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78885271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10313/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15831/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1419_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
