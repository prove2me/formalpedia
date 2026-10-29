-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1382_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:23:33.423541+00:00
-- url     : https://prove2.me/submissions/573e5223-808f-47da-ad63-b8217c54a891

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
theorem support_rectangle_w1382_s0_0 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-892866841/5000000000 : ℝ)*x 0 + (5979819339/10000000000 : ℝ)*x 1 + (4820362567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (892866841/5000000000 : ℝ)^2171 ≤ (10493312790651/100000000000000 : ℝ)^1659 := by
    have hnat : (892866841 : ℕ)^2171*100000000000000^1659 ≤ 10493312790651^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892866841 5000000000 10493312790651 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5979819339/10000000000 : ℝ)^2171 ≤ (12755856363083/25000000000000 : ℝ)^1659 := by
    have hnat : (5979819339 : ℕ)^2171*25000000000000^1659 ≤ 12755856363083^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5979819339 10000000000 12755856363083 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4820362567/10000000000 : ℝ)^2171 ≤ (19241630873561/50000000000000 : ℝ)^1659 := by
    have hnat : (4820362567 : ℕ)^2171*50000000000000^1659 ≤ 19241630873561^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4820362567 10000000000 19241630873561 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-892866841/5000000000 : ℝ), (5979819339/10000000000 : ℝ), (4820362567/10000000000 : ℝ)] ![(10493312790651/100000000000000 : ℝ), (12755856363083/25000000000000 : ℝ), (19241630873561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-892866841/5000000000 : ℝ)|^2171 ≤ (10493312790651/100000000000000 : ℝ)^1659
        have hw : |(-892866841/5000000000 : ℝ)|=(892866841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5979819339/10000000000 : ℝ)|^2171 ≤ (12755856363083/25000000000000 : ℝ)^1659
        have hw : |(5979819339/10000000000 : ℝ)|=(5979819339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4820362567/10000000000 : ℝ)|^2171 ≤ (19241630873561/50000000000000 : ℝ)^1659
        have hw : |(4820362567/10000000000 : ℝ)|=(4820362567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s0_1 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5497338947/10000000000 : ℝ)*x 0 + (-2442870787/10000000000 : ℝ)*x 1 + (1205090813/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5497338947/10000000000 : ℝ)^2171 ≤ (11426112179181/25000000000000 : ℝ)^1659 := by
    have hnat : (5497338947 : ℕ)^2171*25000000000000^1659 ≤ 11426112179181^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497338947 10000000000 11426112179181 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2442870787/10000000000 : ℝ)^2171 ≤ (3162456473393/20000000000000 : ℝ)^1659 := by
    have hnat : (2442870787 : ℕ)^2171*20000000000000^1659 ≤ 3162456473393^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2442870787 10000000000 3162456473393 20000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1205090813/2500000000 : ℝ)^2171 ≤ (9620817225887/25000000000000 : ℝ)^1659 := by
    have hnat : (1205090813 : ℕ)^2171*25000000000000^1659 ≤ 9620817225887^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205090813 2500000000 9620817225887 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5497338947/10000000000 : ℝ), (-2442870787/10000000000 : ℝ), (1205090813/2500000000 : ℝ)] ![(11426112179181/25000000000000 : ℝ), (3162456473393/20000000000000 : ℝ), (9620817225887/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5497338947/10000000000 : ℝ)|^2171 ≤ (11426112179181/25000000000000 : ℝ)^1659
        have hw : |(5497338947/10000000000 : ℝ)|=(5497338947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2442870787/10000000000 : ℝ)|^2171 ≤ (3162456473393/20000000000000 : ℝ)^1659
        have hw : |(-2442870787/10000000000 : ℝ)|=(2442870787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1205090813/2500000000 : ℝ)|^2171 ≤ (9620817225887/25000000000000 : ℝ)^1659
        have hw : |(1205090813/2500000000 : ℝ)|=(1205090813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s0_2 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1374334701/2500000000 : ℝ)*x 0 + (150636327/312500000 : ℝ)*x 1 + (-1221435971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1374334701/2500000000 : ℝ)^2171 ≤ (22852223580459/50000000000000 : ℝ)^1659 := by
    have hnat : (1374334701 : ℕ)^2171*50000000000000^1659 ≤ 22852223580459^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374334701 2500000000 22852223580459 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (150636327/312500000 : ℝ)^2171 ≤ (38483260671047/100000000000000 : ℝ)^1659 := by
    have hnat : (150636327 : ℕ)^2171*100000000000000^1659 ≤ 38483260671047^1659*312500000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150636327 312500000 38483260671047 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1221435971/5000000000 : ℝ)^2171 ≤ (7906146075179/50000000000000 : ℝ)^1659 := by
    have hnat : (1221435971 : ℕ)^2171*50000000000000^1659 ≤ 7906146075179^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221435971 5000000000 7906146075179 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1374334701/2500000000 : ℝ), (150636327/312500000 : ℝ), (-1221435971/5000000000 : ℝ)] ![(22852223580459/50000000000000 : ℝ), (38483260671047/100000000000000 : ℝ), (7906146075179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1374334701/2500000000 : ℝ)|^2171 ≤ (22852223580459/50000000000000 : ℝ)^1659
        have hw : |(1374334701/2500000000 : ℝ)|=(1374334701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(150636327/312500000 : ℝ)|^2171 ≤ (38483260671047/100000000000000 : ℝ)^1659
        have hw : |(150636327/312500000 : ℝ)|=(150636327/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1221435971/5000000000 : ℝ)|^2171 ≤ (7906146075179/50000000000000 : ℝ)^1659
        have hw : |(-1221435971/5000000000 : ℝ)|=(1221435971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s0_3 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (6520031/15625000 : ℝ)*x 0 + (3104819557/10000000000 : ℝ)*x 1 + (2784992043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6520031/15625000 : ℝ)^2171 ≤ (1991437947461/6250000000000 : ℝ)^1659 := by
    have hnat : (6520031 : ℕ)^2171*6250000000000^1659 ≤ 1991437947461^1659*15625000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6520031 15625000 1991437947461 6250000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3104819557/10000000000 : ℝ)^2171 ≤ (4328115099549/20000000000000 : ℝ)^1659 := by
    have hnat : (3104819557 : ℕ)^2171*20000000000000^1659 ≤ 4328115099549^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104819557 10000000000 4328115099549 20000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2784992043/5000000000 : ℝ)^2171 ≤ (46496417323373/100000000000000 : ℝ)^1659 := by
    have hnat : (2784992043 : ℕ)^2171*100000000000000^1659 ≤ 46496417323373^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2784992043 5000000000 46496417323373 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6520031/15625000 : ℝ), (3104819557/10000000000 : ℝ), (2784992043/5000000000 : ℝ)] ![(1991437947461/6250000000000 : ℝ), (4328115099549/20000000000000 : ℝ), (46496417323373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6520031/15625000 : ℝ)|^2171 ≤ (1991437947461/6250000000000 : ℝ)^1659
        have hw : |(6520031/15625000 : ℝ)|=(6520031/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3104819557/10000000000 : ℝ)|^2171 ≤ (4328115099549/20000000000000 : ℝ)^1659
        have hw : |(3104819557/10000000000 : ℝ)|=(3104819557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2784992043/5000000000 : ℝ)|^2171 ≤ (46496417323373/100000000000000 : ℝ)^1659
        have hw : |(2784992043/5000000000 : ℝ)|=(2784992043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s0_4 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-894992243/5000000000 : ℝ)*x 0 + (1212532191/2500000000 : ℝ)*x 1 + (297449461/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (894992243/5000000000 : ℝ)^2171 ≤ (10526012196091/100000000000000 : ℝ)^1659 := by
    have hnat : (894992243 : ℕ)^2171*100000000000000^1659 ≤ 10526012196091^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894992243 5000000000 10526012196091 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1212532191/2500000000 : ℝ)^2171 ≤ (2424658446463/6250000000000 : ℝ)^1659 := by
    have hnat : (1212532191 : ℕ)^2171*6250000000000^1659 ≤ 2424658446463^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212532191 2500000000 2424658446463 6250000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (297449461/500000000 : ℝ)^2171 ≤ (25339726317359/50000000000000 : ℝ)^1659 := by
    have hnat : (297449461 : ℕ)^2171*50000000000000^1659 ≤ 25339726317359^1659*500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297449461 500000000 25339726317359 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-894992243/5000000000 : ℝ), (1212532191/2500000000 : ℝ), (297449461/500000000 : ℝ)] ![(10526012196091/100000000000000 : ℝ), (2424658446463/6250000000000 : ℝ), (25339726317359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-894992243/5000000000 : ℝ)|^2171 ≤ (10526012196091/100000000000000 : ℝ)^1659
        have hw : |(-894992243/5000000000 : ℝ)|=(894992243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1212532191/2500000000 : ℝ)|^2171 ≤ (2424658446463/6250000000000 : ℝ)^1659
        have hw : |(1212532191/2500000000 : ℝ)|=(1212532191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(297449461/500000000 : ℝ)|^2171 ≤ (25339726317359/50000000000000 : ℝ)^1659
        have hw : |(297449461/500000000 : ℝ)|=(297449461/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s0_5 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5181114911/10000000000 : ℝ)*x 0 + (-1314245471/10000000000 : ℝ)*x 1 + (2974494533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5181114911/10000000000 : ℝ)^2171 ≤ (42294960132471/100000000000000 : ℝ)^1659 := by
    have hnat : (5181114911 : ℕ)^2171*100000000000000^1659 ≤ 42294960132471^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181114911 10000000000 42294960132471 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1314245471/10000000000 : ℝ)^2171 ≤ (3512794463369/50000000000000 : ℝ)^1659 := by
    have hnat : (1314245471 : ℕ)^2171*50000000000000^1659 ≤ 3512794463369^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314245471 10000000000 3512794463369 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2974494533/5000000000 : ℝ)^2171 ≤ (10135890183581/20000000000000 : ℝ)^1659 := by
    have hnat : (2974494533 : ℕ)^2171*20000000000000^1659 ≤ 10135890183581^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2974494533 5000000000 10135890183581 20000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5181114911/10000000000 : ℝ), (-1314245471/10000000000 : ℝ), (2974494533/5000000000 : ℝ)] ![(42294960132471/100000000000000 : ℝ), (3512794463369/50000000000000 : ℝ), (10135890183581/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5181114911/10000000000 : ℝ)|^2171 ≤ (42294960132471/100000000000000 : ℝ)^1659
        have hw : |(5181114911/10000000000 : ℝ)|=(5181114911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1314245471/10000000000 : ℝ)|^2171 ≤ (3512794463369/50000000000000 : ℝ)^1659
        have hw : |(-1314245471/10000000000 : ℝ)|=(1314245471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2974494533/5000000000 : ℝ)|^2171 ≤ (10135890183581/20000000000000 : ℝ)^1659
        have hw : |(2974494533/5000000000 : ℝ)|=(2974494533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s0_6 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1295278649/2500000000 : ℝ)*x 0 + (1487247301/2500000000 : ℝ)*x 1 + (-657122867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1295278649/2500000000 : ℝ)^2171 ≤ (21147478383719/50000000000000 : ℝ)^1659 := by
    have hnat : (1295278649 : ℕ)^2171*50000000000000^1659 ≤ 21147478383719^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295278649 2500000000 21147478383719 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1487247301/2500000000 : ℝ)^2171 ≤ (12669863114087/25000000000000 : ℝ)^1659 := by
    have hnat : (1487247301 : ℕ)^2171*25000000000000^1659 ≤ 12669863114087^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1487247301 2500000000 12669863114087 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657122867/5000000000 : ℝ)^2171 ≤ (7025590766559/100000000000000 : ℝ)^1659 := by
    have hnat : (657122867 : ℕ)^2171*100000000000000^1659 ≤ 7025590766559^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657122867 5000000000 7025590766559 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1295278649/2500000000 : ℝ), (1487247301/2500000000 : ℝ), (-657122867/5000000000 : ℝ)] ![(21147478383719/50000000000000 : ℝ), (12669863114087/25000000000000 : ℝ), (7025590766559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1295278649/2500000000 : ℝ)|^2171 ≤ (21147478383719/50000000000000 : ℝ)^1659
        have hw : |(1295278649/2500000000 : ℝ)|=(1295278649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1487247301/2500000000 : ℝ)|^2171 ≤ (12669863114087/25000000000000 : ℝ)^1659
        have hw : |(1487247301/2500000000 : ℝ)|=(1487247301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-657122867/5000000000 : ℝ)|^2171 ≤ (7025590766559/100000000000000 : ℝ)^1659
        have hw : |(-657122867/5000000000 : ℝ)|=(657122867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s0_7 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2090927591/5000000000 : ℝ)*x 0 + (1376674199/2500000000 : ℝ)*x 1 + (792592143/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2090927591/5000000000 : ℝ)^2171 ≤ (15976661109373/50000000000000 : ℝ)^1659 := by
    have hnat : (2090927591 : ℕ)^2171*50000000000000^1659 ≤ 15976661109373^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090927591 5000000000 15976661109373 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376674199/2500000000 : ℝ)^2171 ≤ (11451571654973/25000000000000 : ℝ)^1659 := by
    have hnat : (1376674199 : ℕ)^2171*25000000000000^1659 ≤ 11451571654973^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376674199 2500000000 11451571654973 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (792592143/2500000000 : ℝ)^2171 ≤ (11120195570897/50000000000000 : ℝ)^1659 := by
    have hnat : (792592143 : ℕ)^2171*50000000000000^1659 ≤ 11120195570897^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792592143 2500000000 11120195570897 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2090927591/5000000000 : ℝ), (1376674199/2500000000 : ℝ), (792592143/2500000000 : ℝ)] ![(15976661109373/50000000000000 : ℝ), (11451571654973/25000000000000 : ℝ), (11120195570897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2090927591/5000000000 : ℝ)|^2171 ≤ (15976661109373/50000000000000 : ℝ)^1659
        have hw : |(2090927591/5000000000 : ℝ)|=(2090927591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1376674199/2500000000 : ℝ)|^2171 ≤ (11451571654973/25000000000000 : ℝ)^1659
        have hw : |(1376674199/2500000000 : ℝ)|=(1376674199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(792592143/2500000000 : ℝ)|^2171 ≤ (11120195570897/50000000000000 : ℝ)^1659
        have hw : |(792592143/2500000000 : ℝ)|=(792592143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1382_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (171/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13293/50000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (0 : ℝ) ^ (4341/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4341 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4341*1^1024 ≤ 0^1024*1^4341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4341 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4341/1024 : ℝ) ≤ (2056031240697457049/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4341 ≤ (2056031240697457049/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4341*100000000000000000000^1024 ≤ 2056031240697457049^1024*5^4341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2056031240697457049 100000000000000000000 4341 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2056031240697457049/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4341 := by
      have hnat : (1 : ℕ)^1024*1^4341 ≤ 1^4341*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102056031240697457049/100000000000000000000 : ℝ) ≤ (10048123360118223/10000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (102056031240697457049/100000000000000000000 : ℝ)^1024 ≤ (10048123360118223/10000000000000000 : ℝ)^4341 := by
      have hnat : (102056031240697457049 : ℕ)^1024*10000000000000000^4341 ≤ 10048123360118223^4341*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102056031240697457049 100000000000000000000 10048123360118223 10000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10048123360118223/10000000000000000 : ℝ)) (X := (102056031240697457049/100000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52056031240697457049/50000000000000000000 : ℝ) ≤ (5048123360118223/5000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (52056031240697457049/50000000000000000000 : ℝ)^1024 ≤ (5048123360118223/5000000000000000 : ℝ)^4341 := by
      have hnat : (52056031240697457049 : ℕ)^1024*5000000000000000^4341 ≤ 5048123360118223^4341*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52056031240697457049 50000000000000000000 5048123360118223 5000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5048123360118223/5000000000000000 : ℝ)) (X := (52056031240697457049/50000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(48123360118223/4000000000000000 : ℝ)*(0 : ℝ))^(4341/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(48123360118223/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2056031240697457049/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(48123360118223/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4341/1024 : ℝ) := by
    rw [show (1 : ℝ)+(48123360118223/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10048123360118223/10000000000000000 : ℝ) by norm_num, show 1+(2056031240697457049/100000000000000000000 : ℝ)+(0 : ℝ)=(102056031240697457049/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2056031240697457049/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(48123360118223/4000000000000000 : ℝ)*(2/5 : ℝ))^(4341/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(48123360118223/4000000000000000 : ℝ)*(2/5 : ℝ)=(5048123360118223/5000000000000000 : ℝ) by norm_num, show 1+2*(2056031240697457049/100000000000000000000 : ℝ)=(52056031240697457049/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(48123360118223/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48123360118223/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(48123360118223/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48123360118223/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(48123360118223/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (48123360118223/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-892866841/5000000000 : ℝ)*X 0 0+(5979819339/10000000000 : ℝ)*X 0 1+(4820362567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5497338947/10000000000 : ℝ)*X 1 0+(-2442870787/10000000000 : ℝ)*X 1 1+(1205090813/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1374334701/2500000000 : ℝ)*X 2 0+(150636327/312500000 : ℝ)*X 2 1+(-1221435971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((6520031/15625000 : ℝ)*X 0 0+(3104819557/10000000000 : ℝ)*X 0 1+(2784992043/5000000000 : ℝ)*X 0 2+(6520031/15625000 : ℝ)*X 1 0+(3104819557/10000000000 : ℝ)*X 1 1+(2784992043/5000000000 : ℝ)*X 1 2+(6520031/15625000 : ℝ)*X 2 0+(3104819557/10000000000 : ℝ)*X 2 1+(2784992043/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-894992243/5000000000 : ℝ)*X 0 0+(1212532191/2500000000 : ℝ)*X 0 1+(297449461/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5181114911/10000000000 : ℝ)*X 1 0+(-1314245471/10000000000 : ℝ)*X 1 1+(2974494533/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1295278649/2500000000 : ℝ)*X 2 0+(1487247301/2500000000 : ℝ)*X 2 1+(-657122867/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2090927591/5000000000 : ℝ)*X 0 0+(1376674199/2500000000 : ℝ)*X 0 1+(792592143/2500000000 : ℝ)*X 0 2+(2090927591/5000000000 : ℝ)*X 1 0+(1376674199/2500000000 : ℝ)*X 1 1+(792592143/2500000000 : ℝ)*X 1 2+(2090927591/5000000000 : ℝ)*X 2 0+(1376674199/2500000000 : ℝ)*X 2 1+(792592143/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6701311341872245227/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (132723733/50000000000000 : ℝ)*(base1) + (770527/25000000000000 : ℝ)*(base16) + (1560481967/100000000000000 : ℝ)*(base19) + (61645149/4000000000000 : ℝ)*(base23) + (297528531/100000000000000 : ℝ)*(upper3) + (63406955820921/10000000000000 : ℝ)*(major0) + (63406955820921/10000000000000 : ℝ)*(major1) + (63406955820921/10000000000000 : ℝ)*(major2) + (215619616466727/25000000000000 : ℝ)*(sp0) + (53905033674781/6250000000000 : ℝ)*(sp1) + (431240280615923/50000000000000 : ℝ)*(sp2) + (405654019325709/100000000000000 : ℝ)*(sp3) + (390194113/10000000000000 : ℝ)*(sp4) + (2505907621/100000000000000 : ℝ)*(sp7) + (101414197670199/25000000000000 : ℝ)*(f.failure) + (862482102360571/100000000000000 : ℝ)*(f.sum) + (47366493823383/20000000000000000000000000000 : ℝ)*base65 + (85553762303383/40000000000000000000000000000 : ℝ)*base67 + (22895648136617/40000000000000000000000000000 : ℝ)*base70 + (261459044983383/40000000000000000000000000000 : ℝ)*base71 + (56095640796617/20000000000000000000000000000 : ℝ)*base74 + (9012190376617/40000000000000000000000000000 : ℝ)*base76 + (137922146103383/40000000000000000000000000000 : ℝ)*base77 + (239408505823383/40000000000000000000000000000 : ℝ)*base79 + (2329208336617/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (24256701/2500000000000000000000 : ℝ)*base90 + (24256701/2500000000000000000000 : ℝ)*base92 + (24256701/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2611693966248475437/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (646762721/50000000000000 : ℝ)*(base19) + (247165713/20000000000000 : ℝ)*(base23) + (60129581/50000000000000 : ℝ)*(base32) + (88699857/50000000000000 : ℝ)*(upper3) + (24289937/20000000000000 : ℝ)*(upper5) + (26761103234729/4000000000000 : ℝ)*(major0) + (26761103234729/4000000000000 : ℝ)*(major1) + (26761103234729/4000000000000 : ℝ)*(major2) + (184181031/6250000000000 : ℝ)*(sp1) + (2908080413/100000000000000 : ℝ)*(sp2) + (14219268859669/1562500000000 : ℝ)*(sp4) + (455014483298439/50000000000000 : ℝ)*(sp5) + (455014531554919/50000000000000 : ℝ)*(sp6) + (214010830172769/50000000000000 : ℝ)*(sp7) + (4280217806047/1000000000000 : ℝ)*(f.failure) + (14219268859669/1562500000000 : ℝ)*(f.sum) + (5710844646567/8000000000000000000000000000 : ℝ)*base65 + (26375955385433/16000000000000000000000000000 : ℝ)*base68 + (66831564729433/16000000000000000000000000000 : ℝ)*base70 + (78184528409433/16000000000000000000000000000 : ℝ)*base72 + (7899604502567/8000000000000000000000000000 : ℝ)*base73 + (42776163449433/16000000000000000000000000000 : ℝ)*base76 + (87460751289433/16000000000000000000000000000 : ℝ)*base78 + (24394885945433/16000000000000000000000000000 : ℝ)*base80 + (6291330582567/8000000000000000000000000000 : ℝ)*base81 + (630347/100000000000000000000 : ℝ)*base89 + (630347/100000000000000000000 : ℝ)*base91 + (630347/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1382_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (171/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13293/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1382_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1382_s1_0 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1964795071/10000000000 : ℝ)*x 0 + (1406161457/2500000000 : ℝ)*x 1 + (2530408313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1964795071/10000000000 : ℝ)^2171 ≤ (11891073945149/100000000000000 : ℝ)^1659 := by
    have hnat : (1964795071 : ℕ)^2171*100000000000000^1659 ≤ 11891073945149^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1964795071 10000000000 11891073945149 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1406161457/2500000000 : ℝ)^2171 ≤ (47094440663363/100000000000000 : ℝ)^1659 := by
    have hnat : (1406161457 : ℕ)^2171*100000000000000^1659 ≤ 47094440663363^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1406161457 2500000000 47094440663363 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2530408313/5000000000 : ℝ)^2171 ≤ (8202897076337/20000000000000 : ℝ)^1659 := by
    have hnat : (2530408313 : ℕ)^2171*20000000000000^1659 ≤ 8202897076337^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2530408313 5000000000 8202897076337 20000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1964795071/10000000000 : ℝ), (1406161457/2500000000 : ℝ), (2530408313/5000000000 : ℝ)] ![(11891073945149/100000000000000 : ℝ), (47094440663363/100000000000000 : ℝ), (8202897076337/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1964795071/10000000000 : ℝ)|^2171 ≤ (11891073945149/100000000000000 : ℝ)^1659
        have hw : |(-1964795071/10000000000 : ℝ)|=(1964795071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1406161457/2500000000 : ℝ)|^2171 ≤ (47094440663363/100000000000000 : ℝ)^1659
        have hw : |(1406161457/2500000000 : ℝ)|=(1406161457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2530408313/5000000000 : ℝ)|^2171 ≤ (8202897076337/20000000000000 : ℝ)^1659
        have hw : |(2530408313/5000000000 : ℝ)|=(2530408313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s1_1 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1080315707/2000000000 : ℝ)*x 0 + (-2264665831/10000000000 : ℝ)*x 1 + (316301129/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080315707/2000000000 : ℝ)^2171 ≤ (8933082005109/20000000000000 : ℝ)^1659 := by
    have hnat : (1080315707 : ℕ)^2171*20000000000000^1659 ≤ 8933082005109^1659*2000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080315707 2000000000 8933082005109 20000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264665831/10000000000 : ℝ)^2171 ≤ (14320089321877/100000000000000 : ℝ)^1659 := by
    have hnat : (2264665831 : ℕ)^2171*100000000000000^1659 ≤ 14320089321877^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264665831 10000000000 14320089321877 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (316301129/625000000 : ℝ)^2171 ≤ (20507250316179/50000000000000 : ℝ)^1659 := by
    have hnat : (316301129 : ℕ)^2171*50000000000000^1659 ≤ 20507250316179^1659*625000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316301129 625000000 20507250316179 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080315707/2000000000 : ℝ), (-2264665831/10000000000 : ℝ), (316301129/625000000 : ℝ)] ![(8933082005109/20000000000000 : ℝ), (14320089321877/100000000000000 : ℝ), (20507250316179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080315707/2000000000 : ℝ)|^2171 ≤ (8933082005109/20000000000000 : ℝ)^1659
        have hw : |(1080315707/2000000000 : ℝ)|=(1080315707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2264665831/10000000000 : ℝ)|^2171 ≤ (14320089321877/100000000000000 : ℝ)^1659
        have hw : |(-2264665831/10000000000 : ℝ)|=(2264665831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(316301129/625000000 : ℝ)|^2171 ≤ (20507250316179/50000000000000 : ℝ)^1659
        have hw : |(316301129/625000000 : ℝ)|=(316301129/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s1_2 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5401579251/10000000000 : ℝ)*x 0 + (506081681/1000000000 : ℝ)*x 1 + (-1132333251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5401579251/10000000000 : ℝ)^2171 ≤ (44665417773321/100000000000000 : ℝ)^1659 := by
    have hnat : (5401579251 : ℕ)^2171*100000000000000^1659 ≤ 44665417773321^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401579251 10000000000 44665417773321 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506081681/1000000000 : ℝ)^2171 ≤ (10253621833273/25000000000000 : ℝ)^1659 := by
    have hnat : (506081681 : ℕ)^2171*25000000000000^1659 ≤ 10253621833273^1659*1000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506081681 1000000000 10253621833273 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132333251/5000000000 : ℝ)^2171 ≤ (3580023718559/25000000000000 : ℝ)^1659 := by
    have hnat : (1132333251 : ℕ)^2171*25000000000000^1659 ≤ 3580023718559^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132333251 5000000000 3580023718559 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5401579251/10000000000 : ℝ), (506081681/1000000000 : ℝ), (-1132333251/5000000000 : ℝ)] ![(44665417773321/100000000000000 : ℝ), (10253621833273/25000000000000 : ℝ), (3580023718559/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5401579251/10000000000 : ℝ)|^2171 ≤ (44665417773321/100000000000000 : ℝ)^1659
        have hw : |(5401579251/10000000000 : ℝ)|=(5401579251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(506081681/1000000000 : ℝ)|^2171 ≤ (10253621833273/25000000000000 : ℝ)^1659
        have hw : |(506081681/1000000000 : ℝ)|=(506081681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1132333251/5000000000 : ℝ)|^2171 ≤ (3580023718559/25000000000000 : ℝ)^1659
        have hw : |(-1132333251/5000000000 : ℝ)|=(1132333251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s1_3 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4285142387/10000000000 : ℝ)*x 0 + (1861968401/5000000000 : ℝ)*x 1 + (4922710741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4285142387/10000000000 : ℝ)^2171 ≤ (16495007143689/50000000000000 : ℝ)^1659 := by
    have hnat : (4285142387 : ℕ)^2171*50000000000000^1659 ≤ 16495007143689^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4285142387 10000000000 16495007143689 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1861968401/5000000000 : ℝ)^2171 ≤ (13726985876739/50000000000000 : ℝ)^1659 := by
    have hnat : (1861968401 : ℕ)^2171*50000000000000^1659 ≤ 13726985876739^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1861968401 5000000000 13726985876739 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4922710741/10000000000 : ℝ)^2171 ≤ (19778006973939/50000000000000 : ℝ)^1659 := by
    have hnat : (4922710741 : ℕ)^2171*50000000000000^1659 ≤ 19778006973939^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4922710741 10000000000 19778006973939 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4285142387/10000000000 : ℝ), (1861968401/5000000000 : ℝ), (4922710741/10000000000 : ℝ)] ![(16495007143689/50000000000000 : ℝ), (13726985876739/50000000000000 : ℝ), (19778006973939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4285142387/10000000000 : ℝ)|^2171 ≤ (16495007143689/50000000000000 : ℝ)^1659
        have hw : |(4285142387/10000000000 : ℝ)|=(4285142387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1861968401/5000000000 : ℝ)|^2171 ≤ (13726985876739/50000000000000 : ℝ)^1659
        have hw : |(1861968401/5000000000 : ℝ)|=(1861968401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4922710741/10000000000 : ℝ)|^2171 ≤ (19778006973939/50000000000000 : ℝ)^1659
        have hw : |(4922710741/10000000000 : ℝ)|=(4922710741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s1_4 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1965262963/10000000000 : ℝ)*x 0 + (506767631/1000000000 : ℝ)*x 1 + (5617665221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1965262963/10000000000 : ℝ)^2171 ≤ (11894779718337/100000000000000 : ℝ)^1659 := by
    have hnat : (1965262963 : ℕ)^2171*100000000000000^1659 ≤ 11894779718337^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965262963 10000000000 11894779718337 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506767631/1000000000 : ℝ)^2171 ≤ (41087250796843/100000000000000 : ℝ)^1659 := by
    have hnat : (506767631 : ℕ)^2171*100000000000000^1659 ≤ 41087250796843^1659*1000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506767631 1000000000 41087250796843 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5617665221/10000000000 : ℝ)^2171 ≤ (47017969467027/100000000000000 : ℝ)^1659 := by
    have hnat : (5617665221 : ℕ)^2171*100000000000000^1659 ≤ 47017969467027^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5617665221 10000000000 47017969467027 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1965262963/10000000000 : ℝ), (506767631/1000000000 : ℝ), (5617665221/10000000000 : ℝ)] ![(11894779718337/100000000000000 : ℝ), (41087250796843/100000000000000 : ℝ), (47017969467027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1965262963/10000000000 : ℝ)|^2171 ≤ (11894779718337/100000000000000 : ℝ)^1659
        have hw : |(-1965262963/10000000000 : ℝ)|=(1965262963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(506767631/1000000000 : ℝ)|^2171 ≤ (41087250796843/100000000000000 : ℝ)^1659
        have hw : |(506767631/1000000000 : ℝ)|=(506767631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5617665221/10000000000 : ℝ)|^2171 ≤ (47017969467027/100000000000000 : ℝ)^1659
        have hw : |(5617665221/10000000000 : ℝ)|=(5617665221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s1_5 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5254795581/10000000000 : ℝ)*x 0 + (-341563691/2000000000 : ℝ)*x 1 + (5617665299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254795581/10000000000 : ℝ)^2171 ≤ (861675725337/2000000000000 : ℝ)^1659 := by
    have hnat : (5254795581 : ℕ)^2171*2000000000000^1659 ≤ 861675725337^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254795581 10000000000 861675725337 2000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341563691/2000000000 : ℝ)^2171 ≤ (4949121697949/50000000000000 : ℝ)^1659 := by
    have hnat : (341563691 : ℕ)^2171*50000000000000^1659 ≤ 4949121697949^1659*2000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341563691 2000000000 4949121697949 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5617665299/10000000000 : ℝ)^2171 ≤ (23508985160669/50000000000000 : ℝ)^1659 := by
    have hnat : (5617665299 : ℕ)^2171*50000000000000^1659 ≤ 23508985160669^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5617665299 10000000000 23508985160669 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254795581/10000000000 : ℝ), (-341563691/2000000000 : ℝ), (5617665299/10000000000 : ℝ)] ![(861675725337/2000000000000 : ℝ), (4949121697949/50000000000000 : ℝ), (23508985160669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254795581/10000000000 : ℝ)|^2171 ≤ (861675725337/2000000000000 : ℝ)^1659
        have hw : |(5254795581/10000000000 : ℝ)|=(5254795581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-341563691/2000000000 : ℝ)|^2171 ≤ (4949121697949/50000000000000 : ℝ)^1659
        have hw : |(-341563691/2000000000 : ℝ)|=(341563691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5617665299/10000000000 : ℝ)|^2171 ≤ (23508985160669/50000000000000 : ℝ)^1659
        have hw : |(5617665299/10000000000 : ℝ)|=(5617665299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s1_6 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5254795913/10000000000 : ℝ)*x 0 + (5617665609/10000000000 : ℝ)*x 1 + (-1707817537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254795913/10000000000 : ℝ)^2171 ≤ (43083789828979/100000000000000 : ℝ)^1659 := by
    have hnat : (5254795913 : ℕ)^2171*100000000000000^1659 ≤ 43083789828979^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254795913 10000000000 43083789828979 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5617665609/10000000000 : ℝ)^2171 ≤ (47017973716677/100000000000000 : ℝ)^1659 := by
    have hnat : (5617665609 : ℕ)^2171*100000000000000^1659 ≤ 47017973716677^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5617665609 10000000000 47017973716677 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1707817537/10000000000 : ℝ)^2171 ≤ (9898236433281/100000000000000 : ℝ)^1659 := by
    have hnat : (1707817537 : ℕ)^2171*100000000000000^1659 ≤ 9898236433281^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1707817537 10000000000 9898236433281 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254795913/10000000000 : ℝ), (5617665609/10000000000 : ℝ), (-1707817537/10000000000 : ℝ)] ![(43083789828979/100000000000000 : ℝ), (47017973716677/100000000000000 : ℝ), (9898236433281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254795913/10000000000 : ℝ)|^2171 ≤ (43083789828979/100000000000000 : ℝ)^1659
        have hw : |(5254795913/10000000000 : ℝ)|=(5254795913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5617665609/10000000000 : ℝ)|^2171 ≤ (47017973716677/100000000000000 : ℝ)^1659
        have hw : |(5617665609/10000000000 : ℝ)|=(5617665609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1707817537/10000000000 : ℝ)|^2171 ≤ (9898236433281/100000000000000 : ℝ)^1659
        have hw : |(-1707817537/10000000000 : ℝ)|=(1707817537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s1_7 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4286138691/10000000000 : ℝ)*x 0 + (4908127133/10000000000 : ℝ)*x 1 + (93469383/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4286138691/10000000000 : ℝ)^2171 ≤ (16500026039063/50000000000000 : ℝ)^1659 := by
    have hnat : (4286138691 : ℕ)^2171*50000000000000^1659 ≤ 16500026039063^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4286138691 10000000000 16500026039063 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4908127133/10000000000 : ℝ)^2171 ≤ (7880546619101/20000000000000 : ℝ)^1659 := by
    have hnat : (4908127133 : ℕ)^2171*20000000000000^1659 ≤ 7880546619101^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4908127133 10000000000 7880546619101 20000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (93469383/250000000 : ℝ)^2171 ≤ (27597214801203/100000000000000 : ℝ)^1659 := by
    have hnat : (93469383 : ℕ)^2171*100000000000000^1659 ≤ 27597214801203^1659*250000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93469383 250000000 27597214801203 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4286138691/10000000000 : ℝ), (4908127133/10000000000 : ℝ), (93469383/250000000 : ℝ)] ![(16500026039063/50000000000000 : ℝ), (7880546619101/20000000000000 : ℝ), (27597214801203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4286138691/10000000000 : ℝ)|^2171 ≤ (16500026039063/50000000000000 : ℝ)^1659
        have hw : |(4286138691/10000000000 : ℝ)|=(4286138691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4908127133/10000000000 : ℝ)|^2171 ≤ (7880546619101/20000000000000 : ℝ)^1659
        have hw : |(4908127133/10000000000 : ℝ)|=(4908127133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(93469383/250000000 : ℝ)|^2171 ≤ (27597214801203/100000000000000 : ℝ)^1659
        have hw : |(93469383/250000000 : ℝ)|=(93469383/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1382_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13293/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (171/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (1813/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19169/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13293/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (171/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13293/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (171/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13293/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (171/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13293/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (171/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13293/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (171/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13293/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (171/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (171/10000 : ℝ) ^ (4341/1024 : ℝ) ≤ (3230092476819/100000000000000000000 : ℝ) := by
    have hpowers : (171/10000 : ℝ)^4341 ≤ (3230092476819/100000000000000000000 : ℝ)^1024 := by
      have hnat : (171 : ℕ)^4341*100000000000000000000^1024 ≤ 3230092476819^1024*10000^4341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        171 10000 3230092476819 100000000000000000000 4341 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (171/10000 : ℝ)) (X := (3230092476819/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13293/50000 : ℝ) ^ (4341/1024 : ℝ) ≤ (363877948136558719/100000000000000000000 : ℝ) := by
    have hpowers : (13293/50000 : ℝ)^4341 ≤ (363877948136558719/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13293 : ℕ)^4341*100000000000000000000^1024 ≤ 363877948136558719^1024*50000^4341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13293 50000 363877948136558719 100000000000000000000 4341 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13293/50000 : ℝ)) (X := (363877948136558719/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000003230092476819/50000000000000000000 : ℝ) ≤ (2500000038097381/2500000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (50000003230092476819/50000000000000000000 : ℝ)^1024 ≤ (2500000038097381/2500000000000000 : ℝ)^4341 := by
      have hnat : (50000003230092476819 : ℕ)^1024*2500000000000000^4341 ≤ 2500000038097381^4341*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000003230092476819 50000000000000000000 2500000038097381 2500000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000038097381/2500000000000000 : ℝ)) (X := (50000003230092476819/50000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50181940589114517769/50000000000000000000 : ℝ) ≤ (10008571698092181/10000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (50181940589114517769/50000000000000000000 : ℝ)^1024 ≤ (10008571698092181/10000000000000000 : ℝ)^4341 := by
      have hnat : (50181940589114517769 : ℕ)^1024*10000000000000000^4341 ≤ 10008571698092181^4341*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50181940589114517769 50000000000000000000 10008571698092181 10000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008571698092181/10000000000000000 : ℝ)) (X := (50181940589114517769/50000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50363877948136558719/50000000000000000000 : ℝ) ≤ (5008571621897419/5000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (50363877948136558719/50000000000000000000 : ℝ)^1024 ≤ (5008571621897419/5000000000000000 : ℝ)^4341 := by
      have hnat : (50363877948136558719 : ℕ)^1024*5000000000000000^4341 ≤ 5008571621897419^4341*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50363877948136558719 50000000000000000000 5008571621897419 5000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008571621897419/5000000000000000 : ℝ)) (X := (50363877948136558719/50000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3230092476819/100000000000000000000 : ℝ) ≤ ((6909185808459408669/6910000000000000000 : ℝ)+2*(8571545702657/2487600000000000 : ℝ)*(171/10000 : ℝ))^(4341/1024 : ℝ) := by
    rw [show (6909185808459408669/6910000000000000000 : ℝ)+2*(8571545702657/2487600000000000 : ℝ)*(171/10000 : ℝ)=(2500000038097381/2500000000000000 : ℝ) by norm_num, show 1+2*(3230092476819/100000000000000000000 : ℝ)=(50000003230092476819/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(363877948136558719/100000000000000000000 : ℝ)+(3230092476819/100000000000000000000 : ℝ) ≤ ((6909185808459408669/6910000000000000000 : ℝ)+(8571545702657/2487600000000000 : ℝ)*((13293/50000 : ℝ)+(171/10000 : ℝ)))^(4341/1024 : ℝ) := by
    rw [show (6909185808459408669/6910000000000000000 : ℝ)+(8571545702657/2487600000000000 : ℝ)*((13293/50000 : ℝ)+(171/10000 : ℝ))=(10008571698092181/10000000000000000 : ℝ) by norm_num, show 1+(363877948136558719/100000000000000000000 : ℝ)+(3230092476819/100000000000000000000 : ℝ)=(50181940589114517769/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(363877948136558719/100000000000000000000 : ℝ) ≤ ((6909185808459408669/6910000000000000000 : ℝ)+2*(8571545702657/2487600000000000 : ℝ)*(13293/50000 : ℝ))^(4341/1024 : ℝ) := by
    rw [show (6909185808459408669/6910000000000000000 : ℝ)+2*(8571545702657/2487600000000000 : ℝ)*(13293/50000 : ℝ)=(5008571621897419/5000000000000000 : ℝ) by norm_num, show 1+2*(363877948136558719/100000000000000000000 : ℝ)=(50363877948136558719/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6909185808459408669/6910000000000000000 : ℝ)*(X 1 0+X 2 0)+(8571545702657/2487600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (171/10000 : ℝ)) (hi := (13293/50000 : ℝ)) (c := (6909185808459408669/6910000000000000000 : ℝ)) (alpha := (8571545702657/2487600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6909185808459408669/6910000000000000000 : ℝ)*(X 0 1+X 2 1)+(8571545702657/2487600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (171/10000 : ℝ)) (hi := (13293/50000 : ℝ)) (c := (6909185808459408669/6910000000000000000 : ℝ)) (alpha := (8571545702657/2487600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6909185808459408669/6910000000000000000 : ℝ)*(X 0 2+X 1 2)+(8571545702657/2487600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (171/10000 : ℝ)) (hi := (13293/50000 : ℝ)) (c := (6909185808459408669/6910000000000000000 : ℝ)) (alpha := (8571545702657/2487600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1964795071/10000000000 : ℝ)*X 0 0+(1406161457/2500000000 : ℝ)*X 0 1+(2530408313/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1080315707/2000000000 : ℝ)*X 1 0+(-2264665831/10000000000 : ℝ)*X 1 1+(316301129/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5401579251/10000000000 : ℝ)*X 2 0+(506081681/1000000000 : ℝ)*X 2 1+(-1132333251/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4285142387/10000000000 : ℝ)*X 0 0+(1861968401/5000000000 : ℝ)*X 0 1+(4922710741/10000000000 : ℝ)*X 0 2+(4285142387/10000000000 : ℝ)*X 1 0+(1861968401/5000000000 : ℝ)*X 1 1+(4922710741/10000000000 : ℝ)*X 1 2+(4285142387/10000000000 : ℝ)*X 2 0+(1861968401/5000000000 : ℝ)*X 2 1+(4922710741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1965262963/10000000000 : ℝ)*X 0 0+(506767631/1000000000 : ℝ)*X 0 1+(5617665221/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5254795581/10000000000 : ℝ)*X 1 0+(-341563691/2000000000 : ℝ)*X 1 1+(5617665299/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5254795913/10000000000 : ℝ)*X 2 0+(5617665609/10000000000 : ℝ)*X 2 1+(-1707817537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4286138691/10000000000 : ℝ)*X 0 0+(4908127133/10000000000 : ℝ)*X 0 1+(93469383/250000000 : ℝ)*X 0 2+(4286138691/10000000000 : ℝ)*X 1 0+(4908127133/10000000000 : ℝ)*X 1 1+(93469383/250000000 : ℝ)*X 1 2+(4286138691/10000000000 : ℝ)*X 2 0+(4908127133/10000000000 : ℝ)*X 2 1+(93469383/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (208511152235640539997904431/86375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (212128953/100000000000000 : ℝ)*(base19) + (247559667/50000000000000 : ℝ)*(base23) + (2278931/5000000000000 : ℝ)*(upper2) + (92253/50000000000000 : ℝ)*(upper3) + (325973467952211/25000000000000 : ℝ)*(major0) + (325973467952211/25000000000000 : ℝ)*(major1) + (325973467952211/25000000000000 : ℝ)*(major2) + (886796455085333/50000000000000 : ℝ)*(sp0) + (886799578205919/50000000000000 : ℝ)*(sp1) + (221699691338273/12500000000000 : ℝ)*(sp2) + (417093431944681/50000000000000 : ℝ)*(sp3) + (51666961/800000000000 : ℝ)*(sp4) + (671357637/50000000000000 : ℝ)*(sp6) + (1430720129/100000000000000 : ℝ)*(sp7) + (83418829460949/10000000000000 : ℝ)*(f.failure) + (1773599368540791/100000000000000 : ℝ)*(f.sum) + (4816175970571/10365000000000000000000000000 : ℝ)*base66 + (1219582556953173523/518250000000000000000000000000000 : ℝ)*base68 + (3798336711961173523/518250000000000000000000000000000 : ℝ)*base70 + (1420101195586173523/518250000000000000000000000000000 : ℝ)*base72 + (20285238502193/5182500000000000000000000000 : ℝ)*base74 + (1013067433621923523/518250000000000000000000000000000 : ℝ)*base76 + (2067377833378173523/518250000000000000000000000000000 : ℝ)*base78 + (4136213076874173523/518250000000000000000000000000000 : ℝ)*base80 + (53440613682631/10365000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1290951/1000000000000000000000 : ℝ)*base90 + (1290951/1000000000000000000000 : ℝ)*base92 + (1290951/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38340723210548869347919429/17275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64092761/50000000000000 : ℝ)*(base1) + (774571531/100000000000000 : ℝ)*(base19) + (4827587/500000000000 : ℝ)*(base23) + (35201519/50000000000000 : ℝ)*(upper3) + (5990687/5000000000000 : ℝ)*(upper5) + (133669713677153/10000000000000 : ℝ)*(major0) + (133669713677153/10000000000000 : ℝ)*(major1) + (133669713677153/10000000000000 : ℝ)*(major2) + (94824889/2500000000000 : ℝ)*(sp1) + (6516271399/100000000000000 : ℝ)*(sp2) + (181821958612069/10000000000000 : ℝ)*(sp4) + (1818214890368077/100000000000000 : ℝ)*(sp5) + (181821197614637/10000000000000 : ℝ)*(sp6) + (855174613441229/100000000000000 : ℝ)*(sp7) + (3420698966507/400000000000 : ℝ)*(f.failure) + (1818219457935169/100000000000000 : ℝ)*(f.sum) + (10825730137301/12438000000000000000000000000 : ℝ)*base66 + (1636671730968679213/621900000000000000000000000000000 : ℝ)*base67 + (784438371123979213/621900000000000000000000000000000 : ℝ)*base69 + (1787144653072579213/621900000000000000000000000000000 : ℝ)*base71 + (3608304182873/2487600000000000000000000000 : ℝ)*base73 + (2215720466455279213/621900000000000000000000000000000 : ℝ)*base75 + (4779842988249220787/621900000000000000000000000000000 : ℝ)*base78 + (1532968276590679213/621900000000000000000000000000000 : ℝ)*base79 + (56942358121/19900800000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (35193/40000000000000000000 : ℝ)*base90 + (35193/40000000000000000000 : ℝ)*base92 + (35193/40000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1382_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13293/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (171/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1813/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19169/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1382_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1382_s2_0 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2001584949/10000000000 : ℝ)*x 0 + (5469283927/10000000000 : ℝ)*x 1 + (5192559457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2001584949/10000000000 : ℝ)^2171 ≤ (12183282738087/100000000000000 : ℝ)^1659 := by
    have hnat : (2001584949 : ℕ)^2171*100000000000000^1659 ≤ 12183282738087^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001584949 10000000000 12183282738087 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469283927/10000000000 : ℝ)^2171 ≤ (11349864357159/25000000000000 : ℝ)^1659 := by
    have hnat : (5469283927 : ℕ)^2171*25000000000000^1659 ≤ 11349864357159^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469283927 10000000000 11349864357159 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5192559457/10000000000 : ℝ)^2171 ≤ (42417259815829/100000000000000 : ℝ)^1659 := by
    have hnat : (5192559457 : ℕ)^2171*100000000000000^1659 ≤ 42417259815829^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192559457 10000000000 42417259815829 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2001584949/10000000000 : ℝ), (5469283927/10000000000 : ℝ), (5192559457/10000000000 : ℝ)] ![(12183282738087/100000000000000 : ℝ), (11349864357159/25000000000000 : ℝ), (42417259815829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2001584949/10000000000 : ℝ)|^2171 ≤ (12183282738087/100000000000000 : ℝ)^1659
        have hw : |(-2001584949/10000000000 : ℝ)|=(2001584949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469283927/10000000000 : ℝ)|^2171 ≤ (11349864357159/25000000000000 : ℝ)^1659
        have hw : |(5469283927/10000000000 : ℝ)|=(5469283927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5192559457/10000000000 : ℝ)|^2171 ≤ (42417259815829/100000000000000 : ℝ)^1659
        have hw : |(5192559457/10000000000 : ℝ)|=(5192559457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s2_1 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5363202963/10000000000 : ℝ)*x 0 + (-214427181/1000000000 : ℝ)*x 1 + (649069927/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363202963/10000000000 : ℝ)^2171 ≤ (1770024285539/4000000000000 : ℝ)^1659 := by
    have hnat : (5363202963 : ℕ)^2171*4000000000000^1659 ≤ 1770024285539^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363202963 10000000000 1770024285539 4000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (214427181/1000000000 : ℝ)^2171 ≤ (6666066736783/50000000000000 : ℝ)^1659 := by
    have hnat : (214427181 : ℕ)^2171*50000000000000^1659 ≤ 6666066736783^1659*1000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214427181 1000000000 6666066736783 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (649069927/1250000000 : ℝ)^2171 ≤ (21208629688771/50000000000000 : ℝ)^1659 := by
    have hnat : (649069927 : ℕ)^2171*50000000000000^1659 ≤ 21208629688771^1659*1250000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649069927 1250000000 21208629688771 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363202963/10000000000 : ℝ), (-214427181/1000000000 : ℝ), (649069927/1250000000 : ℝ)] ![(1770024285539/4000000000000 : ℝ), (6666066736783/50000000000000 : ℝ), (21208629688771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363202963/10000000000 : ℝ)|^2171 ≤ (1770024285539/4000000000000 : ℝ)^1659
        have hw : |(5363202963/10000000000 : ℝ)|=(5363202963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-214427181/1000000000 : ℝ)|^2171 ≤ (6666066736783/50000000000000 : ℝ)^1659
        have hw : |(-214427181/1000000000 : ℝ)|=(214427181/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(649069927/1250000000 : ℝ)|^2171 ≤ (21208629688771/50000000000000 : ℝ)^1659
        have hw : |(649069927/1250000000 : ℝ)|=(649069927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s2_2 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (134080071/250000000 : ℝ)*x 0 + (2596279767/5000000000 : ℝ)*x 1 + (-1072135909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134080071/250000000 : ℝ)^2171 ≤ (11062651452607/25000000000000 : ℝ)^1659 := by
    have hnat : (134080071 : ℕ)^2171*25000000000000^1659 ≤ 11062651452607^1659*250000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134080071 250000000 11062651452607 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2596279767/5000000000 : ℝ)^2171 ≤ (42417260638953/100000000000000 : ℝ)^1659 := by
    have hnat : (2596279767 : ℕ)^2171*100000000000000^1659 ≤ 42417260638953^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596279767 5000000000 42417260638953 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1072135909/5000000000 : ℝ)^2171 ≤ (13332133538657/100000000000000 : ℝ)^1659 := by
    have hnat : (1072135909 : ℕ)^2171*100000000000000^1659 ≤ 13332133538657^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072135909 5000000000 13332133538657 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134080071/250000000 : ℝ), (2596279767/5000000000 : ℝ), (-1072135909/5000000000 : ℝ)] ![(11062651452607/25000000000000 : ℝ), (42417260638953/100000000000000 : ℝ), (13332133538657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134080071/250000000 : ℝ)|^2171 ≤ (11062651452607/25000000000000 : ℝ)^1659
        have hw : |(134080071/250000000 : ℝ)|=(134080071/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2596279767/5000000000 : ℝ)|^2171 ≤ (42417260638953/100000000000000 : ℝ)^1659
        have hw : |(2596279767/5000000000 : ℝ)|=(2596279767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1072135909/5000000000 : ℝ)|^2171 ≤ (13332133538657/100000000000000 : ℝ)^1659
        have hw : |(-1072135909/5000000000 : ℝ)|=(1072135909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s2_3 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4310985937/10000000000 : ℝ)*x 0 + (2013001571/5000000000 : ℝ)*x 1 + (184574307/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310985937/10000000000 : ℝ)^2171 ≤ (33250621407493/100000000000000 : ℝ)^1659 := by
    have hnat : (4310985937 : ℕ)^2171*100000000000000^1659 ≤ 33250621407493^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310985937 10000000000 33250621407493 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2013001571/5000000000 : ℝ)^2171 ≤ (3800497999849/12500000000000 : ℝ)^1659 := by
    have hnat : (2013001571 : ℕ)^2171*12500000000000^1659 ≤ 3800497999849^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013001571 5000000000 3800497999849 12500000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (184574307/400000000 : ℝ)^2171 ≤ (1817269729349/5000000000000 : ℝ)^1659 := by
    have hnat : (184574307 : ℕ)^2171*5000000000000^1659 ≤ 1817269729349^1659*400000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184574307 400000000 1817269729349 5000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310985937/10000000000 : ℝ), (2013001571/5000000000 : ℝ), (184574307/400000000 : ℝ)] ![(33250621407493/100000000000000 : ℝ), (3800497999849/12500000000000 : ℝ), (1817269729349/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310985937/10000000000 : ℝ)|^2171 ≤ (33250621407493/100000000000000 : ℝ)^1659
        have hw : |(4310985937/10000000000 : ℝ)|=(4310985937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2013001571/5000000000 : ℝ)|^2171 ≤ (3800497999849/12500000000000 : ℝ)^1659
        have hw : |(2013001571/5000000000 : ℝ)|=(2013001571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(184574307/400000000 : ℝ)|^2171 ≤ (1817269729349/5000000000000 : ℝ)^1659
        have hw : |(184574307/400000000 : ℝ)|=(184574307/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s2_4 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2001640059/10000000000 : ℝ)*x 0 + (1298555379/2500000000 : ℝ)*x 1 + (5467607717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2001640059/10000000000 : ℝ)^2171 ≤ (12183721709249/100000000000000 : ℝ)^1659 := by
    have hnat : (2001640059 : ℕ)^2171*100000000000000^1659 ≤ 12183721709249^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001640059 10000000000 12183721709249 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1298555379/2500000000 : ℝ)^2171 ≤ (21217513987861/50000000000000 : ℝ)^1659 := by
    have hnat : (1298555379 : ℕ)^2171*50000000000000^1659 ≤ 21217513987861^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298555379 2500000000 21217513987861 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5467607717/10000000000 : ℝ)^2171 ≤ (22690625148817/50000000000000 : ℝ)^1659 := by
    have hnat : (5467607717 : ℕ)^2171*50000000000000^1659 ≤ 22690625148817^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467607717 10000000000 22690625148817 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2001640059/10000000000 : ℝ), (1298555379/2500000000 : ℝ), (5467607717/10000000000 : ℝ)] ![(12183721709249/100000000000000 : ℝ), (21217513987861/50000000000000 : ℝ), (22690625148817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2001640059/10000000000 : ℝ)|^2171 ≤ (12183721709249/100000000000000 : ℝ)^1659
        have hw : |(-2001640059/10000000000 : ℝ)|=(2001640059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1298555379/2500000000 : ℝ)|^2171 ≤ (21217513987861/50000000000000 : ℝ)^1659
        have hw : |(1298555379/2500000000 : ℝ)|=(1298555379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5467607717/10000000000 : ℝ)|^2171 ≤ (22690625148817/50000000000000 : ℝ)^1659
        have hw : |(5467607717/10000000000 : ℝ)|=(5467607717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s2_5 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5291576069/10000000000 : ℝ)*x 0 + (-93461207/500000000 : ℝ)*x 1 + (2733803703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291576069/10000000000 : ℝ)^2171 ≤ (679356887173/1562500000000 : ℝ)^1659 := by
    have hnat : (5291576069 : ℕ)^2171*1562500000000^1659 ≤ 679356887173^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291576069 10000000000 679356887173 1562500000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93461207/500000000 : ℝ)^2171 ≤ (2227982456367/20000000000000 : ℝ)^1659 := by
    have hnat : (93461207 : ℕ)^2171*20000000000000^1659 ≤ 2227982456367^1659*500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93461207 500000000 2227982456367 20000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733803703/5000000000 : ℝ)^2171 ≤ (22690623459843/50000000000000 : ℝ)^1659 := by
    have hnat : (2733803703 : ℕ)^2171*50000000000000^1659 ≤ 22690623459843^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733803703 5000000000 22690623459843 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291576069/10000000000 : ℝ), (-93461207/500000000 : ℝ), (2733803703/5000000000 : ℝ)] ![(679356887173/1562500000000 : ℝ), (2227982456367/20000000000000 : ℝ), (22690623459843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291576069/10000000000 : ℝ)|^2171 ≤ (679356887173/1562500000000 : ℝ)^1659
        have hw : |(5291576069/10000000000 : ℝ)|=(5291576069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-93461207/500000000 : ℝ)|^2171 ≤ (2227982456367/20000000000000 : ℝ)^1659
        have hw : |(-93461207/500000000 : ℝ)|=(93461207/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2733803703/5000000000 : ℝ)|^2171 ≤ (22690623459843/50000000000000 : ℝ)^1659
        have hw : |(2733803703/5000000000 : ℝ)|=(2733803703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s2_6 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1058315509/2000000000 : ℝ)*x 0 + (5467607473/10000000000 : ℝ)*x 1 + (-467305503/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058315509/2000000000 : ℝ)^2171 ≤ (43478856649649/100000000000000 : ℝ)^1659 := by
    have hnat : (1058315509 : ℕ)^2171*100000000000000^1659 ≤ 43478856649649^1659*2000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058315509 2000000000 43478856649649 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467607473/10000000000 : ℝ)^2171 ≤ (45381247647411/100000000000000 : ℝ)^1659 := by
    have hnat : (5467607473 : ℕ)^2171*100000000000000^1659 ≤ 45381247647411^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467607473 10000000000 45381247647411 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467305503/2500000000 : ℝ)^2171 ≤ (11139895685761/100000000000000 : ℝ)^1659 := by
    have hnat : (467305503 : ℕ)^2171*100000000000000^1659 ≤ 11139895685761^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467305503 2500000000 11139895685761 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058315509/2000000000 : ℝ), (5467607473/10000000000 : ℝ), (-467305503/2500000000 : ℝ)] ![(43478856649649/100000000000000 : ℝ), (45381247647411/100000000000000 : ℝ), (11139895685761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058315509/2000000000 : ℝ)|^2171 ≤ (43478856649649/100000000000000 : ℝ)^1659
        have hw : |(1058315509/2000000000 : ℝ)|=(1058315509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5467607473/10000000000 : ℝ)|^2171 ≤ (45381247647411/100000000000000 : ℝ)^1659
        have hw : |(5467607473/10000000000 : ℝ)|=(5467607473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-467305503/2500000000 : ℝ)|^2171 ≤ (11139895685761/100000000000000 : ℝ)^1659
        have hw : |(-467305503/2500000000 : ℝ)|=(467305503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s2_7 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4311104687/10000000000 : ℝ)*x 0 + (4610824509/10000000000 : ℝ)*x 1 + (2014783003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311104687/10000000000 : ℝ)^2171 ≤ (33251820001389/100000000000000 : ℝ)^1659 := by
    have hnat : (4311104687 : ℕ)^2171*100000000000000^1659 ≤ 33251820001389^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311104687 10000000000 33251820001389 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4610824509/10000000000 : ℝ)^2171 ≤ (36308980930781/100000000000000 : ℝ)^1659 := by
    have hnat : (4610824509 : ℕ)^2171*100000000000000^1659 ≤ 36308980930781^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4610824509 10000000000 36308980930781 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2014783003/5000000000 : ℝ)^2171 ≤ (30439199052791/100000000000000 : ℝ)^1659 := by
    have hnat : (2014783003 : ℕ)^2171*100000000000000^1659 ≤ 30439199052791^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014783003 5000000000 30439199052791 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311104687/10000000000 : ℝ), (4610824509/10000000000 : ℝ), (2014783003/5000000000 : ℝ)] ![(33251820001389/100000000000000 : ℝ), (36308980930781/100000000000000 : ℝ), (30439199052791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311104687/10000000000 : ℝ)|^2171 ≤ (33251820001389/100000000000000 : ℝ)^1659
        have hw : |(4311104687/10000000000 : ℝ)|=(4311104687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4610824509/10000000000 : ℝ)|^2171 ≤ (36308980930781/100000000000000 : ℝ)^1659
        have hw : |(4610824509/10000000000 : ℝ)|=(4610824509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2014783003/5000000000 : ℝ)|^2171 ≤ (30439199052791/100000000000000 : ℝ)^1659
        have hw : |(2014783003/5000000000 : ℝ)|=(2014783003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1382_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1813/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5051/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7977/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19169/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1813/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19169/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1813/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19169/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1813/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19169/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1813/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19169/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1813/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19169/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1813/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1813/25000 : ℝ) ^ (4341/1024 : ℝ) ≤ (1476341427322029/100000000000000000000 : ℝ) := by
    have hpowers : (1813/25000 : ℝ)^4341 ≤ (1476341427322029/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1813 : ℕ)^4341*100000000000000000000^1024 ≤ 1476341427322029^1024*25000^4341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1813 25000 1476341427322029 100000000000000000000 4341 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1813/25000 : ℝ)) (X := (1476341427322029/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19169/100000 : ℝ) ^ (4341/1024 : ℝ) ≤ (45469915734168989/50000000000000000000 : ℝ) := by
    have hpowers : (19169/100000 : ℝ)^4341 ≤ (45469915734168989/50000000000000000000 : ℝ)^1024 := by
      have hnat : (19169 : ℕ)^4341*50000000000000000000^1024 ≤ 45469915734168989^1024*100000^4341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19169 100000 45469915734168989 50000000000000000000 4341 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19169/100000 : ℝ)) (X := (45469915734168989/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001476341427322029/50000000000000000000 : ℝ) ≤ (10000069650152857/10000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (50001476341427322029/50000000000000000000 : ℝ)^1024 ≤ (10000069650152857/10000000000000000 : ℝ)^4341 := by
      have hnat : (50001476341427322029 : ℕ)^1024*10000000000000000^4341 ≤ 10000069650152857^4341*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001476341427322029 50000000000000000000 10000069650152857 10000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000069650152857/10000000000000000 : ℝ)) (X := (50001476341427322029/50000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100092416172895660007/100000000000000000000 : ℝ) ≤ (2500544809754203/2500000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (100092416172895660007/100000000000000000000 : ℝ)^1024 ≤ (2500544809754203/2500000000000000 : ℝ)^4341 := by
      have hnat : (100092416172895660007 : ℕ)^1024*2500000000000000^4341 ≤ 2500544809754203^4341*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100092416172895660007 100000000000000000000 2500544809754203 2500000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500544809754203/2500000000000000 : ℝ)) (X := (100092416172895660007/100000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25045469915734168989/25000000000000000000 : ℝ) ≤ (10004288827880767/10000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (25045469915734168989/25000000000000000000 : ℝ)^1024 ≤ (10004288827880767/10000000000000000 : ℝ)^4341 := by
      have hnat : (25045469915734168989 : ℕ)^1024*10000000000000000^4341 ≤ 10004288827880767^4341*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25045469915734168989 25000000000000000000 10004288827880767 10000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004288827880767/10000000000000000 : ℝ)) (X := (25045469915734168989/25000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1476341427322029/100000000000000000000 : ℝ) ≤ ((119140232543988793549/119170000000000000000 : ℝ)+2*(421917772791/238340000000000 : ℝ)*(1813/25000 : ℝ))^(4341/1024 : ℝ) := by
    rw [show (119140232543988793549/119170000000000000000 : ℝ)+2*(421917772791/238340000000000 : ℝ)*(1813/25000 : ℝ)=(10000069650152857/10000000000000000 : ℝ) by norm_num, show 1+2*(1476341427322029/100000000000000000000 : ℝ)=(50001476341427322029/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(45469915734168989/50000000000000000000 : ℝ)+(1476341427322029/100000000000000000000 : ℝ) ≤ ((119140232543988793549/119170000000000000000 : ℝ)+(421917772791/238340000000000 : ℝ)*((19169/100000 : ℝ)+(1813/25000 : ℝ)))^(4341/1024 : ℝ) := by
    rw [show (119140232543988793549/119170000000000000000 : ℝ)+(421917772791/238340000000000 : ℝ)*((19169/100000 : ℝ)+(1813/25000 : ℝ))=(2500544809754203/2500000000000000 : ℝ) by norm_num, show 1+(45469915734168989/50000000000000000000 : ℝ)+(1476341427322029/100000000000000000000 : ℝ)=(100092416172895660007/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(45469915734168989/50000000000000000000 : ℝ) ≤ ((119140232543988793549/119170000000000000000 : ℝ)+2*(421917772791/238340000000000 : ℝ)*(19169/100000 : ℝ))^(4341/1024 : ℝ) := by
    rw [show (119140232543988793549/119170000000000000000 : ℝ)+2*(421917772791/238340000000000 : ℝ)*(19169/100000 : ℝ)=(10004288827880767/10000000000000000 : ℝ) by norm_num, show 1+2*(45469915734168989/50000000000000000000 : ℝ)=(25045469915734168989/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (119140232543988793549/119170000000000000000 : ℝ)*(X 1 0+X 2 0)+(421917772791/238340000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (1813/25000 : ℝ)) (hi := (19169/100000 : ℝ)) (c := (119140232543988793549/119170000000000000000 : ℝ)) (alpha := (421917772791/238340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (119140232543988793549/119170000000000000000 : ℝ)*(X 0 1+X 2 1)+(421917772791/238340000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (1813/25000 : ℝ)) (hi := (19169/100000 : ℝ)) (c := (119140232543988793549/119170000000000000000 : ℝ)) (alpha := (421917772791/238340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (119140232543988793549/119170000000000000000 : ℝ)*(X 0 2+X 1 2)+(421917772791/238340000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (1813/25000 : ℝ)) (hi := (19169/100000 : ℝ)) (c := (119140232543988793549/119170000000000000000 : ℝ)) (alpha := (421917772791/238340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2001584949/10000000000 : ℝ)*X 0 0+(5469283927/10000000000 : ℝ)*X 0 1+(5192559457/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5363202963/10000000000 : ℝ)*X 1 0+(-214427181/1000000000 : ℝ)*X 1 1+(649069927/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((134080071/250000000 : ℝ)*X 2 0+(2596279767/5000000000 : ℝ)*X 2 1+(-1072135909/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4310985937/10000000000 : ℝ)*X 0 0+(2013001571/5000000000 : ℝ)*X 0 1+(184574307/400000000 : ℝ)*X 0 2+(4310985937/10000000000 : ℝ)*X 1 0+(2013001571/5000000000 : ℝ)*X 1 1+(184574307/400000000 : ℝ)*X 1 2+(4310985937/10000000000 : ℝ)*X 2 0+(2013001571/5000000000 : ℝ)*X 2 1+(184574307/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2001640059/10000000000 : ℝ)*X 0 0+(1298555379/2500000000 : ℝ)*X 0 1+(5467607717/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5291576069/10000000000 : ℝ)*X 1 0+(-93461207/500000000 : ℝ)*X 1 1+(2733803703/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058315509/2000000000 : ℝ)*X 2 0+(5467607473/10000000000 : ℝ)*X 2 1+(-467305503/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4311104687/10000000000 : ℝ)*X 0 0+(4610824509/10000000000 : ℝ)*X 0 1+(2014783003/5000000000 : ℝ)*X 0 2+(4311104687/10000000000 : ℝ)*X 1 0+(4610824509/10000000000 : ℝ)*X 1 1+(2014783003/5000000000 : ℝ)*X 1 2+(4311104687/10000000000 : ℝ)*X 2 0+(4610824509/10000000000 : ℝ)*X 2 1+(2014783003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (635325859204597857187174833/87625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1316734309/100000000000000 : ℝ)*(base19) + (1114418879/100000000000000 : ℝ)*(base23) + (16014239/25000000000000 : ℝ)*(lower2) + (54280069/25000000000000 : ℝ)*(upper3) + (98047897/100000000000000 : ℝ)*(upper5) + (664175629528737/25000000000000 : ℝ)*(major0) + (664175629528737/25000000000000 : ℝ)*(major1) + (664175629528737/25000000000000 : ℝ)*(major2) + (3613719563885389/100000000000000 : ℝ)*(sp0) + (903433207289921/25000000000000 : ℝ)*(sp1) + (1806866515737557/50000000000000 : ℝ)*(sp2) + (339932478118173/20000000000000 : ℝ)*(sp3) + (3645502151/25000000000000 : ℝ)*(sp4) + (2064515349/25000000000000 : ℝ)*(sp7) + (1699670648652261/100000000000000 : ℝ)*(f.failure) + (3613734145893993/100000000000000 : ℝ)*(f.sum) + (642098196661/175250000000000000000000000 : ℝ)*base65 + (14765010103233389/175250000000000000000000000000000 : ℝ)*base67 + (742211035820483389/175250000000000000000000000000000 : ℝ)*base69 + (373475706193766611/175250000000000000000000000000000 : ℝ)*base72 + (10532117909/2804000000000000000000000 : ℝ)*base73 + (459197409369733389/175250000000000000000000000000000 : ℝ)*base75 + (1244926486889233389/175250000000000000000000000000000 : ℝ)*base77 + (13743014124016611/175250000000000000000000000000000 : ℝ)*base80 + (565685012821/140200000000000000000000000 : ℝ)*base81 + (56446839/10000000000000000000000 : ℝ)*base90 + (56446839/10000000000000000000000 : ℝ)*base92 + (56446839/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (185633484228475325598931749/59585000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (339815479/50000000000000 : ℝ)*(base19) + (2505808783/100000000000000 : ℝ)*(base23) + (15754873/20000000000000 : ℝ)*(lower2) + (194276933/100000000000000 : ℝ)*(upper3) + (45886939/20000000000000 : ℝ)*(lower4) + (53782399137267/2000000000000 : ℝ)*(major0) + (53782399137267/2000000000000 : ℝ)*(major1) + (53782399137267/2000000000000 : ℝ)*(major2) + (19251598547/50000000000000 : ℝ)*(sp2) + (462152299/100000000000000 : ℝ)*(sp3) + (3657829553095891/100000000000000 : ℝ)*(sp4) + (914457218366233/25000000000000 : ℝ)*(sp5) + (1828894272045007/50000000000000 : ℝ)*(sp6) + (172040979463051/10000000000000 : ℝ)*(sp7) + (1720410256782809/100000000000000 : ℝ)*(f.failure) + (3657829553095891/100000000000000 : ℝ)*(f.sum) + (22418608932431/5958500000000000000000000000 : ℝ)*base65 + (1150370050971769417/238340000000000000000000000000000 : ℝ)*base68 + (1146841410111289417/238340000000000000000000000000000 : ℝ)*base70 + (216064866110349417/238340000000000000000000000000000 : ℝ)*base72 + (11451367718503/5958500000000000000000000000 : ℝ)*base74 + (232695405693410583/238340000000000000000000000000000 : ℝ)*base75 + (425749315122229417/238340000000000000000000000000000 : ℝ)*base78 + (916434112268849417/238340000000000000000000000000000 : ℝ)*base80 + (1139323530227/476680000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (104864909/10000000000000000000000 : ℝ)*base89 + (104864909/10000000000000000000000 : ℝ)*base91 + (104864909/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1382_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19169/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1813/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5051/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7977/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1382_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1382_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5051/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7977/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1382_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1382_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1382_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5051/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7977/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1382_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
