-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1070_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:10:03.657012+00:00
-- url     : https://prove2.me/submissions/23882c35-e7d1-43ab-ae99-7777daa13f78

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
theorem support_rectangle_w1070_s3_0 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1098557221/5000000000 : ℝ)*x 0 + (1359268867/2500000000 : ℝ)*x 1 + (81637531/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098557221/5000000000 : ℝ)^8263 ≤ (6667245732437/50000000000000 : ℝ)^6215 := by
    have hnat : (1098557221 : ℕ)^8263*50000000000000^6215 ≤ 6667245732437^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098557221 5000000000 6667245732437 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359268867/2500000000 : ℝ)^8263 ≤ (44479668444627/100000000000000 : ℝ)^6215 := by
    have hnat : (1359268867 : ℕ)^8263*100000000000000^6215 ≤ 44479668444627^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359268867 2500000000 44479668444627 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81637531/156250000 : ℝ)^8263 ≤ (10546460017309/25000000000000 : ℝ)^6215 := by
    have hnat : (81637531 : ℕ)^8263*25000000000000^6215 ≤ 10546460017309^6215*156250000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81637531 156250000 10546460017309 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1098557221/5000000000 : ℝ), (1359268867/2500000000 : ℝ), (81637531/156250000 : ℝ)] ![(6667245732437/50000000000000 : ℝ), (44479668444627/100000000000000 : ℝ), (10546460017309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1098557221/5000000000 : ℝ)|^8263 ≤ (6667245732437/50000000000000 : ℝ)^6215
        have hw : |(-1098557221/5000000000 : ℝ)|=(1098557221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359268867/2500000000 : ℝ)|^8263 ≤ (44479668444627/100000000000000 : ℝ)^6215
        have hw : |(1359268867/2500000000 : ℝ)|=(1359268867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81637531/156250000 : ℝ)|^8263 ≤ (10546460017309/25000000000000 : ℝ)^6215
        have hw : |(81637531/156250000 : ℝ)|=(81637531/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s3_1 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334724341/625000000 : ℝ)*x 0 + (-2305804657/10000000000 : ℝ)*x 1 + (1306200507/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334724341/625000000 : ℝ)^8263 ≤ (21797787160793/50000000000000 : ℝ)^6215 := by
    have hnat : (334724341 : ℕ)^8263*50000000000000^6215 ≤ 21797787160793^6215*625000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334724341 625000000 21797787160793 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2305804657/10000000000 : ℝ)^8263 ≤ (14218585124617/100000000000000 : ℝ)^6215 := by
    have hnat : (2305804657 : ℕ)^8263*100000000000000^6215 ≤ 14218585124617^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2305804657 10000000000 14218585124617 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306200507/2500000000 : ℝ)^8263 ≤ (42185840541567/100000000000000 : ℝ)^6215 := by
    have hnat : (1306200507 : ℕ)^8263*100000000000000^6215 ≤ 42185840541567^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306200507 2500000000 42185840541567 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334724341/625000000 : ℝ), (-2305804657/10000000000 : ℝ), (1306200507/2500000000 : ℝ)] ![(21797787160793/50000000000000 : ℝ), (14218585124617/100000000000000 : ℝ), (42185840541567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334724341/625000000 : ℝ)|^8263 ≤ (21797787160793/50000000000000 : ℝ)^6215
        have hw : |(334724341/625000000 : ℝ)|=(334724341/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2305804657/10000000000 : ℝ)|^8263 ≤ (14218585124617/100000000000000 : ℝ)^6215
        have hw : |(-2305804657/10000000000 : ℝ)|=(2305804657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1306200507/2500000000 : ℝ)|^8263 ≤ (42185840541567/100000000000000 : ℝ)^6215
        have hw : |(1306200507/2500000000 : ℝ)|=(1306200507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s3_2 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338897357/2500000000 : ℝ)*x 0 + (326550139/625000000 : ℝ)*x 1 + (-2305804437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338897357/2500000000 : ℝ)^8263 ≤ (43595574018553/100000000000000 : ℝ)^6215 := by
    have hnat : (1338897357 : ℕ)^8263*100000000000000^6215 ≤ 43595574018553^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338897357 2500000000 43595574018553 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326550139/625000000 : ℝ)^8263 ≤ (8437168529117/20000000000000 : ℝ)^6215 := by
    have hnat : (326550139 : ℕ)^8263*20000000000000^6215 ≤ 8437168529117^6215*625000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326550139 625000000 8437168529117 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2305804437/10000000000 : ℝ)^8263 ≤ (14218583320963/100000000000000 : ℝ)^6215 := by
    have hnat : (2305804437 : ℕ)^8263*100000000000000^6215 ≤ 14218583320963^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2305804437 10000000000 14218583320963 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338897357/2500000000 : ℝ), (326550139/625000000 : ℝ), (-2305804437/10000000000 : ℝ)] ![(43595574018553/100000000000000 : ℝ), (8437168529117/20000000000000 : ℝ), (14218583320963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338897357/2500000000 : ℝ)|^8263 ≤ (43595574018553/100000000000000 : ℝ)^6215
        have hw : |(1338897357/2500000000 : ℝ)|=(1338897357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326550139/625000000 : ℝ)|^8263 ≤ (8437168529117/20000000000000 : ℝ)^6215
        have hw : |(326550139/625000000 : ℝ)|=(326550139/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2305804437/10000000000 : ℝ)|^8263 ≤ (14218583320963/100000000000000 : ℝ)^6215
        have hw : |(-2305804437/10000000000 : ℝ)|=(2305804437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s3_3 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (546518213/1250000000 : ℝ)*x 0 + (4168975893/10000000000 : ℝ)*x 1 + (4585332081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546518213/1250000000 : ℝ)^8263 ≤ (33288513380029/100000000000000 : ℝ)^6215 := by
    have hnat : (546518213 : ℕ)^8263*100000000000000^6215 ≤ 33288513380029^6215*1250000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546518213 1250000000 33288513380029 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4168975893/10000000000 : ℝ)^8263 ≤ (31247799306059/100000000000000 : ℝ)^6215 := by
    have hnat : (4168975893 : ℕ)^8263*100000000000000^6215 ≤ 31247799306059^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168975893 10000000000 31247799306059 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4585332081/10000000000 : ℝ)^8263 ≤ (35463687294911/100000000000000 : ℝ)^6215 := by
    have hnat : (4585332081 : ℕ)^8263*100000000000000^6215 ≤ 35463687294911^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4585332081 10000000000 35463687294911 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546518213/1250000000 : ℝ), (4168975893/10000000000 : ℝ), (4585332081/10000000000 : ℝ)] ![(33288513380029/100000000000000 : ℝ), (31247799306059/100000000000000 : ℝ), (35463687294911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546518213/1250000000 : ℝ)|^8263 ≤ (33288513380029/100000000000000 : ℝ)^6215
        have hw : |(546518213/1250000000 : ℝ)|=(546518213/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4168975893/10000000000 : ℝ)|^8263 ≤ (31247799306059/100000000000000 : ℝ)^6215
        have hw : |(4168975893/10000000000 : ℝ)|=(4168975893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4585332081/10000000000 : ℝ)|^8263 ≤ (35463687294911/100000000000000 : ℝ)^6215
        have hw : |(4585332081/10000000000 : ℝ)|=(4585332081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s3_4 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-439427351/2000000000 : ℝ)*x 0 + (2612834933/5000000000 : ℝ)*x 1 + (2718101151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (439427351/2000000000 : ℝ)^8263 ≤ (2666934301811/20000000000000 : ℝ)^6215 := by
    have hnat : (439427351 : ℕ)^8263*20000000000000^6215 ≤ 2666934301811^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439427351 2000000000 2666934301811 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2612834933/5000000000 : ℝ)^8263 ≤ (5274394606723/12500000000000 : ℝ)^6215 := by
    have hnat : (2612834933 : ℕ)^8263*12500000000000^6215 ≤ 5274394606723^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612834933 5000000000 5274394606723 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718101151/5000000000 : ℝ)^8263 ≤ (5558771453303/12500000000000 : ℝ)^6215 := by
    have hnat : (2718101151 : ℕ)^8263*12500000000000^6215 ≤ 5558771453303^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718101151 5000000000 5558771453303 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-439427351/2000000000 : ℝ), (2612834933/5000000000 : ℝ), (2718101151/5000000000 : ℝ)] ![(2666934301811/20000000000000 : ℝ), (5274394606723/12500000000000 : ℝ), (5558771453303/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-439427351/2000000000 : ℝ)|^8263 ≤ (2666934301811/20000000000000 : ℝ)^6215
        have hw : |(-439427351/2000000000 : ℝ)|=(439427351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2612834933/5000000000 : ℝ)|^8263 ≤ (5274394606723/12500000000000 : ℝ)^6215
        have hw : |(2612834933/5000000000 : ℝ)|=(2612834933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718101151/5000000000 : ℝ)|^8263 ≤ (5558771453303/12500000000000 : ℝ)^6215
        have hw : |(2718101151/5000000000 : ℝ)|=(2718101151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s3_5 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5302101961/10000000000 : ℝ)*x 0 + (-2094403457/10000000000 : ℝ)*x 1 + (2718101451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302101961/10000000000 : ℝ)^8263 ≤ (21508827529733/50000000000000 : ℝ)^6215 := by
    have hnat : (5302101961 : ℕ)^8263*50000000000000^6215 ≤ 21508827529733^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302101961 10000000000 21508827529733 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2094403457/10000000000 : ℝ)^8263 ≤ (12512166773979/100000000000000 : ℝ)^6215 := by
    have hnat : (2094403457 : ℕ)^8263*100000000000000^6215 ≤ 12512166773979^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094403457 10000000000 12512166773979 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718101451/5000000000 : ℝ)^8263 ≤ (44470178152033/100000000000000 : ℝ)^6215 := by
    have hnat : (2718101451 : ℕ)^8263*100000000000000^6215 ≤ 44470178152033^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718101451 5000000000 44470178152033 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302101961/10000000000 : ℝ), (-2094403457/10000000000 : ℝ), (2718101451/5000000000 : ℝ)] ![(21508827529733/50000000000000 : ℝ), (12512166773979/100000000000000 : ℝ), (44470178152033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302101961/10000000000 : ℝ)|^8263 ≤ (21508827529733/50000000000000 : ℝ)^6215
        have hw : |(5302101961/10000000000 : ℝ)|=(5302101961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2094403457/10000000000 : ℝ)|^8263 ≤ (12512166773979/100000000000000 : ℝ)^6215
        have hw : |(-2094403457/10000000000 : ℝ)|=(2094403457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718101451/5000000000 : ℝ)|^8263 ≤ (44470178152033/100000000000000 : ℝ)^6215
        have hw : |(2718101451/5000000000 : ℝ)|=(2718101451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s3_6 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5302101483/10000000000 : ℝ)*x 0 + (5436202849/10000000000 : ℝ)*x 1 + (-1047202089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302101483/10000000000 : ℝ)^8263 ≤ (2688603118959/6250000000000 : ℝ)^6215 := by
    have hnat : (5302101483 : ℕ)^8263*6250000000000^6215 ≤ 2688603118959^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302101483 10000000000 2688603118959 6250000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436202849/10000000000 : ℝ)^8263 ≤ (8894035515121/20000000000000 : ℝ)^6215 := by
    have hnat : (5436202849 : ℕ)^8263*20000000000000^6215 ≤ 8894035515121^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436202849 10000000000 8894035515121 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047202089/5000000000 : ℝ)^8263 ≤ (500486900027/4000000000000 : ℝ)^6215 := by
    have hnat : (1047202089 : ℕ)^8263*4000000000000^6215 ≤ 500486900027^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047202089 5000000000 500486900027 4000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302101483/10000000000 : ℝ), (5436202849/10000000000 : ℝ), (-1047202089/5000000000 : ℝ)] ![(2688603118959/6250000000000 : ℝ), (8894035515121/20000000000000 : ℝ), (500486900027/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302101483/10000000000 : ℝ)|^8263 ≤ (2688603118959/6250000000000 : ℝ)^6215
        have hw : |(5302101483/10000000000 : ℝ)|=(5302101483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436202849/10000000000 : ℝ)|^8263 ≤ (8894035515121/20000000000000 : ℝ)^6215
        have hw : |(5436202849/10000000000 : ℝ)|=(5436202849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1047202089/5000000000 : ℝ)|^8263 ≤ (500486900027/4000000000000 : ℝ)^6215
        have hw : |(-1047202089/5000000000 : ℝ)|=(1047202089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s3_7 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (218609439/500000000 : ℝ)*x 0 + (458363097/1000000000 : ℝ)*x 1 + (4170687231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218609439/500000000 : ℝ)^8263 ≤ (3328894942619/10000000000000 : ℝ)^6215 := by
    have hnat : (218609439 : ℕ)^8263*10000000000000^6215 ≤ 3328894942619^6215*500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218609439 500000000 3328894942619 10000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458363097/1000000000 : ℝ)^8263 ≤ (7089239249489/20000000000000 : ℝ)^6215 := by
    have hnat : (458363097 : ℕ)^8263*20000000000000^6215 ≤ 7089239249489^6215*1000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458363097 1000000000 7089239249489 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170687231/10000000000 : ℝ)^8263 ≤ (15632427155231/50000000000000 : ℝ)^6215 := by
    have hnat : (4170687231 : ℕ)^8263*50000000000000^6215 ≤ 15632427155231^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170687231 10000000000 15632427155231 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218609439/500000000 : ℝ), (458363097/1000000000 : ℝ), (4170687231/10000000000 : ℝ)] ![(3328894942619/10000000000000 : ℝ), (7089239249489/20000000000000 : ℝ), (15632427155231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218609439/500000000 : ℝ)|^8263 ≤ (3328894942619/10000000000000 : ℝ)^6215
        have hw : |(218609439/500000000 : ℝ)|=(218609439/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(458363097/1000000000 : ℝ)|^8263 ≤ (7089239249489/20000000000000 : ℝ)^6215
        have hw : |(458363097/1000000000 : ℝ)|=(458363097/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170687231/10000000000 : ℝ)|^8263 ≤ (15632427155231/50000000000000 : ℝ)^6215
        have hw : |(4170687231/10000000000 : ℝ)|=(4170687231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1070_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2091/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8731/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10409/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (149/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2091/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8731/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2091/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8731/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2091/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8731/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2091/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8731/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2091/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8731/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2091/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8731/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8731/100000 : ℝ) ^ (4131/1024 : ℝ) ≤ (2673202479336901/50000000000000000000 : ℝ) := by
    have hpowers : (8731/100000 : ℝ)^4131 ≤ (2673202479336901/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8731 : ℕ)^4131*50000000000000000000^1024 ≤ 2673202479336901^1024*100000^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8731 100000 2673202479336901 50000000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8731/100000 : ℝ)) (X := (2673202479336901/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2091/12500 : ℝ) ^ (4131/1024 : ℝ) ≤ (73660326325691427/100000000000000000000 : ℝ) := by
    have hpowers : (2091/12500 : ℝ)^4131 ≤ (73660326325691427/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2091 : ℕ)^4131*100000000000000000000^1024 ≤ 73660326325691427^1024*12500^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2091 12500 73660326325691427 100000000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2091/12500 : ℝ)) (X := (73660326325691427/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002673202479336901/25000000000000000000 : ℝ) ≤ (200005300894259/200000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (25002673202479336901/25000000000000000000 : ℝ)^1024 ≤ (200005300894259/200000000000000 : ℝ)^4131 := by
      have hnat : (25002673202479336901 : ℕ)^1024*200000000000000^4131 ≤ 200005300894259^4131*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002673202479336901 25000000000000000000 200005300894259 200000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200005300894259/200000000000000 : ℝ)) (X := (25002673202479336901/25000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100079006731284365229/100000000000000000000 : ℝ) ≤ (5000978926007049/5000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (100079006731284365229/100000000000000000000 : ℝ)^1024 ≤ (5000978926007049/5000000000000000 : ℝ)^4131 := by
      have hnat : (100079006731284365229 : ℕ)^1024*5000000000000000^4131 ≤ 5000978926007049^4131*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100079006731284365229 100000000000000000000 5000978926007049 5000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000978926007049/5000000000000000 : ℝ)) (X := (100079006731284365229/100000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50073660326325691427/50000000000000000000 : ℝ) ≤ (5001825329657623/5000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (50073660326325691427/50000000000000000000 : ℝ)^1024 ≤ (5001825329657623/5000000000000000 : ℝ)^4131 := by
      have hnat : (50073660326325691427 : ℕ)^1024*5000000000000000^4131 ≤ 5001825329657623^4131*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50073660326325691427 50000000000000000000 5001825329657623 5000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001825329657623/5000000000000000 : ℝ)) (X := (50073660326325691427/50000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2673202479336901/50000000000000000000 : ℝ) ≤ ((39971279880738407387/39985000000000000000 : ℝ)+2*(423201825287/199925000000000 : ℝ)*(8731/100000 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (39971279880738407387/39985000000000000000 : ℝ)+2*(423201825287/199925000000000 : ℝ)*(8731/100000 : ℝ)=(200005300894259/200000000000000 : ℝ) by norm_num, show 1+2*(2673202479336901/50000000000000000000 : ℝ)=(25002673202479336901/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(73660326325691427/100000000000000000000 : ℝ)+(2673202479336901/50000000000000000000 : ℝ) ≤ ((39971279880738407387/39985000000000000000 : ℝ)+(423201825287/199925000000000 : ℝ)*((2091/12500 : ℝ)+(8731/100000 : ℝ)))^(4131/1024 : ℝ) := by
    rw [show (39971279880738407387/39985000000000000000 : ℝ)+(423201825287/199925000000000 : ℝ)*((2091/12500 : ℝ)+(8731/100000 : ℝ))=(5000978926007049/5000000000000000 : ℝ) by norm_num, show 1+(73660326325691427/100000000000000000000 : ℝ)+(2673202479336901/50000000000000000000 : ℝ)=(100079006731284365229/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(73660326325691427/100000000000000000000 : ℝ) ≤ ((39971279880738407387/39985000000000000000 : ℝ)+2*(423201825287/199925000000000 : ℝ)*(2091/12500 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (39971279880738407387/39985000000000000000 : ℝ)+2*(423201825287/199925000000000 : ℝ)*(2091/12500 : ℝ)=(5001825329657623/5000000000000000 : ℝ) by norm_num, show 1+2*(73660326325691427/100000000000000000000 : ℝ)=(50073660326325691427/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39971279880738407387/39985000000000000000 : ℝ)*(X 1 0+X 2 0)+(423201825287/199925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (8731/100000 : ℝ)) (hi := (2091/12500 : ℝ)) (c := (39971279880738407387/39985000000000000000 : ℝ)) (alpha := (423201825287/199925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39971279880738407387/39985000000000000000 : ℝ)*(X 0 1+X 2 1)+(423201825287/199925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (8731/100000 : ℝ)) (hi := (2091/12500 : ℝ)) (c := (39971279880738407387/39985000000000000000 : ℝ)) (alpha := (423201825287/199925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39971279880738407387/39985000000000000000 : ℝ)*(X 0 2+X 1 2)+(423201825287/199925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (8731/100000 : ℝ)) (hi := (2091/12500 : ℝ)) (c := (39971279880738407387/39985000000000000000 : ℝ)) (alpha := (423201825287/199925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1098557221/5000000000 : ℝ)*X 0 0+(1359268867/2500000000 : ℝ)*X 0 1+(81637531/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334724341/625000000 : ℝ)*X 1 0+(-2305804657/10000000000 : ℝ)*X 1 1+(1306200507/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338897357/2500000000 : ℝ)*X 2 0+(326550139/625000000 : ℝ)*X 2 1+(-2305804437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((546518213/1250000000 : ℝ)*X 0 0+(4168975893/10000000000 : ℝ)*X 0 1+(4585332081/10000000000 : ℝ)*X 0 2+(546518213/1250000000 : ℝ)*X 1 0+(4168975893/10000000000 : ℝ)*X 1 1+(4585332081/10000000000 : ℝ)*X 1 2+(546518213/1250000000 : ℝ)*X 2 0+(4168975893/10000000000 : ℝ)*X 2 1+(4585332081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-439427351/2000000000 : ℝ)*X 0 0+(2612834933/5000000000 : ℝ)*X 0 1+(2718101151/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302101961/10000000000 : ℝ)*X 1 0+(-2094403457/10000000000 : ℝ)*X 1 1+(2718101451/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302101483/10000000000 : ℝ)*X 2 0+(5436202849/10000000000 : ℝ)*X 2 1+(-1047202089/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((218609439/500000000 : ℝ)*X 0 0+(458363097/1000000000 : ℝ)*X 0 1+(4170687231/10000000000 : ℝ)*X 0 2+(218609439/500000000 : ℝ)*X 1 0+(458363097/1000000000 : ℝ)*X 1 1+(4170687231/10000000000 : ℝ)*X 1 2+(218609439/500000000 : ℝ)*X 2 0+(458363097/1000000000 : ℝ)*X 2 1+(4170687231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2569433926960446511294225869/399850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1588542007/100000000000000 : ℝ)*(base19) + (1310196213/100000000000000 : ℝ)*(base23) + (8492493/6250000000000 : ℝ)*(lower2) + (64606167/50000000000000 : ℝ)*(upper3) + (142113357/100000000000000 : ℝ)*(upper5) + (222274338172003/6250000000000 : ℝ)*(major0) + (222274338172003/6250000000000 : ℝ)*(major1) + (3556389410752049/100000000000000 : ℝ)*(major2) + (471093195632161/10000000000000 : ℝ)*(sp0) + (94219222374683/2000000000000 : ℝ)*(sp1) + (588870174634993/12500000000000 : ℝ)*(sp2) + (60045060529621/2500000000000 : ℝ)*(sp3) + (30750954547/100000000000000 : ℝ)*(sp4) + (13478843273/100000000000000 : ℝ)*(sp7) + (150113493751757/6250000000000 : ℝ)*(f.failure) + (4710962707276157/100000000000000 : ℝ)*(f.sum) + (6864428167103/39985000000000000000000000000 : ℝ)*base65 + (1735747659953176339/249906250000000000000000000000000 : ℝ)*base68 + (13943425289432314037/3998500000000000000000000000000000 : ℝ)*base70 + (660065089241801339/249906250000000000000000000000000 : ℝ)*base72 + (2795399278689/19992500000000000000000000000 : ℝ)*base73 + (91290468331283314037/3998500000000000000000000000000000 : ℝ)*base76 + (752849697279888839/249906250000000000000000000000000 : ℝ)*base78 + (1309737299587326339/249906250000000000000000000000000 : ℝ)*base80 + (42205879935271/39985000000000000000000000000 : ℝ)*base82 + (1001247/312500000000000000000 : ℝ)*base90 + (1001247/312500000000000000000 : ℝ)*base92 + (4126247/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (715815729321050374786912413/199925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1255104613/100000000000000 : ℝ)*(base19) + (25141441/3125000000000 : ℝ)*(base23) + (25550627/50000000000000 : ℝ)*(upper2) + (214363481/100000000000000 : ℝ)*(upper3) + (358574670870133/10000000000000 : ℝ)*(major0) + (358574670870133/10000000000000 : ℝ)*(major1) + (3585746708701331/100000000000000 : ℝ)*(major2) + (15218287401/50000000000000 : ℝ)*(sp1) + (9332745837/50000000000000 : ℝ)*(sp2) + (1092257439/50000000000000 : ℝ)*(sp3) + (949970175649501/20000000000000 : ℝ)*(sp4) + (474981918656809/10000000000000 : ℝ)*(sp5) + (4749831408229719/100000000000000 : ℝ)*(sp6) + (1210820117646447/50000000000000 : ℝ)*(sp7) + (2421642419807773/100000000000000 : ℝ)*(f.failure) + (949970175649501/20000000000000 : ℝ)*(f.sum) + (150272337995231/39985000000000000000000000000 : ℝ)*base66 + (1938667656400587529/399850000000000000000000000000000 : ℝ)*base68 + (178066190457867903/3998500000000000000000000000000000 : ℝ)*base70 + (1229524912690087529/399850000000000000000000000000000 : ℝ)*base72 + (881484782829/2499062500000000000000000000 : ℝ)*base73 + (28870480014231132097/3998500000000000000000000000000000 : ℝ)*base75 + (4442980045463777529/399850000000000000000000000000000 : ℝ)*base78 + (2421322291505222471/399850000000000000000000000000000 : ℝ)*base79 + (1017085683963/999625000000000000000000000 : ℝ)*base81 + (71589617/5000000000000000000000 : ℝ)*base89 + (71589617/5000000000000000000000 : ℝ)*base91 + (21589617/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1070_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2091/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8731/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10409/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (149/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1070_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1070_s4_0 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1100377829/5000000000 : ℝ)*x 0 + (2702797041/5000000000 : ℝ)*x 1 + (2626952173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100377829/5000000000 : ℝ)^8263 ≤ (1670485062839/12500000000000 : ℝ)^6215 := by
    have hnat : (1100377829 : ℕ)^8263*12500000000000^6215 ≤ 1670485062839^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100377829 5000000000 1670485062839 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702797041/5000000000 : ℝ)^8263 ≤ (11034396341377/25000000000000 : ℝ)^6215 := by
    have hnat : (2702797041 : ℕ)^8263*25000000000000^6215 ≤ 11034396341377^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702797041 5000000000 11034396341377 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626952173/5000000000 : ℝ)^8263 ≤ (332019797789/781250000000 : ℝ)^6215 := by
    have hnat : (2626952173 : ℕ)^8263*781250000000^6215 ≤ 332019797789^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626952173 5000000000 332019797789 781250000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1100377829/5000000000 : ℝ), (2702797041/5000000000 : ℝ), (2626952173/5000000000 : ℝ)] ![(1670485062839/12500000000000 : ℝ), (11034396341377/25000000000000 : ℝ), (332019797789/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1100377829/5000000000 : ℝ)|^8263 ≤ (1670485062839/12500000000000 : ℝ)^6215
        have hw : |(-1100377829/5000000000 : ℝ)|=(1100377829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702797041/5000000000 : ℝ)|^8263 ≤ (11034396341377/25000000000000 : ℝ)^6215
        have hw : |(2702797041/5000000000 : ℝ)|=(2702797041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626952173/5000000000 : ℝ)|^8263 ≤ (332019797789/781250000000 : ℝ)^6215
        have hw : |(2626952173/5000000000 : ℝ)|=(2626952173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s4_1 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673893407/5000000000 : ℝ)*x 0 + (-569476233/2500000000 : ℝ)*x 1 + (164184533/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673893407/5000000000 : ℝ)^8263 ≤ (21755574849331/50000000000000 : ℝ)^6215 := by
    have hnat : (2673893407 : ℕ)^8263*50000000000000^6215 ≤ 21755574849331^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673893407 5000000000 21755574849331 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569476233/2500000000 : ℝ)^8263 ≤ (1748788566281/12500000000000 : ℝ)^6215 := by
    have hnat : (569476233 : ℕ)^8263*12500000000000^6215 ≤ 1748788566281^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569476233 2500000000 1748788566281 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164184533/312500000 : ℝ)^8263 ≤ (8499708350531/20000000000000 : ℝ)^6215 := by
    have hnat : (164184533 : ℕ)^8263*20000000000000^6215 ≤ 8499708350531^6215*312500000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164184533 312500000 8499708350531 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673893407/5000000000 : ℝ), (-569476233/2500000000 : ℝ), (164184533/312500000 : ℝ)] ![(21755574849331/50000000000000 : ℝ), (1748788566281/12500000000000 : ℝ), (8499708350531/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673893407/5000000000 : ℝ)|^8263 ≤ (21755574849331/50000000000000 : ℝ)^6215
        have hw : |(2673893407/5000000000 : ℝ)|=(2673893407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-569476233/2500000000 : ℝ)|^8263 ≤ (1748788566281/12500000000000 : ℝ)^6215
        have hw : |(-569476233/2500000000 : ℝ)|=(569476233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164184533/312500000 : ℝ)|^8263 ≤ (8499708350531/20000000000000 : ℝ)^6215
        have hw : |(164184533/312500000 : ℝ)|=(164184533/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s4_2 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673893391/5000000000 : ℝ)*x 0 + (1050781033/2000000000 : ℝ)*x 1 + (-35592263/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673893391/5000000000 : ℝ)^8263 ≤ (8702229870501/20000000000000 : ℝ)^6215 := by
    have hnat : (2673893391 : ℕ)^8263*20000000000000^6215 ≤ 8702229870501^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673893391 5000000000 8702229870501 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050781033/2000000000 : ℝ)^8263 ≤ (4249854292489/10000000000000 : ℝ)^6215 := by
    have hnat : (1050781033 : ℕ)^8263*10000000000000^6215 ≤ 4249854292489^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050781033 2000000000 4249854292489 10000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35592263/156250000 : ℝ)^8263 ≤ (1748788464211/12500000000000 : ℝ)^6215 := by
    have hnat : (35592263 : ℕ)^8263*12500000000000^6215 ≤ 1748788464211^6215*156250000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35592263 156250000 1748788464211 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673893391/5000000000 : ℝ), (1050781033/2000000000 : ℝ), (-35592263/156250000 : ℝ)] ![(8702229870501/20000000000000 : ℝ), (4249854292489/10000000000000 : ℝ), (1748788464211/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673893391/5000000000 : ℝ)|^8263 ≤ (8702229870501/20000000000000 : ℝ)^6215
        have hw : |(2673893391/5000000000 : ℝ)|=(2673893391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1050781033/2000000000 : ℝ)|^8263 ≤ (4249854292489/10000000000000 : ℝ)^6215
        have hw : |(1050781033/2000000000 : ℝ)|=(1050781033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35592263/156250000 : ℝ)|^8263 ≤ (1748788464211/12500000000000 : ℝ)^6215
        have hw : |(-35592263/156250000 : ℝ)|=(35592263/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s4_3 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187155441/5000000000 : ℝ)*x 0 + (1057026867/2500000000 : ℝ)*x 1 + (565704123/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187155441/5000000000 : ℝ)^8263 ≤ (33310432616897/100000000000000 : ℝ)^6215 := by
    have hnat : (2187155441 : ℕ)^8263*100000000000000^6215 ≤ 33310432616897^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187155441 5000000000 33310432616897 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057026867/2500000000 : ℝ)^8263 ≤ (3183843089079/10000000000000 : ℝ)^6215 := by
    have hnat : (1057026867 : ℕ)^8263*10000000000000^6215 ≤ 3183843089079^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057026867 2500000000 3183843089079 10000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565704123/1250000000 : ℝ)^8263 ≤ (34851136480001/100000000000000 : ℝ)^6215 := by
    have hnat : (565704123 : ℕ)^8263*100000000000000^6215 ≤ 34851136480001^6215*1250000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565704123 1250000000 34851136480001 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187155441/5000000000 : ℝ), (1057026867/2500000000 : ℝ), (565704123/1250000000 : ℝ)] ![(33310432616897/100000000000000 : ℝ), (3183843089079/10000000000000 : ℝ), (34851136480001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187155441/5000000000 : ℝ)|^8263 ≤ (33310432616897/100000000000000 : ℝ)^6215
        have hw : |(2187155441/5000000000 : ℝ)|=(2187155441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1057026867/2500000000 : ℝ)|^8263 ≤ (3183843089079/10000000000000 : ℝ)^6215
        have hw : |(1057026867/2500000000 : ℝ)|=(1057026867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(565704123/1250000000 : ℝ)|^8263 ≤ (34851136480001/100000000000000 : ℝ)^6215
        have hw : |(565704123/1250000000 : ℝ)|=(565704123/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s4_4 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-440152633/2000000000 : ℝ)*x 0 + (1313587161/2500000000 : ℝ)*x 1 + (5405148337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (440152633/2000000000 : ℝ)^8263 ≤ (6681970554943/50000000000000 : ℝ)^6215 := by
    have hnat : (440152633 : ℕ)^8263*50000000000000^6215 ≤ 6681970554943^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440152633 2000000000 6681970554943 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313587161/2500000000 : ℝ)^8263 ≤ (21251656183217/50000000000000 : ℝ)^6215 := by
    have hnat : (1313587161 : ℕ)^8263*50000000000000^6215 ≤ 21251656183217^6215*2500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313587161 2500000000 21251656183217 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405148337/10000000000 : ℝ)^8263 ≤ (22066373256751/50000000000000 : ℝ)^6215 := by
    have hnat : (5405148337 : ℕ)^8263*50000000000000^6215 ≤ 22066373256751^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405148337 10000000000 22066373256751 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-440152633/2000000000 : ℝ), (1313587161/2500000000 : ℝ), (5405148337/10000000000 : ℝ)] ![(6681970554943/50000000000000 : ℝ), (21251656183217/50000000000000 : ℝ), (22066373256751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-440152633/2000000000 : ℝ)|^8263 ≤ (6681970554943/50000000000000 : ℝ)^6215
        have hw : |(-440152633/2000000000 : ℝ)|=(440152633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313587161/2500000000 : ℝ)|^8263 ≤ (21251656183217/50000000000000 : ℝ)^6215
        have hw : |(1313587161/2500000000 : ℝ)|=(1313587161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405148337/10000000000 : ℝ)|^8263 ≤ (22066373256751/50000000000000 : ℝ)^6215
        have hw : |(5405148337/10000000000 : ℝ)|=(5405148337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s4_5 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2654785003/5000000000 : ℝ)*x 0 + (-1063330389/5000000000 : ℝ)*x 1 + (5405148117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654785003/5000000000 : ℝ)^8263 ≤ (8619646109577/20000000000000 : ℝ)^6215 := by
    have hnat : (2654785003 : ℕ)^8263*20000000000000^6215 ≤ 8619646109577^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654785003 5000000000 8619646109577 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1063330389/5000000000 : ℝ)^8263 ≤ (6384512658053/50000000000000 : ℝ)^6215 := by
    have hnat : (1063330389 : ℕ)^8263*50000000000000^6215 ≤ 6384512658053^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063330389 5000000000 6384512658053 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405148117/10000000000 : ℝ)^8263 ≤ (11033186031323/25000000000000 : ℝ)^6215 := by
    have hnat : (5405148117 : ℕ)^8263*25000000000000^6215 ≤ 11033186031323^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405148117 10000000000 11033186031323 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654785003/5000000000 : ℝ), (-1063330389/5000000000 : ℝ), (5405148117/10000000000 : ℝ)] ![(8619646109577/20000000000000 : ℝ), (6384512658053/50000000000000 : ℝ), (11033186031323/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654785003/5000000000 : ℝ)|^8263 ≤ (8619646109577/20000000000000 : ℝ)^6215
        have hw : |(2654785003/5000000000 : ℝ)|=(2654785003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1063330389/5000000000 : ℝ)|^8263 ≤ (6384512658053/50000000000000 : ℝ)^6215
        have hw : |(-1063330389/5000000000 : ℝ)|=(1063330389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405148117/10000000000 : ℝ)|^8263 ≤ (11033186031323/25000000000000 : ℝ)^6215
        have hw : |(5405148117/10000000000 : ℝ)|=(5405148117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s4_6 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2654784897/5000000000 : ℝ)*x 0 + (2702574089/5000000000 : ℝ)*x 1 + (-2126660981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654784897/5000000000 : ℝ)^8263 ≤ (43098228260009/100000000000000 : ℝ)^6215 := by
    have hnat : (2654784897 : ℕ)^8263*100000000000000^6215 ≤ 43098228260009^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654784897 5000000000 43098228260009 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702574089/5000000000 : ℝ)^8263 ≤ (44132744787477/100000000000000 : ℝ)^6215 := by
    have hnat : (2702574089 : ℕ)^8263*100000000000000^6215 ≤ 44132744787477^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702574089 5000000000 44132744787477 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2126660981/10000000000 : ℝ)^8263 ≤ (12769026936617/100000000000000 : ℝ)^6215 := by
    have hnat : (2126660981 : ℕ)^8263*100000000000000^6215 ≤ 12769026936617^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126660981 10000000000 12769026936617 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654784897/5000000000 : ℝ), (2702574089/5000000000 : ℝ), (-2126660981/10000000000 : ℝ)] ![(43098228260009/100000000000000 : ℝ), (44132744787477/100000000000000 : ℝ), (12769026936617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654784897/5000000000 : ℝ)|^8263 ≤ (43098228260009/100000000000000 : ℝ)^6215
        have hw : |(2654784897/5000000000 : ℝ)|=(2654784897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702574089/5000000000 : ℝ)|^8263 ≤ (44132744787477/100000000000000 : ℝ)^6215
        have hw : |(2702574089/5000000000 : ℝ)|=(2702574089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2126660981/10000000000 : ℝ)|^8263 ≤ (12769026936617/100000000000000 : ℝ)^6215
        have hw : |(-2126660981/10000000000 : ℝ)|=(2126660981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s4_7 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4374326841/10000000000 : ℝ)*x 0 + (4524762441/10000000000 : ℝ)*x 1 + (2114490771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374326841/10000000000 : ℝ)^8263 ≤ (8327648547883/25000000000000 : ℝ)^6215 := by
    have hnat : (4374326841 : ℕ)^8263*25000000000000^6215 ≤ 8327648547883^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374326841 10000000000 8327648547883 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4524762441/10000000000 : ℝ)^8263 ≤ (34842223751111/100000000000000 : ℝ)^6215 := by
    have hnat : (4524762441 : ℕ)^8263*100000000000000^6215 ≤ 34842223751111^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524762441 10000000000 34842223751111 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114490771/5000000000 : ℝ)^8263 ≤ (31847182043291/100000000000000 : ℝ)^6215 := by
    have hnat : (2114490771 : ℕ)^8263*100000000000000^6215 ≤ 31847182043291^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114490771 5000000000 31847182043291 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374326841/10000000000 : ℝ), (4524762441/10000000000 : ℝ), (2114490771/5000000000 : ℝ)] ![(8327648547883/25000000000000 : ℝ), (34842223751111/100000000000000 : ℝ), (31847182043291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374326841/10000000000 : ℝ)|^8263 ≤ (8327648547883/25000000000000 : ℝ)^6215
        have hw : |(4374326841/10000000000 : ℝ)|=(4374326841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4524762441/10000000000 : ℝ)|^8263 ≤ (34842223751111/100000000000000 : ℝ)^6215
        have hw : |(4524762441/10000000000 : ℝ)|=(4524762441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2114490771/5000000000 : ℝ)|^8263 ≤ (31847182043291/100000000000000 : ℝ)^6215
        have hw : |(2114490771/5000000000 : ℝ)|=(2114490771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1070_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (149/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10409/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11031/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7121/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (149/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10409/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (149/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10409/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (149/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10409/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (149/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10409/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (149/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10409/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (149/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10409/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
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
  have hpowlo : (10409/100000 : ℝ) ^ (4131/1024 : ℝ) ≤ (5432770827881221/50000000000000000000 : ℝ) := by
    have hpowers : (10409/100000 : ℝ)^4131 ≤ (5432770827881221/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10409 : ℕ)^4131*50000000000000000000^1024 ≤ 5432770827881221^1024*100000^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10409 100000 5432770827881221 50000000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10409/100000 : ℝ)) (X := (5432770827881221/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (149/1000 : ℝ) ^ (4131/1024 : ℝ) ≤ (2309164344626523/5000000000000000000 : ℝ) := by
    have hpowers : (149/1000 : ℝ)^4131 ≤ (2309164344626523/5000000000000000000 : ℝ)^1024 := by
      have hnat : (149 : ℕ)^4131*5000000000000000000^1024 ≤ 2309164344626523^1024*1000^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        149 1000 2309164344626523 5000000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (149/1000 : ℝ)) (X := (2309164344626523/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005432770827881221/25000000000000000000 : ℝ) ≤ (10000538630138439/10000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (25005432770827881221/25000000000000000000 : ℝ)^1024 ≤ (10000538630138439/10000000000000000 : ℝ)^4131 := by
      have hnat : (25005432770827881221 : ℕ)^1024*10000000000000000^4131 ≤ 10000538630138439^4131*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005432770827881221 25000000000000000000 10000538630138439 10000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538630138439/10000000000000000 : ℝ)) (X := (25005432770827881221/25000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50028524414274146451/50000000000000000000 : ℝ) ≤ (10001413833739241/10000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (50028524414274146451/50000000000000000000 : ℝ)^1024 ≤ (10001413833739241/10000000000000000 : ℝ)^4131 := by
      have hnat : (50028524414274146451 : ℕ)^1024*10000000000000000^4131 ≤ 10001413833739241^4131*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028524414274146451 50000000000000000000 10001413833739241 10000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001413833739241/10000000000000000 : ℝ)) (X := (50028524414274146451/50000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2502309164344626523/2500000000000000000 : ℝ) ≤ (10002289037340043/10000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (2502309164344626523/2500000000000000000 : ℝ)^1024 ≤ (10002289037340043/10000000000000000 : ℝ)^4131 := by
      have hnat : (2502309164344626523 : ℕ)^1024*10000000000000000^4131 ≤ 10002289037340043^4131*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2502309164344626523 2500000000000000000 10002289037340043 10000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002289037340043/10000000000000000 : ℝ)) (X := (2502309164344626523/2500000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5432770827881221/50000000000000000000 : ℝ) ≤ ((44894198999390233513/44910000000000000000 : ℝ)+2*(437601800401/224550000000000 : ℝ)*(10409/100000 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (44894198999390233513/44910000000000000000 : ℝ)+2*(437601800401/224550000000000 : ℝ)*(10409/100000 : ℝ)=(10000538630138439/10000000000000000 : ℝ) by norm_num, show 1+2*(5432770827881221/50000000000000000000 : ℝ)=(25005432770827881221/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2309164344626523/5000000000000000000 : ℝ)+(5432770827881221/50000000000000000000 : ℝ) ≤ ((44894198999390233513/44910000000000000000 : ℝ)+(437601800401/224550000000000 : ℝ)*((149/1000 : ℝ)+(10409/100000 : ℝ)))^(4131/1024 : ℝ) := by
    rw [show (44894198999390233513/44910000000000000000 : ℝ)+(437601800401/224550000000000 : ℝ)*((149/1000 : ℝ)+(10409/100000 : ℝ))=(10001413833739241/10000000000000000 : ℝ) by norm_num, show 1+(2309164344626523/5000000000000000000 : ℝ)+(5432770827881221/50000000000000000000 : ℝ)=(50028524414274146451/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2309164344626523/5000000000000000000 : ℝ) ≤ ((44894198999390233513/44910000000000000000 : ℝ)+2*(437601800401/224550000000000 : ℝ)*(149/1000 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (44894198999390233513/44910000000000000000 : ℝ)+2*(437601800401/224550000000000 : ℝ)*(149/1000 : ℝ)=(10002289037340043/10000000000000000 : ℝ) by norm_num, show 1+2*(2309164344626523/5000000000000000000 : ℝ)=(2502309164344626523/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44894198999390233513/44910000000000000000 : ℝ)*(X 1 0+X 2 0)+(437601800401/224550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (10409/100000 : ℝ)) (hi := (149/1000 : ℝ)) (c := (44894198999390233513/44910000000000000000 : ℝ)) (alpha := (437601800401/224550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44894198999390233513/44910000000000000000 : ℝ)*(X 0 1+X 2 1)+(437601800401/224550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (10409/100000 : ℝ)) (hi := (149/1000 : ℝ)) (c := (44894198999390233513/44910000000000000000 : ℝ)) (alpha := (437601800401/224550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44894198999390233513/44910000000000000000 : ℝ)*(X 0 2+X 1 2)+(437601800401/224550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (10409/100000 : ℝ)) (hi := (149/1000 : ℝ)) (c := (44894198999390233513/44910000000000000000 : ℝ)) (alpha := (437601800401/224550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1100377829/5000000000 : ℝ)*X 0 0+(2702797041/5000000000 : ℝ)*X 0 1+(2626952173/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673893407/5000000000 : ℝ)*X 1 0+(-569476233/2500000000 : ℝ)*X 1 1+(164184533/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673893391/5000000000 : ℝ)*X 2 0+(1050781033/2000000000 : ℝ)*X 2 1+(-35592263/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187155441/5000000000 : ℝ)*X 0 0+(1057026867/2500000000 : ℝ)*X 0 1+(565704123/1250000000 : ℝ)*X 0 2+(2187155441/5000000000 : ℝ)*X 1 0+(1057026867/2500000000 : ℝ)*X 1 1+(565704123/1250000000 : ℝ)*X 1 2+(2187155441/5000000000 : ℝ)*X 2 0+(1057026867/2500000000 : ℝ)*X 2 1+(565704123/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-440152633/2000000000 : ℝ)*X 0 0+(1313587161/2500000000 : ℝ)*X 0 1+(5405148337/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2654785003/5000000000 : ℝ)*X 1 0+(-1063330389/5000000000 : ℝ)*X 1 1+(5405148117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2654784897/5000000000 : ℝ)*X 2 0+(2702574089/5000000000 : ℝ)*X 2 1+(-2126660981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4374326841/10000000000 : ℝ)*X 0 0+(4524762441/10000000000 : ℝ)*X 0 1+(2114490771/5000000000 : ℝ)*X 0 2+(4374326841/10000000000 : ℝ)*X 1 0+(4524762441/10000000000 : ℝ)*X 1 1+(2114490771/5000000000 : ℝ)*X 1 2+(4374326841/10000000000 : ℝ)*X 2 0+(4524762441/10000000000 : ℝ)*X 2 1+(2114490771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1103520067211528103373252417/374250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93611533/100000000000000 : ℝ)*(base21) + (27661211/50000000000000 : ℝ)*(base29) + (140085859/100000000000000 : ℝ)*(upper2) + (68665319/50000000000000 : ℝ)*(upper3) + (32508027/20000000000000 : ℝ)*(upper4) + (16901967/6250000000000 : ℝ)*(upper5) + (4976747078339187/100000000000000 : ℝ)*(major0) + (4976747133661609/100000000000000 : ℝ)*(major1) + (4976747133661609/100000000000000 : ℝ)*(major2) + (412026025535977/6250000000000 : ℝ)*(sp0) + (65924363060647/1000000000000 : ℝ)*(sp1) + (1318487242490633/20000000000000 : ℝ)*(sp2) + (840264451912207/25000000000000 : ℝ)*(sp3) + (19952811489/100000000000000 : ℝ)*(sp4) + (840264451912207/25000000000000 : ℝ)*(f.failure) + (6592436361387121/100000000000000 : ℝ)*(f.sum) + (1667730240321893/22455000000000000000000000000 : ℝ)*base65 + (402798077947655287/499000000000000000000000000000000 : ℝ)*base68 + (17204854109474655287/499000000000000000000000000000000 : ℝ)*base70 + (225313803378054373931/4491000000000000000000000000000000 : ℝ)*base71 + (25524714224719/5613750000000000000000000000 : ℝ)*base73 + (12127416026401297583/4491000000000000000000000000000000 : ℝ)*base76 + (128083881363875626069/4491000000000000000000000000000000 : ℝ)*base78 + (1903559213908297583/4491000000000000000000000000000000 : ℝ)*base80 + (1485295818641/5613750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (3081803/1250000000000000000000 : ℝ)*base89 + (3081803/1250000000000000000000 : ℝ)*base91 + (3081803/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (181359896346955628369534737/249500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (200479111/20000000000000 : ℝ)*(base19) + (868548791/100000000000000 : ℝ)*(base23) + (22502097/100000000000000 : ℝ)*(lower3) + (96597249/100000000000000 : ℝ)*(lower4) + (5006095471309253/100000000000000 : ℝ)*(major0) + (5006095471309253/100000000000000 : ℝ)*(major1) + (5006095471309253/100000000000000 : ℝ)*(major2) + (903913859/50000000000000 : ℝ)*(sp0) + (12051509489/50000000000000 : ℝ)*(sp1) + (1063560543/6250000000000 : ℝ)*(sp2) + (1326262166898633/20000000000000 : ℝ)*(sp4) + (6631287536906349/100000000000000 : ℝ)*(sp5) + (6631294756803403/100000000000000 : ℝ)*(sp6) + (845219569016959/25000000000000 : ℝ)*(sp7) + (845219569016959/25000000000000 : ℝ)*(f.failure) + (6631312642320883/100000000000000 : ℝ)*(f.sum) + (75468491768279/22455000000000000000000000000 : ℝ)*base66 + (1262137971899311579/499000000000000000000000000000000 : ℝ)*base68 + (2322961792933688421/499000000000000000000000000000000 : ℝ)*base69 + (1194014217449311579/499000000000000000000000000000000 : ℝ)*base72 + (33743999723621/5613750000000000000000000000 : ℝ)*base74 + (4207301277501688421/499000000000000000000000000000000 : ℝ)*base75 + (234140343362688421/499000000000000000000000000000000 : ℝ)*base77 + (10856206709218688421/499000000000000000000000000000000 : ℝ)*base79 + (121507393225709/22455000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (5340411/1250000000000000000000 : ℝ)*base89 + (5340411/1250000000000000000000 : ℝ)*base91 + (5340411/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1070_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (149/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10409/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11031/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7121/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1070_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1070_s5_0 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2201572587/10000000000 : ℝ)*x 0 + (5396878557/10000000000 : ℝ)*x 1 + (1052416851/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2201572587/10000000000 : ℝ)^8263 ≤ (3342619078601/25000000000000 : ℝ)^6215 := by
    have hnat : (2201572587 : ℕ)^8263*25000000000000^6215 ≤ 3342619078601^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201572587 10000000000 3342619078601 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396878557/10000000000 : ℝ)^8263 ≤ (44042996528489/100000000000000 : ℝ)^6215 := by
    have hnat : (5396878557 : ℕ)^8263*100000000000000^6215 ≤ 44042996528489^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396878557 10000000000 44042996528489 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052416851/2000000000 : ℝ)^8263 ≤ (10646631784787/25000000000000 : ℝ)^6215 := by
    have hnat : (1052416851 : ℕ)^8263*25000000000000^6215 ≤ 10646631784787^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052416851 2000000000 10646631784787 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2201572587/10000000000 : ℝ), (5396878557/10000000000 : ℝ), (1052416851/2000000000 : ℝ)] ![(3342619078601/25000000000000 : ℝ), (44042996528489/100000000000000 : ℝ), (10646631784787/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2201572587/10000000000 : ℝ)|^8263 ≤ (3342619078601/25000000000000 : ℝ)^6215
        have hw : |(-2201572587/10000000000 : ℝ)|=(2201572587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396878557/10000000000 : ℝ)|^8263 ≤ (44042996528489/100000000000000 : ℝ)^6215
        have hw : |(5396878557/10000000000 : ℝ)|=(5396878557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052416851/2000000000 : ℝ)|^8263 ≤ (10646631784787/25000000000000 : ℝ)^6215
        have hw : |(1052416851/2000000000 : ℝ)|=(1052416851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s5_1 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345616267/10000000000 : ℝ)*x 0 + (-141875001/625000000 : ℝ)*x 1 + (5262084647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345616267/10000000000 : ℝ)^8263 ≤ (5435958947857/12500000000000 : ℝ)^6215 := by
    have hnat : (5345616267 : ℕ)^8263*12500000000000^6215 ≤ 5435958947857^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345616267 10000000000 5435958947857 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141875001/625000000 : ℝ)^8263 ≤ (6962898525801/50000000000000 : ℝ)^6215 := by
    have hnat : (141875001 : ℕ)^8263*50000000000000^6215 ≤ 6962898525801^6215*625000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141875001 625000000 6962898525801 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262084647/10000000000 : ℝ)^8263 ≤ (332707276227/781250000000 : ℝ)^6215 := by
    have hnat : (5262084647 : ℕ)^8263*781250000000^6215 ≤ 332707276227^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262084647 10000000000 332707276227 781250000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345616267/10000000000 : ℝ), (-141875001/625000000 : ℝ), (5262084647/10000000000 : ℝ)] ![(5435958947857/12500000000000 : ℝ), (6962898525801/50000000000000 : ℝ), (332707276227/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345616267/10000000000 : ℝ)|^8263 ≤ (5435958947857/12500000000000 : ℝ)^6215
        have hw : |(5345616267/10000000000 : ℝ)|=(5345616267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-141875001/625000000 : ℝ)|^8263 ≤ (6962898525801/50000000000000 : ℝ)^6215
        have hw : |(-141875001/625000000 : ℝ)|=(141875001/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262084647/10000000000 : ℝ)|^8263 ≤ (332707276227/781250000000 : ℝ)^6215
        have hw : |(5262084647/10000000000 : ℝ)|=(5262084647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s5_2 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672808151/5000000000 : ℝ)*x 0 + (526208433/1000000000 : ℝ)*x 1 + (-2270000387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672808151/5000000000 : ℝ)^8263 ≤ (8697534392283/20000000000000 : ℝ)^6215 := by
    have hnat : (2672808151 : ℕ)^8263*20000000000000^6215 ≤ 8697534392283^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672808151 5000000000 8697534392283 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526208433/1000000000 : ℝ)^8263 ≤ (21293263973073/50000000000000 : ℝ)^6215 := by
    have hnat : (526208433 : ℕ)^8263*50000000000000^6215 ≤ 21293263973073^6215*1000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526208433 1000000000 21293263973073 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2270000387/10000000000 : ℝ)^8263 ≤ (13925800077573/100000000000000 : ℝ)^6215 := by
    have hnat : (2270000387 : ℕ)^8263*100000000000000^6215 ≤ 13925800077573^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270000387 10000000000 13925800077573 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672808151/5000000000 : ℝ), (526208433/1000000000 : ℝ), (-2270000387/10000000000 : ℝ)] ![(8697534392283/20000000000000 : ℝ), (21293263973073/50000000000000 : ℝ), (13925800077573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672808151/5000000000 : ℝ)|^8263 ≤ (8697534392283/20000000000000 : ℝ)^6215
        have hw : |(2672808151/5000000000 : ℝ)|=(2672808151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526208433/1000000000 : ℝ)|^8263 ≤ (21293263973073/50000000000000 : ℝ)^6215
        have hw : |(526208433/1000000000 : ℝ)|=(526208433/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2270000387/10000000000 : ℝ)|^8263 ≤ (13925800077573/100000000000000 : ℝ)^6215
        have hw : |(-2270000387/10000000000 : ℝ)|=(2270000387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s5_3 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4374786557/10000000000 : ℝ)*x 0 + (265288367/625000000 : ℝ)*x 1 + (4509001519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374786557/10000000000 : ℝ)^8263 ≤ (16657624302223/50000000000000 : ℝ)^6215 := by
    have hnat : (4374786557 : ℕ)^8263*50000000000000^6215 ≤ 16657624302223^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374786557 10000000000 16657624302223 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265288367/625000000 : ℝ)^8263 ≤ (32003792140721/100000000000000 : ℝ)^6215 := by
    have hnat : (265288367 : ℕ)^8263*100000000000000^6215 ≤ 32003792140721^6215*625000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265288367 625000000 32003792140721 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4509001519/10000000000 : ℝ)^8263 ≤ (3468095923801/10000000000000 : ℝ)^6215 := by
    have hnat : (4509001519 : ℕ)^8263*10000000000000^6215 ≤ 3468095923801^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509001519 10000000000 3468095923801 10000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374786557/10000000000 : ℝ), (265288367/625000000 : ℝ), (4509001519/10000000000 : ℝ)] ![(16657624302223/50000000000000 : ℝ), (32003792140721/100000000000000 : ℝ), (3468095923801/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374786557/10000000000 : ℝ)|^8263 ≤ (16657624302223/50000000000000 : ℝ)^6215
        have hw : |(4374786557/10000000000 : ℝ)|=(4374786557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(265288367/625000000 : ℝ)|^8263 ≤ (32003792140721/100000000000000 : ℝ)^6215
        have hw : |(265288367/625000000 : ℝ)|=(265288367/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4509001519/10000000000 : ℝ)|^8263 ≤ (3468095923801/10000000000000 : ℝ)^6215
        have hw : |(4509001519/10000000000 : ℝ)|=(4509001519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s5_4 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-44031563/200000000 : ℝ)*x 0 + (2631217529/5000000000 : ℝ)*x 1 + (5396526519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44031563/200000000 : ℝ)^8263 ≤ (6685260616167/50000000000000 : ℝ)^6215 := by
    have hnat : (44031563 : ℕ)^8263*50000000000000^6215 ≤ 6685260616167^6215*200000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44031563 200000000 6685260616167 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631217529/5000000000 : ℝ)^8263 ≤ (42590301810253/100000000000000 : ℝ)^6215 := by
    have hnat : (2631217529 : ℕ)^8263*100000000000000^6215 ≤ 42590301810253^6215*5000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631217529 5000000000 42590301810253 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396526519/10000000000 : ℝ)^8263 ≤ (5504897118451/12500000000000 : ℝ)^6215 := by
    have hnat : (5396526519 : ℕ)^8263*12500000000000^6215 ≤ 5504897118451^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396526519 10000000000 5504897118451 12500000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-44031563/200000000 : ℝ), (2631217529/5000000000 : ℝ), (5396526519/10000000000 : ℝ)] ![(6685260616167/50000000000000 : ℝ), (42590301810253/100000000000000 : ℝ), (5504897118451/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-44031563/200000000 : ℝ)|^8263 ≤ (6685260616167/50000000000000 : ℝ)^6215
        have hw : |(-44031563/200000000 : ℝ)|=(44031563/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631217529/5000000000 : ℝ)|^8263 ≤ (42590301810253/100000000000000 : ℝ)^6215
        have hw : |(2631217529/5000000000 : ℝ)|=(2631217529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396526519/10000000000 : ℝ)|^8263 ≤ (5504897118451/12500000000000 : ℝ)^6215
        have hw : |(5396526519/10000000000 : ℝ)|=(5396526519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s5_5 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311654239/10000000000 : ℝ)*x 0 + (-427111591/2000000000 : ℝ)*x 1 + (5396526473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311654239/10000000000 : ℝ)^8263 ≤ (43120724774269/100000000000000 : ℝ)^6215 := by
    have hnat : (5311654239 : ℕ)^8263*100000000000000^6215 ≤ 43120724774269^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311654239 10000000000 43120724774269 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (427111591/2000000000 : ℝ)^8263 ≤ (2568019751899/20000000000000 : ℝ)^6215 := by
    have hnat : (427111591 : ℕ)^8263*20000000000000^6215 ≤ 2568019751899^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427111591 2000000000 2568019751899 20000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396526473/10000000000 : ℝ)^8263 ≤ (22019588224259/50000000000000 : ℝ)^6215 := by
    have hnat : (5396526473 : ℕ)^8263*50000000000000^6215 ≤ 22019588224259^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396526473 10000000000 22019588224259 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311654239/10000000000 : ℝ), (-427111591/2000000000 : ℝ), (5396526473/10000000000 : ℝ)] ![(43120724774269/100000000000000 : ℝ), (2568019751899/20000000000000 : ℝ), (22019588224259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311654239/10000000000 : ℝ)|^8263 ≤ (43120724774269/100000000000000 : ℝ)^6215
        have hw : |(5311654239/10000000000 : ℝ)|=(5311654239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-427111591/2000000000 : ℝ)|^8263 ≤ (2568019751899/20000000000000 : ℝ)^6215
        have hw : |(-427111591/2000000000 : ℝ)|=(427111591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396526473/10000000000 : ℝ)|^8263 ≤ (22019588224259/50000000000000 : ℝ)^6215
        have hw : |(5396526473/10000000000 : ℝ)|=(5396526473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s5_6 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311654199/10000000000 : ℝ)*x 0 + (5396526521/10000000000 : ℝ)*x 1 + (-266944743/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311654199/10000000000 : ℝ)^8263 ≤ (21560362171269/50000000000000 : ℝ)^6215 := by
    have hnat : (5311654199 : ℕ)^8263*50000000000000^6215 ≤ 21560362171269^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311654199 10000000000 21560362171269 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396526521/10000000000 : ℝ)^8263 ≤ (11009794242327/25000000000000 : ℝ)^6215 := by
    have hnat : (5396526521 : ℕ)^8263*25000000000000^6215 ≤ 11009794242327^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396526521 10000000000 11009794242327 25000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266944743/1250000000 : ℝ)^8263 ≤ (12840098671563/100000000000000 : ℝ)^6215 := by
    have hnat : (266944743 : ℕ)^8263*100000000000000^6215 ≤ 12840098671563^6215*1250000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266944743 1250000000 12840098671563 100000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311654199/10000000000 : ℝ), (5396526521/10000000000 : ℝ), (-266944743/1250000000 : ℝ)] ![(21560362171269/50000000000000 : ℝ), (11009794242327/25000000000000 : ℝ), (12840098671563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311654199/10000000000 : ℝ)|^8263 ≤ (21560362171269/50000000000000 : ℝ)^6215
        have hw : |(5311654199/10000000000 : ℝ)|=(5311654199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396526521/10000000000 : ℝ)|^8263 ≤ (11009794242327/25000000000000 : ℝ)^6215
        have hw : |(5396526521/10000000000 : ℝ)|=(5396526521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-266944743/1250000000 : ℝ)|^8263 ≤ (12840098671563/100000000000000 : ℝ)^6215
        have hw : |(-266944743/1250000000 : ℝ)|=(266944743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1070_s5_7 (p : ℝ) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (218739877/500000000 : ℝ)*x 0 + (4508313729/10000000000 : ℝ)*x 1 + (849060873/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218739877/500000000 : ℝ)^8263 ≤ (16657679902119/50000000000000 : ℝ)^6215 := by
    have hnat : (218739877 : ℕ)^8263*50000000000000^6215 ≤ 16657679902119^6215*500000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218739877 500000000 16657679902119 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508313729/10000000000 : ℝ)^8263 ≤ (277391408393/800000000000 : ℝ)^6215 := by
    have hnat : (4508313729 : ℕ)^8263*800000000000^6215 ≤ 277391408393^6215*10000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508313729 10000000000 277391408393 800000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849060873/2000000000 : ℝ)^8263 ≤ (16005357063959/50000000000000 : ℝ)^6215 := by
    have hnat : (849060873 : ℕ)^8263*50000000000000^6215 ≤ 16005357063959^6215*2000000000^8263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849060873 2000000000 16005357063959 50000000000000 8263 6215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8263/2048 : ℝ)) 8263 6215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218739877/500000000 : ℝ), (4508313729/10000000000 : ℝ), (849060873/2000000000 : ℝ)] ![(16657679902119/50000000000000 : ℝ), (277391408393/800000000000 : ℝ), (16005357063959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218739877/500000000 : ℝ)|^8263 ≤ (16657679902119/50000000000000 : ℝ)^6215
        have hw : |(218739877/500000000 : ℝ)|=(218739877/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508313729/10000000000 : ℝ)|^8263 ≤ (277391408393/800000000000 : ℝ)^6215
        have hw : |(4508313729/10000000000 : ℝ)|=(4508313729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849060873/2000000000 : ℝ)|^8263 ≤ (16005357063959/50000000000000 : ℝ)^6215
        have hw : |(849060873/2000000000 : ℝ)|=(849060873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1070_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7121/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11031/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2241/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (703/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7121/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11031/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7121/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11031/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7121/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11031/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7121/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11031/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7121/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11031/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7121/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11031/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11031/100000 : ℝ) ^ (4131/1024 : ℝ) ≤ (3433020706923683/25000000000000000000 : ℝ) := by
    have hpowers : (11031/100000 : ℝ)^4131 ≤ (3433020706923683/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11031 : ℕ)^4131*25000000000000000000^1024 ≤ 3433020706923683^1024*100000^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11031 100000 3433020706923683 25000000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11031/100000 : ℝ)) (X := (3433020706923683/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7121/50000 : ℝ) ^ (4131/1024 : ℝ) ≤ (38490472851428393/100000000000000000000 : ℝ) := by
    have hpowers : (7121/50000 : ℝ)^4131 ≤ (38490472851428393/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7121 : ℕ)^4131*100000000000000000000^1024 ≤ 38490472851428393^1024*50000^4131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7121 50000 38490472851428393 100000000000000000000 4131 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7121/50000 : ℝ)) (X := (38490472851428393/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503433020706923683/12500000000000000000 : ℝ) ≤ (5000340358284679/5000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (12503433020706923683/12500000000000000000 : ℝ)^1024 ≤ (5000340358284679/5000000000000000 : ℝ)^4131 := by
      have hnat : (12503433020706923683 : ℕ)^1024*5000000000000000^4131 ≤ 5000340358284679^4131*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503433020706923683 12500000000000000000 5000340358284679 5000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000340358284679/5000000000000000 : ℝ)) (X := (12503433020706923683/12500000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (160083556089086597/160000000000000000 : ℝ) ≤ (2500323562080679/2500000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (160083556089086597/160000000000000000 : ℝ)^1024 ≤ (2500323562080679/2500000000000000 : ℝ)^4131 := by
      have hnat : (160083556089086597 : ℕ)^1024*2500000000000000^4131 ≤ 2500323562080679^4131*160000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        160083556089086597 160000000000000000 2500323562080679 2500000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500323562080679/2500000000000000 : ℝ)) (X := (160083556089086597/160000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038490472851428393/50000000000000000000 : ℝ) ≤ (5000953890038037/5000000000000000 : ℝ) ^ (4131/1024 : ℝ) := by
    have hpowers : (50038490472851428393/50000000000000000000 : ℝ)^1024 ≤ (5000953890038037/5000000000000000 : ℝ)^4131 := by
      have hnat : (50038490472851428393 : ℕ)^1024*5000000000000000^4131 ≤ 5000953890038037^4131*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038490472851428393 50000000000000000000 5000953890038037 5000000000000000 1024 4131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000953890038037/5000000000000000 : ℝ)) (X := (50038490472851428393/50000000000000000000 : ℝ)) (by norm_num) 4131 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3433020706923683/25000000000000000000 : ℝ) ≤ ((16049325021680812171/16055000000000000000 : ℝ)+2*(306765876679/160550000000000 : ℝ)*(11031/100000 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (16049325021680812171/16055000000000000000 : ℝ)+2*(306765876679/160550000000000 : ℝ)*(11031/100000 : ℝ)=(5000340358284679/5000000000000000 : ℝ) by norm_num, show 1+2*(3433020706923683/25000000000000000000 : ℝ)=(12503433020706923683/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38490472851428393/100000000000000000000 : ℝ)+(3433020706923683/25000000000000000000 : ℝ) ≤ ((16049325021680812171/16055000000000000000 : ℝ)+(306765876679/160550000000000 : ℝ)*((7121/50000 : ℝ)+(11031/100000 : ℝ)))^(4131/1024 : ℝ) := by
    rw [show (16049325021680812171/16055000000000000000 : ℝ)+(306765876679/160550000000000 : ℝ)*((7121/50000 : ℝ)+(11031/100000 : ℝ))=(2500323562080679/2500000000000000 : ℝ) by norm_num, show 1+(38490472851428393/100000000000000000000 : ℝ)+(3433020706923683/25000000000000000000 : ℝ)=(160083556089086597/160000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38490472851428393/100000000000000000000 : ℝ) ≤ ((16049325021680812171/16055000000000000000 : ℝ)+2*(306765876679/160550000000000 : ℝ)*(7121/50000 : ℝ))^(4131/1024 : ℝ) := by
    rw [show (16049325021680812171/16055000000000000000 : ℝ)+2*(306765876679/160550000000000 : ℝ)*(7121/50000 : ℝ)=(5000953890038037/5000000000000000 : ℝ) by norm_num, show 1+2*(38490472851428393/100000000000000000000 : ℝ)=(50038490472851428393/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16049325021680812171/16055000000000000000 : ℝ)*(X 1 0+X 2 0)+(306765876679/160550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (11031/100000 : ℝ)) (hi := (7121/50000 : ℝ)) (c := (16049325021680812171/16055000000000000000 : ℝ)) (alpha := (306765876679/160550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16049325021680812171/16055000000000000000 : ℝ)*(X 0 1+X 2 1)+(306765876679/160550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (11031/100000 : ℝ)) (hi := (7121/50000 : ℝ)) (c := (16049325021680812171/16055000000000000000 : ℝ)) (alpha := (306765876679/160550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16049325021680812171/16055000000000000000 : ℝ)*(X 0 2+X 1 2)+(306765876679/160550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4131/1024 : ℝ)) (lo := (11031/100000 : ℝ)) (hi := (7121/50000 : ℝ)) (c := (16049325021680812171/16055000000000000000 : ℝ)) (alpha := (306765876679/160550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2201572587/10000000000 : ℝ)*X 0 0+(5396878557/10000000000 : ℝ)*X 0 1+(1052416851/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345616267/10000000000 : ℝ)*X 1 0+(-141875001/625000000 : ℝ)*X 1 1+(5262084647/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672808151/5000000000 : ℝ)*X 2 0+(526208433/1000000000 : ℝ)*X 2 1+(-2270000387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4374786557/10000000000 : ℝ)*X 0 0+(265288367/625000000 : ℝ)*X 0 1+(4509001519/10000000000 : ℝ)*X 0 2+(4374786557/10000000000 : ℝ)*X 1 0+(265288367/625000000 : ℝ)*X 1 1+(4509001519/10000000000 : ℝ)*X 1 2+(4374786557/10000000000 : ℝ)*X 2 0+(265288367/625000000 : ℝ)*X 2 1+(4509001519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-44031563/200000000 : ℝ)*X 0 0+(2631217529/5000000000 : ℝ)*X 0 1+(5396526519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311654239/10000000000 : ℝ)*X 1 0+(-427111591/2000000000 : ℝ)*X 1 1+(5396526473/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311654199/10000000000 : ℝ)*X 2 0+(5396526521/10000000000 : ℝ)*X 2 1+(-266944743/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((218739877/500000000 : ℝ)*X 0 0+(4508313729/10000000000 : ℝ)*X 0 1+(849060873/2000000000 : ℝ)*X 0 2+(218739877/500000000 : ℝ)*X 1 0+(4508313729/10000000000 : ℝ)*X 1 1+(849060873/2000000000 : ℝ)*X 1 2+(218739877/500000000 : ℝ)*X 2 0+(4508313729/10000000000 : ℝ)*X 2 1+(849060873/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1070_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5106130657212880157323913487/802750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51037461/6250000000000 : ℝ)*(base19) + (885525201/100000000000000 : ℝ)*(base23) + (364521829/100000000000000 : ℝ)*(upper3) + (1886449/6250000000000 : ℝ)*(lower4) + (5600565185950329/100000000000000 : ℝ)*(major0) + (5600565185950329/100000000000000 : ℝ)*(major1) + (560056518595033/10000000000000 : ℝ)*(major2) + (7418752077061781/100000000000000 : ℝ)*(sp0) + (7418774556115723/100000000000000 : ℝ)*(sp1) + (3709384401633987/50000000000000 : ℝ)*(sp2) + (3782336402960967/100000000000000 : ℝ)*(sp3) + (11647826659/50000000000000 : ℝ)*(sp4) + (227356877/4000000000000 : ℝ)*(sp6) + (18384197981/100000000000000 : ℝ)*(sp7) + (3782354787158949/100000000000000 : ℝ)*(f.failure) + (7418775372715099/100000000000000 : ℝ)*(f.sum) + (2746694412199/16055000000000000000000000000 : ℝ)*base66 + (34341599999104654259/1605500000000000000000000000000000 : ℝ)*base67 + (1860887490686206643/160550000000000000000000000000000 : ℝ)*base69 + (3780492677108345741/1605500000000000000000000000000000 : ℝ)*base72 + (5796303778907/8027500000000000000000000000 : ℝ)*base74 + (1303151788625006643/160550000000000000000000000000000 : ℝ)*base75 + (132992856919855039/84500000000000000000000000000000 : ℝ)*base78 + (157246311911855039/84500000000000000000000000000000 : ℝ)*base80 + (18141083037109/8027500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (30404121/5000000000000000000000 : ℝ)*base89 + (30404121/5000000000000000000000 : ℝ)*base91 + (19595879/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9331818176009017036840941/1187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (761081071/50000000000000 : ℝ)*(base19) + (162368549/10000000000000 : ℝ)*(base23) + (79505211/50000000000000 : ℝ)*(upper3) + (68316993/100000000000000 : ℝ)*(lower4) + (27754871/20000000000000 : ℝ)*(upper5) + (1407467394549411/25000000000000 : ℝ)*(major0) + (1407467394549411/25000000000000 : ℝ)*(major1) + (1407467394549411/25000000000000 : ℝ)*(major2) + (37741823091/100000000000000 : ℝ)*(sp1) + (42287708563/100000000000000 : ℝ)*(sp2) + (3728796658750183/50000000000000 : ℝ)*(sp4) + (1864388513378783/25000000000000 : ℝ)*(sp5) + (7457549406106313/100000000000000 : ℝ)*(sp6) + (1901072788474571/50000000000000 : ℝ)*(sp7) + (1901072788474571/50000000000000 : ℝ)*(f.failure) + (3728796658750183/50000000000000 : ℝ)*(f.sum) + (736591648449/308750000000000000000000000 : ℝ)*base66 + (8348859364875177/1625000000000000000000000000000 : ℝ)*base68 + (17525086551625177/1625000000000000000000000000000 : ℝ)*base70 + (10922493380750177/1625000000000000000000000000000 : ℝ)*base72 + (111360048983/617500000000000000000000000 : ℝ)*base74 + (7082946010000177/1625000000000000000000000000000 : ℝ)*base76 + (22395621391250177/1625000000000000000000000000000 : ℝ)*base78 + (4209844021750177/1625000000000000000000000000000 : ℝ)*base80 + (3225443775409/1235000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (19575959/2500000000000000000000 : ℝ)*base89 + (19575959/2500000000000000000000 : ℝ)*base91 + (19575959/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1070_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7121/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11031/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (703/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1070_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1070_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2091/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8731/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (703/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1070_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1070_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1070_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4131/1024 : ℝ) ≤ p) (hpb : p ≤ (8263/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74035429/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2091/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8731/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (703/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1070_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
