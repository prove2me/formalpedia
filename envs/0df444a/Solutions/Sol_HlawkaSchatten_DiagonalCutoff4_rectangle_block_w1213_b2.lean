-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1213_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:08:01.445402+00:00
-- url     : https://prove2.me/submissions/baec8440-c836-4097-a005-23fe9b152792

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
theorem support_rectangle_w1213_s6_0 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-533342189/2500000000 : ℝ)*x 0 + (1078393169/2000000000 : ℝ)*x 1 + (2633298949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533342189/2500000000 : ℝ)^4203 ≤ (2594052461149/20000000000000 : ℝ)^3179 := by
    have hnat : (533342189 : ℕ)^4203*20000000000000^3179 ≤ 2594052461149^3179*2500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533342189 2500000000 2594052461149 20000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078393169/2000000000 : ℝ)^4203 ≤ (44191542685081/100000000000000 : ℝ)^3179 := by
    have hnat : (1078393169 : ℕ)^4203*100000000000000^3179 ≤ 44191542685081^3179*2000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078393169 2000000000 44191542685081 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633298949/5000000000 : ℝ)^4203 ≤ (2677387187759/6250000000000 : ℝ)^3179 := by
    have hnat : (2633298949 : ℕ)^4203*6250000000000^3179 ≤ 2677387187759^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633298949 5000000000 2677387187759 6250000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-533342189/2500000000 : ℝ), (1078393169/2000000000 : ℝ), (2633298949/5000000000 : ℝ)] ![(2594052461149/20000000000000 : ℝ), (44191542685081/100000000000000 : ℝ), (2677387187759/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-533342189/2500000000 : ℝ)|^4203 ≤ (2594052461149/20000000000000 : ℝ)^3179
        have hw : |(-533342189/2500000000 : ℝ)|=(533342189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078393169/2000000000 : ℝ)|^4203 ≤ (44191542685081/100000000000000 : ℝ)^3179
        have hw : |(1078393169/2000000000 : ℝ)|=(1078393169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633298949/5000000000 : ℝ)|^4203 ≤ (2677387187759/6250000000000 : ℝ)^3179
        have hw : |(2633298949/5000000000 : ℝ)|=(2633298949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s6_1 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068902689/2000000000 : ℝ)*x 0 + (-87877739/400000000 : ℝ)*x 1 + (2633298953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068902689/2000000000 : ℝ)^4203 ≤ (43678088330397/100000000000000 : ℝ)^3179 := by
    have hnat : (1068902689 : ℕ)^4203*100000000000000^3179 ≤ 43678088330397^3179*2000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068902689 2000000000 43678088330397 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87877739/400000000 : ℝ)^4203 ≤ (3370929141811/25000000000000 : ℝ)^3179 := by
    have hnat : (87877739 : ℕ)^4203*25000000000000^3179 ≤ 3370929141811^3179*400000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87877739 400000000 3370929141811 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633298953/5000000000 : ℝ)^4203 ≤ (167336699571/390625000000 : ℝ)^3179 := by
    have hnat : (2633298953 : ℕ)^4203*390625000000^3179 ≤ 167336699571^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633298953 5000000000 167336699571 390625000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068902689/2000000000 : ℝ), (-87877739/400000000 : ℝ), (2633298953/5000000000 : ℝ)] ![(43678088330397/100000000000000 : ℝ), (3370929141811/25000000000000 : ℝ), (167336699571/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068902689/2000000000 : ℝ)|^4203 ≤ (43678088330397/100000000000000 : ℝ)^3179
        have hw : |(1068902689/2000000000 : ℝ)|=(1068902689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-87877739/400000000 : ℝ)|^4203 ≤ (3370929141811/25000000000000 : ℝ)^3179
        have hw : |(-87877739/400000000 : ℝ)|=(87877739/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633298953/5000000000 : ℝ)|^4203 ≤ (167336699571/390625000000 : ℝ)^3179
        have hw : |(2633298953/5000000000 : ℝ)|=(2633298953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s6_2 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344513449/10000000000 : ℝ)*x 0 + (5266597903/10000000000 : ℝ)*x 1 + (-1098471737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344513449/10000000000 : ℝ)^4203 ≤ (43678088373617/100000000000000 : ℝ)^3179 := by
    have hnat : (5344513449 : ℕ)^4203*100000000000000^3179 ≤ 43678088373617^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344513449 10000000000 43678088373617 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266597903/10000000000 : ℝ)^4203 ≤ (21419097528957/50000000000000 : ℝ)^3179 := by
    have hnat : (5266597903 : ℕ)^4203*50000000000000^3179 ≤ 21419097528957^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266597903 10000000000 21419097528957 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098471737/5000000000 : ℝ)^4203 ≤ (1348371655913/10000000000000 : ℝ)^3179 := by
    have hnat : (1098471737 : ℕ)^4203*10000000000000^3179 ≤ 1348371655913^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098471737 5000000000 1348371655913 10000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344513449/10000000000 : ℝ), (5266597903/10000000000 : ℝ), (-1098471737/5000000000 : ℝ)] ![(43678088373617/100000000000000 : ℝ), (21419097528957/50000000000000 : ℝ), (1348371655913/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344513449/10000000000 : ℝ)|^4203 ≤ (43678088373617/100000000000000 : ℝ)^3179
        have hw : |(5344513449/10000000000 : ℝ)|=(5344513449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266597903/10000000000 : ℝ)|^4203 ≤ (21419097528957/50000000000000 : ℝ)^3179
        have hw : |(5266597903/10000000000 : ℝ)|=(5266597903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1098471737/5000000000 : ℝ)|^4203 ≤ (1348371655913/10000000000000 : ℝ)^3179
        have hw : |(-1098471737/5000000000 : ℝ)|=(1098471737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s6_3 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2177377261/5000000000 : ℝ)*x 0 + (84602083/200000000 : ℝ)*x 1 + (4482998557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177377261/5000000000 : ℝ)^4203 ≤ (6663445761077/20000000000000 : ℝ)^3179 := by
    have hnat : (2177377261 : ℕ)^4203*20000000000000^3179 ≤ 6663445761077^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177377261 5000000000 6663445761077 20000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84602083/200000000 : ℝ)^4203 ≤ (32062217322421/100000000000000 : ℝ)^3179 := by
    have hnat : (84602083 : ℕ)^4203*100000000000000^3179 ≤ 32062217322421^3179*200000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84602083 200000000 32062217322421 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4482998557/10000000000 : ℝ)^4203 ≤ (8655138462059/25000000000000 : ℝ)^3179 := by
    have hnat : (4482998557 : ℕ)^4203*25000000000000^3179 ≤ 8655138462059^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482998557 10000000000 8655138462059 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177377261/5000000000 : ℝ), (84602083/200000000 : ℝ), (4482998557/10000000000 : ℝ)] ![(6663445761077/20000000000000 : ℝ), (32062217322421/100000000000000 : ℝ), (8655138462059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177377261/5000000000 : ℝ)|^4203 ≤ (6663445761077/20000000000000 : ℝ)^3179
        have hw : |(2177377261/5000000000 : ℝ)|=(2177377261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84602083/200000000 : ℝ)|^4203 ≤ (32062217322421/100000000000000 : ℝ)^3179
        have hw : |(84602083/200000000 : ℝ)|=(84602083/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4482998557/10000000000 : ℝ)|^4203 ≤ (8655138462059/25000000000000 : ℝ)^3179
        have hw : |(4482998557/10000000000 : ℝ)|=(4482998557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s6_4 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-213337353/1000000000 : ℝ)*x 0 + (5266914847/10000000000 : ℝ)*x 1 + (5391647741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213337353/1000000000 : ℝ)^4203 ≤ (12970300679497/100000000000000 : ℝ)^3179 := by
    have hnat : (213337353 : ℕ)^4203*100000000000000^3179 ≤ 12970300679497^3179*1000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213337353 1000000000 12970300679497 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266914847/10000000000 : ℝ)^4203 ≤ (42841603505407/100000000000000 : ℝ)^3179 := by
    have hnat : (5266914847 : ℕ)^4203*100000000000000^3179 ≤ 42841603505407^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266914847 10000000000 42841603505407 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391647741/10000000000 : ℝ)^4203 ≤ (44188095807211/100000000000000 : ℝ)^3179 := by
    have hnat : (5391647741 : ℕ)^4203*100000000000000^3179 ≤ 44188095807211^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391647741 10000000000 44188095807211 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213337353/1000000000 : ℝ), (5266914847/10000000000 : ℝ), (5391647741/10000000000 : ℝ)] ![(12970300679497/100000000000000 : ℝ), (42841603505407/100000000000000 : ℝ), (44188095807211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213337353/1000000000 : ℝ)|^4203 ≤ (12970300679497/100000000000000 : ℝ)^3179
        have hw : |(-213337353/1000000000 : ℝ)|=(213337353/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266914847/10000000000 : ℝ)|^4203 ≤ (42841603505407/100000000000000 : ℝ)^3179
        have hw : |(5266914847/10000000000 : ℝ)|=(5266914847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391647741/10000000000 : ℝ)|^4203 ≤ (44188095807211/100000000000000 : ℝ)^3179
        have hw : |(5391647741/10000000000 : ℝ)|=(5391647741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s6_5 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312588731/10000000000 : ℝ)*x 0 + (-1035946803/5000000000 : ℝ)*x 1 + (269582389/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312588731/10000000000 : ℝ)^4203 ≤ (5416684308331/12500000000000 : ℝ)^3179 := by
    have hnat : (5312588731 : ℕ)^4203*12500000000000^3179 ≤ 5416684308331^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312588731 10000000000 5416684308331 12500000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035946803/5000000000 : ℝ)^4203 ≤ (12478429287119/100000000000000 : ℝ)^3179 := by
    have hnat : (1035946803 : ℕ)^4203*100000000000000^3179 ≤ 12478429287119^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035946803 5000000000 12478429287119 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269582389/500000000 : ℝ)^4203 ≤ (44188096229799/100000000000000 : ℝ)^3179 := by
    have hnat : (269582389 : ℕ)^4203*100000000000000^3179 ≤ 44188096229799^3179*500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269582389 500000000 44188096229799 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312588731/10000000000 : ℝ), (-1035946803/5000000000 : ℝ), (269582389/500000000 : ℝ)] ![(5416684308331/12500000000000 : ℝ), (12478429287119/100000000000000 : ℝ), (44188096229799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312588731/10000000000 : ℝ)|^4203 ≤ (5416684308331/12500000000000 : ℝ)^3179
        have hw : |(5312588731/10000000000 : ℝ)|=(5312588731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1035946803/5000000000 : ℝ)|^4203 ≤ (12478429287119/100000000000000 : ℝ)^3179
        have hw : |(-1035946803/5000000000 : ℝ)|=(1035946803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269582389/500000000 : ℝ)|^4203 ≤ (44188096229799/100000000000000 : ℝ)^3179
        have hw : |(269582389/500000000 : ℝ)|=(269582389/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s6_6 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53125887/100000000 : ℝ)*x 0 + (5391647807/10000000000 : ℝ)*x 1 + (-2071893611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53125887/100000000 : ℝ)^4203 ≤ (43333474132339/100000000000000 : ℝ)^3179 := by
    have hnat : (53125887 : ℕ)^4203*100000000000000^3179 ≤ 43333474132339^3179*100000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53125887 100000000 43333474132339 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391647807/10000000000 : ℝ)^4203 ≤ (1104702413059/2500000000000 : ℝ)^3179 := by
    have hnat : (5391647807 : ℕ)^4203*2500000000000^3179 ≤ 1104702413059^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391647807 10000000000 1104702413059 2500000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2071893611/10000000000 : ℝ)^4203 ≤ (3119607331733/25000000000000 : ℝ)^3179 := by
    have hnat : (2071893611 : ℕ)^4203*25000000000000^3179 ≤ 3119607331733^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071893611 10000000000 3119607331733 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53125887/100000000 : ℝ), (5391647807/10000000000 : ℝ), (-2071893611/10000000000 : ℝ)] ![(43333474132339/100000000000000 : ℝ), (1104702413059/2500000000000 : ℝ), (3119607331733/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53125887/100000000 : ℝ)|^4203 ≤ (43333474132339/100000000000000 : ℝ)^3179
        have hw : |(53125887/100000000 : ℝ)|=(53125887/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391647807/10000000000 : ℝ)|^4203 ≤ (1104702413059/2500000000000 : ℝ)^3179
        have hw : |(5391647807/10000000000 : ℝ)|=(5391647807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2071893611/10000000000 : ℝ)|^4203 ≤ (3119607331733/25000000000000 : ℝ)^3179
        have hw : |(-2071893611/10000000000 : ℝ)|=(2071893611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s6_7 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4354764171/10000000000 : ℝ)*x 0 + (448235923/1000000000 : ℝ)*x 1 + (2115372889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354764171/10000000000 : ℝ)^4203 ≤ (3331732640689/10000000000000 : ℝ)^3179 := by
    have hnat : (4354764171 : ℕ)^4203*10000000000000^3179 ≤ 3331732640689^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354764171 10000000000 3331732640689 10000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448235923/1000000000 : ℝ)^4203 ≤ (1730701317063/5000000000000 : ℝ)^3179 := by
    have hnat : (448235923 : ℕ)^4203*5000000000000^3179 ≤ 1730701317063^3179*1000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448235923 1000000000 1730701317063 5000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115372889/5000000000 : ℝ)^4203 ≤ (16034323619009/50000000000000 : ℝ)^3179 := by
    have hnat : (2115372889 : ℕ)^4203*50000000000000^3179 ≤ 16034323619009^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115372889 5000000000 16034323619009 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354764171/10000000000 : ℝ), (448235923/1000000000 : ℝ), (2115372889/5000000000 : ℝ)] ![(3331732640689/10000000000000 : ℝ), (1730701317063/5000000000000 : ℝ), (16034323619009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354764171/10000000000 : ℝ)|^4203 ≤ (3331732640689/10000000000000 : ℝ)^3179
        have hw : |(4354764171/10000000000 : ℝ)|=(4354764171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448235923/1000000000 : ℝ)|^4203 ≤ (1730701317063/5000000000000 : ℝ)^3179
        have hw : |(448235923/1000000000 : ℝ)|=(448235923/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115372889/5000000000 : ℝ)|^4203 ≤ (16034323619009/50000000000000 : ℝ)^3179
        have hw : |(2115372889/5000000000 : ℝ)|=(2115372889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1213_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2283/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5719/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7047/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7059/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2283/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7059/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2283/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7059/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2283/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7059/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2283/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7059/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2283/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7059/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2283/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2283/20000 : ℝ) ^ (8405/2048 : ℝ) ≤ (2709614280326727/20000000000000000000 : ℝ) := by
    have hpowers : (2283/20000 : ℝ)^8405 ≤ (2709614280326727/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2283 : ℕ)^8405*20000000000000000000^2048 ≤ 2709614280326727^2048*20000^8405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2283 20000 2709614280326727 20000000000000000000 8405 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2283/20000 : ℝ)) (X := (2709614280326727/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7059/50000 : ℝ) ^ (8405/2048 : ℝ) ≤ (1620450629441679/5000000000000000000 : ℝ) := by
    have hpowers : (7059/50000 : ℝ)^8405 ≤ (1620450629441679/5000000000000000000 : ℝ)^2048 := by
      have hnat : (7059 : ℕ)^8405*5000000000000000000^2048 ≤ 1620450629441679^2048*50000^8405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7059 50000 1620450629441679 5000000000000000000 8405 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7059/50000 : ℝ)) (X := (1620450629441679/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002709614280326727/10000000000000000000 : ℝ) ≤ (1250082521140791/1250000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (10002709614280326727/10000000000000000000 : ℝ)^2048 ≤ (1250082521140791/1250000000000000 : ℝ)^8405 := by
      have hnat : (10002709614280326727 : ℕ)^2048*1250000000000000^8405 ≤ 1250082521140791^8405*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002709614280326727 10000000000000000000 1250082521140791 1250000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250082521140791/1250000000000000 : ℝ)) (X := (10002709614280326727/10000000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009191416798093443/20000000000000000000 : ℝ) ≤ (10001119616357167/10000000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (20009191416798093443/20000000000000000000 : ℝ)^2048 ≤ (10001119616357167/10000000000000000 : ℝ)^8405 := by
      have hnat : (20009191416798093443 : ℕ)^2048*10000000000000000^8405 ≤ 10001119616357167^8405*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009191416798093443 20000000000000000000 10001119616357167 10000000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001119616357167/10000000000000000 : ℝ)) (X := (20009191416798093443/20000000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501620450629441679/2500000000000000000 : ℝ) ≤ (5000789531794003/5000000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (2501620450629441679/2500000000000000000 : ℝ)^2048 ≤ (5000789531794003/5000000000000000 : ℝ)^8405 := by
      have hnat : (2501620450629441679 : ℕ)^2048*5000000000000000^8405 ≤ 5000789531794003^8405*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501620450629441679 2500000000000000000 5000789531794003 5000000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000789531794003/5000000000000000 : ℝ)) (X := (2501620450629441679/2500000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2709614280326727/20000000000000000000 : ℝ) ≤ ((4503549209478068369/4505000000000000000 : ℝ)+2*(459447230839/270300000000000 : ℝ)*(2283/20000 : ℝ))^(8405/2048 : ℝ) := by
    rw [show (4503549209478068369/4505000000000000000 : ℝ)+2*(459447230839/270300000000000 : ℝ)*(2283/20000 : ℝ)=(1250082521140791/1250000000000000 : ℝ) by norm_num, show 1+2*(2709614280326727/20000000000000000000 : ℝ)=(10002709614280326727/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1620450629441679/5000000000000000000 : ℝ)+(2709614280326727/20000000000000000000 : ℝ) ≤ ((4503549209478068369/4505000000000000000 : ℝ)+(459447230839/270300000000000 : ℝ)*((7059/50000 : ℝ)+(2283/20000 : ℝ)))^(8405/2048 : ℝ) := by
    rw [show (4503549209478068369/4505000000000000000 : ℝ)+(459447230839/270300000000000 : ℝ)*((7059/50000 : ℝ)+(2283/20000 : ℝ))=(10001119616357167/10000000000000000 : ℝ) by norm_num, show 1+(1620450629441679/5000000000000000000 : ℝ)+(2709614280326727/20000000000000000000 : ℝ)=(20009191416798093443/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1620450629441679/5000000000000000000 : ℝ) ≤ ((4503549209478068369/4505000000000000000 : ℝ)+2*(459447230839/270300000000000 : ℝ)*(7059/50000 : ℝ))^(8405/2048 : ℝ) := by
    rw [show (4503549209478068369/4505000000000000000 : ℝ)+2*(459447230839/270300000000000 : ℝ)*(7059/50000 : ℝ)=(5000789531794003/5000000000000000 : ℝ) by norm_num, show 1+2*(1620450629441679/5000000000000000000 : ℝ)=(2501620450629441679/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4503549209478068369/4505000000000000000 : ℝ)*(X 1 0+X 2 0)+(459447230839/270300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (2283/20000 : ℝ)) (hi := (7059/50000 : ℝ)) (c := (4503549209478068369/4505000000000000000 : ℝ)) (alpha := (459447230839/270300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4503549209478068369/4505000000000000000 : ℝ)*(X 0 1+X 2 1)+(459447230839/270300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (2283/20000 : ℝ)) (hi := (7059/50000 : ℝ)) (c := (4503549209478068369/4505000000000000000 : ℝ)) (alpha := (459447230839/270300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4503549209478068369/4505000000000000000 : ℝ)*(X 0 2+X 1 2)+(459447230839/270300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (2283/20000 : ℝ)) (hi := (7059/50000 : ℝ)) (c := (4503549209478068369/4505000000000000000 : ℝ)) (alpha := (459447230839/270300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-533342189/2500000000 : ℝ)*X 0 0+(1078393169/2000000000 : ℝ)*X 0 1+(2633298949/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068902689/2000000000 : ℝ)*X 1 0+(-87877739/400000000 : ℝ)*X 1 1+(2633298953/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344513449/10000000000 : ℝ)*X 2 0+(5266597903/10000000000 : ℝ)*X 2 1+(-1098471737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2177377261/5000000000 : ℝ)*X 0 0+(84602083/200000000 : ℝ)*X 0 1+(4482998557/10000000000 : ℝ)*X 0 2+(2177377261/5000000000 : ℝ)*X 1 0+(84602083/200000000 : ℝ)*X 1 1+(4482998557/10000000000 : ℝ)*X 1 2+(2177377261/5000000000 : ℝ)*X 2 0+(84602083/200000000 : ℝ)*X 2 1+(4482998557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-213337353/1000000000 : ℝ)*X 0 0+(5266914847/10000000000 : ℝ)*X 0 1+(5391647741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312588731/10000000000 : ℝ)*X 1 0+(-1035946803/5000000000 : ℝ)*X 1 1+(269582389/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((53125887/100000000 : ℝ)*X 2 0+(5391647807/10000000000 : ℝ)*X 2 1+(-2071893611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4354764171/10000000000 : ℝ)*X 0 0+(448235923/1000000000 : ℝ)*X 0 1+(2115372889/5000000000 : ℝ)*X 0 2+(4354764171/10000000000 : ℝ)*X 1 0+(448235923/1000000000 : ℝ)*X 1 1+(2115372889/5000000000 : ℝ)*X 1 2+(4354764171/10000000000 : ℝ)*X 2 0+(448235923/1000000000 : ℝ)*X 2 1+(2115372889/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41851208114142071408049313/4505000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (362537983/20000000000000 : ℝ)*(base19) + (423848961/25000000000000 : ℝ)*(base23) + (32939311/50000000000000 : ℝ)*(lower2) + (234965113/100000000000000 : ℝ)*(upper3) + (29442401/20000000000000 : ℝ)*(upper5) + (119308940499059/2000000000000 : ℝ)*(major0) + (119308940499059/2000000000000 : ℝ)*(major1) + (119308940499059/2000000000000 : ℝ)*(major2) + (7976572965654169/100000000000000 : ℝ)*(sp0) + (3988310743855129/50000000000000 : ℝ)*(sp1) + (797662160500433/10000000000000 : ℝ)*(sp2) + (1977121834776663/50000000000000 : ℝ)*(sp3) + (12583686501/25000000000000 : ℝ)*(sp4) + (13385143759/50000000000000 : ℝ)*(sp7) + (988567609960211/25000000000000 : ℝ)*(f.failure) + (7976623300400173/100000000000000 : ℝ)*(f.sum) + (2505388086803/675750000000000000000000000 : ℝ)*base65 + (188705139916445687/27030000000000000000000000000000 : ℝ)*base68 + (273159441248184313/27030000000000000000000000000000 : ℝ)*base69 + (34346330154744313/27030000000000000000000000000000 : ℝ)*base71 + (15160979977/135150000000000000000000000 : ℝ)*base73 + (13137075526475687/27030000000000000000000000000000 : ℝ)*base76 + (269546969026055687/27030000000000000000000000000000 : ℝ)*base78 + (267431117659355687/27030000000000000000000000000000 : ℝ)*base80 + (970816108457/168937500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1651209/625000000000000000000 : ℝ)*base89 + (1651209/625000000000000000000 : ℝ)*base91 + (1651209/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (130933014429857068320102501/22525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (512361001/50000000000000 : ℝ)*(base19) + (217408711/20000000000000 : ℝ)*(base23) + (34583693/25000000000000 : ℝ)*(upper3) + (1215557/2500000000000 : ℝ)*(lower4) + (57845443/50000000000000 : ℝ)*(upper5) + (599573938531581/10000000000000 : ℝ)*(major0) + (599573938531581/10000000000000 : ℝ)*(major1) + (599573938531581/10000000000000 : ℝ)*(major2) + (29201150613/100000000000000 : ℝ)*(sp1) + (16063326123/50000000000000 : ℝ)*(sp2) + (8017128470807583/100000000000000 : ℝ)*(sp4) + (1002137280616871/12500000000000 : ℝ)*(sp5) + (4008547628555891/50000000000000 : ℝ)*(sp6) + (993587526516121/25000000000000 : ℝ)*(sp7) + (993587526516121/25000000000000 : ℝ)*(f.failure) + (8017128470807583/100000000000000 : ℝ)*(f.sum) + (343290865733/225250000000000000000000000 : ℝ)*base65 + (56901433759738611/45050000000000000000000000000000 : ℝ)*base68 + (249071058111438611/45050000000000000000000000000000 : ℝ)*base70 + (124749798781538611/45050000000000000000000000000000 : ℝ)*base72 + (3655901171531/901000000000000000000000000 : ℝ)*base74 + (174755110157188611/45050000000000000000000000000000 : ℝ)*base76 + (48614508649588611/45050000000000000000000000000000 : ℝ)*base78 + (722970973125288611/45050000000000000000000000000000 : ℝ)*base80 + (1752586603/11262500000000000000000000 : ℝ)*base82 + (1954501/625000000000000000000 : ℝ)*base90 + (1954501/625000000000000000000 : ℝ)*base92 + (1954501/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1213_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2283/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5719/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1213_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1213_s7_0 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2133387917/10000000000 : ℝ)*x 0 + (5391739639/10000000000 : ℝ)*x 1 + (5266811499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133387917/10000000000 : ℝ)^4203 ≤ (6485208161697/50000000000000 : ℝ)^3179 := by
    have hnat : (2133387917 : ℕ)^4203*50000000000000^3179 ≤ 6485208161697^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133387917 10000000000 6485208161697 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391739639/10000000000 : ℝ)^4203 ≤ (22094545789583/50000000000000 : ℝ)^3179 := by
    have hnat : (5391739639 : ℕ)^4203*50000000000000^3179 ≤ 22094545789583^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391739639 10000000000 22094545789583 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266811499/10000000000 : ℝ)^4203 ≤ (42840492083413/100000000000000 : ℝ)^3179 := by
    have hnat : (5266811499 : ℕ)^4203*100000000000000^3179 ≤ 42840492083413^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266811499 10000000000 42840492083413 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2133387917/10000000000 : ℝ), (5391739639/10000000000 : ℝ), (5266811499/10000000000 : ℝ)] ![(6485208161697/50000000000000 : ℝ), (22094545789583/50000000000000 : ℝ), (42840492083413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2133387917/10000000000 : ℝ)|^4203 ≤ (6485208161697/50000000000000 : ℝ)^3179
        have hw : |(-2133387917/10000000000 : ℝ)|=(2133387917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391739639/10000000000 : ℝ)|^4203 ≤ (22094545789583/50000000000000 : ℝ)^3179
        have hw : |(5391739639/10000000000 : ℝ)|=(5391739639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266811499/10000000000 : ℝ)|^4203 ≤ (42840492083413/100000000000000 : ℝ)^3179
        have hw : |(5266811499/10000000000 : ℝ)|=(5266811499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s7_1 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167014259/312500000 : ℝ)*x 0 + (-2196736507/10000000000 : ℝ)*x 1 + (5266811499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167014259/312500000 : ℝ)^4203 ≤ (43677470750731/100000000000000 : ℝ)^3179 := by
    have hnat : (167014259 : ℕ)^4203*100000000000000^3179 ≤ 43677470750731^3179*312500000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167014259 312500000 43677470750731 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2196736507/10000000000 : ℝ)^4203 ≤ (2696407431857/20000000000000 : ℝ)^3179 := by
    have hnat : (2196736507 : ℕ)^4203*20000000000000^3179 ≤ 2696407431857^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196736507 10000000000 2696407431857 20000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266811499/10000000000 : ℝ)^4203 ≤ (42840492083413/100000000000000 : ℝ)^3179 := by
    have hnat : (5266811499 : ℕ)^4203*100000000000000^3179 ≤ 42840492083413^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266811499 10000000000 42840492083413 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167014259/312500000 : ℝ), (-2196736507/10000000000 : ℝ), (5266811499/10000000000 : ℝ)] ![(43677470750731/100000000000000 : ℝ), (2696407431857/20000000000000 : ℝ), (42840492083413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167014259/312500000 : ℝ)|^4203 ≤ (43677470750731/100000000000000 : ℝ)^3179
        have hw : |(167014259/312500000 : ℝ)|=(167014259/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2196736507/10000000000 : ℝ)|^4203 ≤ (2696407431857/20000000000000 : ℝ)^3179
        have hw : |(-2196736507/10000000000 : ℝ)|=(2196736507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266811499/10000000000 : ℝ)|^4203 ≤ (42840492083413/100000000000000 : ℝ)^3179
        have hw : |(5266811499/10000000000 : ℝ)|=(5266811499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s7_2 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167014259/312500000 : ℝ)*x 0 + (5266811499/10000000000 : ℝ)*x 1 + (-2196736507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167014259/312500000 : ℝ)^4203 ≤ (43677470750731/100000000000000 : ℝ)^3179 := by
    have hnat : (167014259 : ℕ)^4203*100000000000000^3179 ≤ 43677470750731^3179*312500000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167014259 312500000 43677470750731 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266811499/10000000000 : ℝ)^4203 ≤ (42840492083413/100000000000000 : ℝ)^3179 := by
    have hnat : (5266811499 : ℕ)^4203*100000000000000^3179 ≤ 42840492083413^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266811499 10000000000 42840492083413 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2196736507/10000000000 : ℝ)^4203 ≤ (2696407431857/20000000000000 : ℝ)^3179 := by
    have hnat : (2196736507 : ℕ)^4203*20000000000000^3179 ≤ 2696407431857^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196736507 10000000000 2696407431857 20000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167014259/312500000 : ℝ), (5266811499/10000000000 : ℝ), (-2196736507/10000000000 : ℝ)] ![(43677470750731/100000000000000 : ℝ), (42840492083413/100000000000000 : ℝ), (2696407431857/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167014259/312500000 : ℝ)|^4203 ≤ (43677470750731/100000000000000 : ℝ)^3179
        have hw : |(167014259/312500000 : ℝ)|=(167014259/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266811499/10000000000 : ℝ)|^4203 ≤ (42840492083413/100000000000000 : ℝ)^3179
        have hw : |(5266811499/10000000000 : ℝ)|=(5266811499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2196736507/10000000000 : ℝ)|^4203 ≤ (2696407431857/20000000000000 : ℝ)^3179
        have hw : |(-2196736507/10000000000 : ℝ)|=(2196736507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s7_3 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2177382829/5000000000 : ℝ)*x 0 + (423054631/1000000000 : ℝ)*x 1 + (560319193/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177382829/5000000000 : ℝ)^4203 ≤ (33317341448189/100000000000000 : ℝ)^3179 := by
    have hnat : (2177382829 : ℕ)^4203*100000000000000^3179 ≤ 33317341448189^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177382829 5000000000 33317341448189 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423054631/1000000000 : ℝ)^4203 ≤ (32066648285363/100000000000000 : ℝ)^3179 := by
    have hnat : (423054631 : ℕ)^4203*100000000000000^3179 ≤ 32066648285363^3179*1000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423054631 1000000000 32066648285363 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560319193/1250000000 : ℝ)^4203 ≤ (6923202049777/20000000000000 : ℝ)^3179 := by
    have hnat : (560319193 : ℕ)^4203*20000000000000^3179 ≤ 6923202049777^3179*1250000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560319193 1250000000 6923202049777 20000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177382829/5000000000 : ℝ), (423054631/1000000000 : ℝ), (560319193/1250000000 : ℝ)] ![(33317341448189/100000000000000 : ℝ), (32066648285363/100000000000000 : ℝ), (6923202049777/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177382829/5000000000 : ℝ)|^4203 ≤ (33317341448189/100000000000000 : ℝ)^3179
        have hw : |(2177382829/5000000000 : ℝ)|=(2177382829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(423054631/1000000000 : ℝ)|^4203 ≤ (32066648285363/100000000000000 : ℝ)^3179
        have hw : |(423054631/1000000000 : ℝ)|=(423054631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(560319193/1250000000 : ℝ)|^4203 ≤ (6923202049777/20000000000000 : ℝ)^3179
        have hw : |(560319193/1250000000 : ℝ)|=(560319193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s7_4 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1666713/7812500 : ℝ)*x 0 + (526712621/1000000000 : ℝ)*x 1 + (2695711893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1666713/7812500 : ℝ)^4203 ≤ (6485227143657/50000000000000 : ℝ)^3179 := by
    have hnat : (1666713 : ℕ)^4203*50000000000000^3179 ≤ 6485227143657^3179*7812500^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1666713 7812500 6485227143657 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526712621/1000000000 : ℝ)^4203 ≤ (21421938280491/50000000000000 : ℝ)^3179 := by
    have hnat : (526712621 : ℕ)^4203*50000000000000^3179 ≤ 21421938280491^3179*1000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526712621 1000000000 21421938280491 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695711893/5000000000 : ℝ)^4203 ≤ (44185669138467/100000000000000 : ℝ)^3179 := by
    have hnat : (2695711893 : ℕ)^4203*100000000000000^3179 ≤ 44185669138467^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695711893 5000000000 44185669138467 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1666713/7812500 : ℝ), (526712621/1000000000 : ℝ), (2695711893/5000000000 : ℝ)] ![(6485227143657/50000000000000 : ℝ), (21421938280491/50000000000000 : ℝ), (44185669138467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1666713/7812500 : ℝ)|^4203 ≤ (6485227143657/50000000000000 : ℝ)^3179
        have hw : |(-1666713/7812500 : ℝ)|=(1666713/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526712621/1000000000 : ℝ)|^4203 ≤ (21421938280491/50000000000000 : ℝ)^3179
        have hw : |(526712621/1000000000 : ℝ)|=(526712621/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695711893/5000000000 : ℝ)|^4203 ≤ (44185669138467/100000000000000 : ℝ)^3179
        have hw : |(2695711893/5000000000 : ℝ)|=(2695711893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s7_5 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531264351/1000000000 : ℝ)*x 0 + (-259015527/1250000000 : ℝ)*x 1 + (5391423789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531264351/1000000000 : ℝ)^4203 ≤ (10833516303233/25000000000000 : ℝ)^3179 := by
    have hnat : (531264351 : ℕ)^4203*25000000000000^3179 ≤ 10833516303233^3179*1000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531264351 1000000000 10833516303233 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259015527/1250000000 : ℝ)^4203 ≤ (12480265602429/100000000000000 : ℝ)^3179 := by
    have hnat : (259015527 : ℕ)^4203*100000000000000^3179 ≤ 12480265602429^3179*1250000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259015527 1250000000 12480265602429 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391423789/10000000000 : ℝ)^4203 ≤ (44185669170973/100000000000000 : ℝ)^3179 := by
    have hnat : (5391423789 : ℕ)^4203*100000000000000^3179 ≤ 44185669170973^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391423789 10000000000 44185669170973 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531264351/1000000000 : ℝ), (-259015527/1250000000 : ℝ), (5391423789/10000000000 : ℝ)] ![(10833516303233/25000000000000 : ℝ), (12480265602429/100000000000000 : ℝ), (44185669170973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531264351/1000000000 : ℝ)|^4203 ≤ (10833516303233/25000000000000 : ℝ)^3179
        have hw : |(531264351/1000000000 : ℝ)|=(531264351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-259015527/1250000000 : ℝ)|^4203 ≤ (12480265602429/100000000000000 : ℝ)^3179
        have hw : |(-259015527/1250000000 : ℝ)|=(259015527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391423789/10000000000 : ℝ)|^4203 ≤ (44185669170973/100000000000000 : ℝ)^3179
        have hw : |(5391423789/10000000000 : ℝ)|=(5391423789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s7_6 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328160877/2500000000 : ℝ)*x 0 + (539142379/1000000000 : ℝ)*x 1 + (-2072124217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328160877/2500000000 : ℝ)^4203 ≤ (43334065191363/100000000000000 : ℝ)^3179 := by
    have hnat : (1328160877 : ℕ)^4203*100000000000000^3179 ≤ 43334065191363^3179*2500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328160877 2500000000 43334065191363 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539142379/1000000000 : ℝ)^4203 ≤ (2761604323863/6250000000000 : ℝ)^3179 := by
    have hnat : (539142379 : ℕ)^4203*6250000000000^3179 ≤ 2761604323863^3179*1000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539142379 1000000000 2761604323863 6250000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072124217/10000000000 : ℝ)^4203 ≤ (1560033201299/12500000000000 : ℝ)^3179 := by
    have hnat : (2072124217 : ℕ)^4203*12500000000000^3179 ≤ 1560033201299^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072124217 10000000000 1560033201299 12500000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328160877/2500000000 : ℝ), (539142379/1000000000 : ℝ), (-2072124217/10000000000 : ℝ)] ![(43334065191363/100000000000000 : ℝ), (2761604323863/6250000000000 : ℝ), (1560033201299/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328160877/2500000000 : ℝ)|^4203 ≤ (43334065191363/100000000000000 : ℝ)^3179
        have hw : |(1328160877/2500000000 : ℝ)|=(1328160877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539142379/1000000000 : ℝ)|^4203 ≤ (2761604323863/6250000000000 : ℝ)^3179
        have hw : |(539142379/1000000000 : ℝ)|=(539142379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2072124217/10000000000 : ℝ)|^4203 ≤ (1560033201299/12500000000000 : ℝ)^3179
        have hw : |(-2072124217/10000000000 : ℝ)|=(2072124217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s7_7 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (272173449/625000000 : ℝ)*x 0 + (4481918703/10000000000 : ℝ)*x 1 + (4231183449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272173449/625000000 : ℝ)^4203 ≤ (6663487561121/20000000000000 : ℝ)^3179 := by
    have hnat : (272173449 : ℕ)^4203*20000000000000^3179 ≤ 6663487561121^3179*625000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272173449 625000000 6663487561121 20000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481918703/10000000000 : ℝ)^4203 ≤ (1081547773439/3125000000000 : ℝ)^3179 := by
    have hnat : (4481918703 : ℕ)^4203*3125000000000^3179 ≤ 1081547773439^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481918703 10000000000 1081547773439 3125000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231183449/10000000000 : ℝ)^4203 ≤ (1282921337177/4000000000000 : ℝ)^3179 := by
    have hnat : (4231183449 : ℕ)^4203*4000000000000^3179 ≤ 1282921337177^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231183449 10000000000 1282921337177 4000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272173449/625000000 : ℝ), (4481918703/10000000000 : ℝ), (4231183449/10000000000 : ℝ)] ![(6663487561121/20000000000000 : ℝ), (1081547773439/3125000000000 : ℝ), (1282921337177/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272173449/625000000 : ℝ)|^4203 ≤ (6663487561121/20000000000000 : ℝ)^3179
        have hw : |(272173449/625000000 : ℝ)|=(272173449/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4481918703/10000000000 : ℝ)|^4203 ≤ (1081547773439/3125000000000 : ℝ)^3179
        have hw : |(4481918703/10000000000 : ℝ)|=(4481918703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231183449/10000000000 : ℝ)|^4203 ≤ (1282921337177/4000000000000 : ℝ)^3179
        have hw : |(4231183449/10000000000 : ℝ)|=(4231183449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1213_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5719/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11443/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14089/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7047/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5719/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7047/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5719/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7047/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5719/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7047/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5719/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7047/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5719/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7047/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5719/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5719/50000 : ℝ) ^ (8405/2048 : ℝ) ≤ (13660452959334379/100000000000000000000 : ℝ) := by
    have hpowers : (5719/50000 : ℝ)^8405 ≤ (13660452959334379/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5719 : ℕ)^8405*100000000000000000000^2048 ≤ 13660452959334379^2048*50000^8405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5719 50000 13660452959334379 100000000000000000000 8405 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5719/50000 : ℝ)) (X := (13660452959334379/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7047/50000 : ℝ) ^ (8405/2048 : ℝ) ≤ (16091751329810899/50000000000000000000 : ℝ) := by
    have hpowers : (7047/50000 : ℝ)^8405 ≤ (16091751329810899/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7047 : ℕ)^8405*50000000000000000000^2048 ≤ 16091751329810899^2048*50000^8405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7047 50000 16091751329810899 50000000000000000000 8405 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7047/50000 : ℝ)) (X := (16091751329810899/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013660452959334379/50000000000000000000 : ℝ) ≤ (200013312893569/200000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (50013660452959334379/50000000000000000000 : ℝ)^2048 ≤ (200013312893569/200000000000000 : ℝ)^8405 := by
      have hnat : (50013660452959334379 : ℕ)^2048*200000000000000^8405 ≤ 200013312893569^8405*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013660452959334379 50000000000000000000 200013312893569 200000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200013312893569/200000000000000 : ℝ)) (X := (50013660452959334379/50000000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045843955618956177/100000000000000000000 : ℝ) ≤ (10001116860777103/10000000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (100045843955618956177/100000000000000000000 : ℝ)^2048 ≤ (10001116860777103/10000000000000000 : ℝ)^8405 := by
      have hnat : (100045843955618956177 : ℕ)^2048*10000000000000000^8405 ≤ 10001116860777103^8405*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045843955618956177 100000000000000000000 10001116860777103 10000000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001116860777103/10000000000000000 : ℝ)) (X := (100045843955618956177/100000000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016091751329810899/25000000000000000000 : ℝ) ≤ (2500392019218939/2500000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (25016091751329810899/25000000000000000000 : ℝ)^2048 ≤ (2500392019218939/2500000000000000 : ℝ)^8405 := by
      have hnat : (25016091751329810899 : ℕ)^2048*2500000000000000^8405 ≤ 2500392019218939^8405*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016091751329810899 25000000000000000000 2500392019218939 2500000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500392019218939/2500000000000000 : ℝ)) (X := (25016091751329810899/25000000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13660452959334379/100000000000000000000 : ℝ) ≤ ((6637861483198294293/6640000000000000000 : ℝ)+2*(451216098653/265600000000000 : ℝ)*(5719/50000 : ℝ))^(8405/2048 : ℝ) := by
    rw [show (6637861483198294293/6640000000000000000 : ℝ)+2*(451216098653/265600000000000 : ℝ)*(5719/50000 : ℝ)=(200013312893569/200000000000000 : ℝ) by norm_num, show 1+2*(13660452959334379/100000000000000000000 : ℝ)=(50013660452959334379/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16091751329810899/50000000000000000000 : ℝ)+(13660452959334379/100000000000000000000 : ℝ) ≤ ((6637861483198294293/6640000000000000000 : ℝ)+(451216098653/265600000000000 : ℝ)*((7047/50000 : ℝ)+(5719/50000 : ℝ)))^(8405/2048 : ℝ) := by
    rw [show (6637861483198294293/6640000000000000000 : ℝ)+(451216098653/265600000000000 : ℝ)*((7047/50000 : ℝ)+(5719/50000 : ℝ))=(10001116860777103/10000000000000000 : ℝ) by norm_num, show 1+(16091751329810899/50000000000000000000 : ℝ)+(13660452959334379/100000000000000000000 : ℝ)=(100045843955618956177/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16091751329810899/50000000000000000000 : ℝ) ≤ ((6637861483198294293/6640000000000000000 : ℝ)+2*(451216098653/265600000000000 : ℝ)*(7047/50000 : ℝ))^(8405/2048 : ℝ) := by
    rw [show (6637861483198294293/6640000000000000000 : ℝ)+2*(451216098653/265600000000000 : ℝ)*(7047/50000 : ℝ)=(2500392019218939/2500000000000000 : ℝ) by norm_num, show 1+2*(16091751329810899/50000000000000000000 : ℝ)=(25016091751329810899/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6637861483198294293/6640000000000000000 : ℝ)*(X 1 0+X 2 0)+(451216098653/265600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (5719/50000 : ℝ)) (hi := (7047/50000 : ℝ)) (c := (6637861483198294293/6640000000000000000 : ℝ)) (alpha := (451216098653/265600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6637861483198294293/6640000000000000000 : ℝ)*(X 0 1+X 2 1)+(451216098653/265600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (5719/50000 : ℝ)) (hi := (7047/50000 : ℝ)) (c := (6637861483198294293/6640000000000000000 : ℝ)) (alpha := (451216098653/265600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6637861483198294293/6640000000000000000 : ℝ)*(X 0 2+X 1 2)+(451216098653/265600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (5719/50000 : ℝ)) (hi := (7047/50000 : ℝ)) (c := (6637861483198294293/6640000000000000000 : ℝ)) (alpha := (451216098653/265600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2133387917/10000000000 : ℝ)*X 0 0+(5391739639/10000000000 : ℝ)*X 0 1+(5266811499/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167014259/312500000 : ℝ)*X 1 0+(-2196736507/10000000000 : ℝ)*X 1 1+(5266811499/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167014259/312500000 : ℝ)*X 2 0+(5266811499/10000000000 : ℝ)*X 2 1+(-2196736507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2177382829/5000000000 : ℝ)*X 0 0+(423054631/1000000000 : ℝ)*X 0 1+(560319193/1250000000 : ℝ)*X 0 2+(2177382829/5000000000 : ℝ)*X 1 0+(423054631/1000000000 : ℝ)*X 1 1+(560319193/1250000000 : ℝ)*X 1 2+(2177382829/5000000000 : ℝ)*X 2 0+(423054631/1000000000 : ℝ)*X 2 1+(560319193/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1666713/7812500 : ℝ)*X 0 0+(526712621/1000000000 : ℝ)*X 0 1+(2695711893/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531264351/1000000000 : ℝ)*X 1 0+(-259015527/1250000000 : ℝ)*X 1 1+(5391423789/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328160877/2500000000 : ℝ)*X 2 0+(539142379/1000000000 : ℝ)*X 2 1+(-2072124217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((272173449/625000000 : ℝ)*X 0 0+(4481918703/10000000000 : ℝ)*X 0 1+(4231183449/10000000000 : ℝ)*X 0 2+(272173449/625000000 : ℝ)*X 1 0+(4481918703/10000000000 : ℝ)*X 1 1+(4231183449/10000000000 : ℝ)*X 1 2+(272173449/625000000 : ℝ)*X 2 0+(4481918703/10000000000 : ℝ)*X 2 1+(4231183449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1681827167802970671041563893/332000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (481707/48828125000 : ℝ)*(base19) + (918950107/100000000000000 : ℝ)*(base23) + (36120953/100000000000000 : ℝ)*(lower2) + (127665271/100000000000000 : ℝ)*(upper3) + (77954007/100000000000000 : ℝ)*(upper5) + (5986412689840933/100000000000000 : ℝ)*(major0) + (5986412689840933/100000000000000 : ℝ)*(major1) + (5986412689840933/100000000000000 : ℝ)*(major2) + (8004630193448931/100000000000000 : ℝ)*(sp0) + (8004656433825691/100000000000000 : ℝ)*(sp1) + (25014551566911/312500000000 : ℝ)*(sp2) + (396815319538251/10000000000000 : ℝ)*(sp3) + (27226912697/100000000000000 : ℝ)*(sp4) + (7297539783/50000000000000 : ℝ)*(sp7) + (992041947615519/25000000000000 : ℝ)*(f.failure) + (8004657420361627/100000000000000 : ℝ)*(f.sum) + (43602663465489/13280000000000000000000000000 : ℝ)*base65 + (4233588630244920369/664000000000000000000000000000000 : ℝ)*base67 + (2600273943867079631/664000000000000000000000000000000 : ℝ)*base70 + (8925630735875079631/664000000000000000000000000000000 : ℝ)*base72 + (61350789265169/13280000000000000000000000000 : ℝ)*base73 + (14856848863860920369/664000000000000000000000000000000 : ℝ)*base75 + (5165284076796920369/664000000000000000000000000000000 : ℝ)*base77 + (17432777040780920369/664000000000000000000000000000000 : ℝ)*base79 + (43105683800271/13280000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (4366339/625000000000000000000 : ℝ)*base90 + (4366339/625000000000000000000 : ℝ)*base92 + (4366339/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21739737915601739845467/6640000000000000000000000000 : ℝ) := by norm_num
    linear_combination (599681563/100000000000000 : ℝ)*(base19) + (323406301/50000000000000 : ℝ)*(base23) + (13691497/20000000000000 : ℝ)*(upper3) + (11426719/50000000000000 : ℝ)*(lower4) + (67462501/100000000000000 : ℝ)*(upper5) + (3008369708492431/50000000000000 : ℝ)*(major0) + (3008369708492431/50000000000000 : ℝ)*(major1) + (3008369708492431/50000000000000 : ℝ)*(major2) + (4219565651/25000000000000 : ℝ)*(sp1) + (4517766659/25000000000000 : ℝ)*(sp2) + (4022604243851159/50000000000000 : ℝ)*(sp4) + (160903820195163/2000000000000 : ℝ)*(sp5) + (8045189769823081/100000000000000 : ℝ)*(sp6) + (1994135118566083/50000000000000 : ℝ)*(sp7) + (1994135118566083/50000000000000 : ℝ)*(f.failure) + (4022604243851159/50000000000000 : ℝ)*(f.sum) + (25258384923917/6640000000000000000000000000 : ℝ)*base66 + (2698858728108928717/332000000000000000000000000000000 : ℝ)*base68 + (2979204138563071283/332000000000000000000000000000000 : ℝ)*base69 + (1876010463915071283/332000000000000000000000000000000 : ℝ)*base71 + (38056500509357/6640000000000000000000000000 : ℝ)*base74 + (2586455509627071283/332000000000000000000000000000000 : ℝ)*base75 + (2270754150932928717/332000000000000000000000000000000 : ℝ)*base78 + (5640043266676928717/332000000000000000000000000000000 : ℝ)*base80 + (13541165237757/6640000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (11317177/1250000000000000000000 : ℝ)*base89 + (11317177/1250000000000000000000 : ℝ)*base91 + (11317177/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1213_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5719/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11443/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1213_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1213_s8_0 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2133391301/10000000000 : ℝ)*x 0 + (1078338447/2000000000 : ℝ)*x 1 + (5266856733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133391301/10000000000 : ℝ)^4203 ≤ (12970443524303/100000000000000 : ℝ)^3179 := by
    have hnat : (2133391301 : ℕ)^4203*100000000000000^3179 ≤ 12970443524303^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133391301 10000000000 12970443524303 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078338447/2000000000 : ℝ)^4203 ≤ (11047144481669/25000000000000 : ℝ)^3179 := by
    have hnat : (1078338447 : ℕ)^4203*25000000000000^3179 ≤ 11047144481669^3179*2000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078338447 2000000000 11047144481669 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266856733/10000000000 : ℝ)^4203 ≤ (42840978536689/100000000000000 : ℝ)^3179 := by
    have hnat : (5266856733 : ℕ)^4203*100000000000000^3179 ≤ 42840978536689^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266856733 10000000000 42840978536689 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2133391301/10000000000 : ℝ), (1078338447/2000000000 : ℝ), (5266856733/10000000000 : ℝ)] ![(12970443524303/100000000000000 : ℝ), (11047144481669/25000000000000 : ℝ), (42840978536689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2133391301/10000000000 : ℝ)|^4203 ≤ (12970443524303/100000000000000 : ℝ)^3179
        have hw : |(-2133391301/10000000000 : ℝ)|=(2133391301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078338447/2000000000 : ℝ)|^4203 ≤ (11047144481669/25000000000000 : ℝ)^3179
        have hw : |(1078338447/2000000000 : ℝ)|=(1078338447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266856733/10000000000 : ℝ)|^4203 ≤ (42840978536689/100000000000000 : ℝ)^3179
        have hw : |(5266856733/10000000000 : ℝ)|=(5266856733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s8_1 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16701389/31250000 : ℝ)*x 0 + (-1098346143/5000000000 : ℝ)*x 1 + (5266856727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16701389/31250000 : ℝ)^4203 ≤ (5459667895739/12500000000000 : ℝ)^3179 := by
    have hnat : (16701389 : ℕ)^4203*12500000000000^3179 ≤ 5459667895739^3179*31250000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16701389 31250000 5459667895739 12500000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098346143/5000000000 : ℝ)^4203 ≤ (6740839170913/50000000000000 : ℝ)^3179 := by
    have hnat : (1098346143 : ℕ)^4203*50000000000000^3179 ≤ 6740839170913^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098346143 5000000000 6740839170913 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266856727/10000000000 : ℝ)^4203 ≤ (10710244618041/25000000000000 : ℝ)^3179 := by
    have hnat : (5266856727 : ℕ)^4203*25000000000000^3179 ≤ 10710244618041^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266856727 10000000000 10710244618041 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16701389/31250000 : ℝ), (-1098346143/5000000000 : ℝ), (5266856727/10000000000 : ℝ)] ![(5459667895739/12500000000000 : ℝ), (6740839170913/50000000000000 : ℝ), (10710244618041/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16701389/31250000 : ℝ)|^4203 ≤ (5459667895739/12500000000000 : ℝ)^3179
        have hw : |(16701389/31250000 : ℝ)|=(16701389/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1098346143/5000000000 : ℝ)|^4203 ≤ (6740839170913/50000000000000 : ℝ)^3179
        have hw : |(-1098346143/5000000000 : ℝ)|=(1098346143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266856727/10000000000 : ℝ)|^4203 ≤ (10710244618041/25000000000000 : ℝ)^3179
        have hw : |(5266856727/10000000000 : ℝ)|=(5266856727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s8_2 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068888899/2000000000 : ℝ)*x 0 + (2633428359/5000000000 : ℝ)*x 1 + (-2196692279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068888899/2000000000 : ℝ)^4203 ≤ (21838671663993/50000000000000 : ℝ)^3179 := by
    have hnat : (1068888899 : ℕ)^4203*50000000000000^3179 ≤ 21838671663993^3179*2000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068888899 2000000000 21838671663993 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633428359/5000000000 : ℝ)^4203 ≤ (2677561148461/6250000000000 : ℝ)^3179 := by
    have hnat : (2633428359 : ℕ)^4203*6250000000000^3179 ≤ 2677561148461^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633428359 5000000000 2677561148461 6250000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2196692279/10000000000 : ℝ)^4203 ≤ (13481678285027/100000000000000 : ℝ)^3179 := by
    have hnat : (2196692279 : ℕ)^4203*100000000000000^3179 ≤ 13481678285027^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196692279 10000000000 13481678285027 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068888899/2000000000 : ℝ), (2633428359/5000000000 : ℝ), (-2196692279/10000000000 : ℝ)] ![(21838671663993/50000000000000 : ℝ), (2677561148461/6250000000000 : ℝ), (13481678285027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068888899/2000000000 : ℝ)|^4203 ≤ (21838671663993/50000000000000 : ℝ)^3179
        have hw : |(1068888899/2000000000 : ℝ)|=(1068888899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633428359/5000000000 : ℝ)|^4203 ≤ (2677561148461/6250000000000 : ℝ)^3179
        have hw : |(2633428359/5000000000 : ℝ)|=(2633428359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2196692279/10000000000 : ℝ)|^4203 ≤ (13481678285027/100000000000000 : ℝ)^3179
        have hw : |(-2196692279/10000000000 : ℝ)|=(2196692279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s8_3 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4354767987/10000000000 : ℝ)*x 0 + (4230639453/10000000000 : ℝ)*x 1 + (2241229907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354767987/10000000000 : ℝ)^4203 ≤ (33317365006489/100000000000000 : ℝ)^3179 := by
    have hnat : (4354767987 : ℕ)^4203*100000000000000^3179 ≤ 33317365006489^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354767987 10000000000 33317365006489 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4230639453/10000000000 : ℝ)^4203 ≤ (8016895426683/25000000000000 : ℝ)^3179 := by
    have hnat : (4230639453 : ℕ)^4203*25000000000000^3179 ≤ 8016895426683^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230639453 10000000000 8016895426683 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241229907/5000000000 : ℝ)^4203 ≤ (1081720415019/3125000000000 : ℝ)^3179 := by
    have hnat : (2241229907 : ℕ)^4203*3125000000000^3179 ≤ 1081720415019^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241229907 5000000000 1081720415019 3125000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354767987/10000000000 : ℝ), (4230639453/10000000000 : ℝ), (2241229907/5000000000 : ℝ)] ![(33317365006489/100000000000000 : ℝ), (8016895426683/25000000000000 : ℝ), (1081720415019/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354767987/10000000000 : ℝ)|^4203 ≤ (33317365006489/100000000000000 : ℝ)^3179
        have hw : |(4354767987/10000000000 : ℝ)|=(4354767987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4230639453/10000000000 : ℝ)|^4203 ≤ (8016895426683/25000000000000 : ℝ)^3179
        have hw : |(4230639453/10000000000 : ℝ)|=(4230639453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2241229907/5000000000 : ℝ)|^4203 ≤ (1081720415019/3125000000000 : ℝ)^3179
        have hw : |(2241229907/5000000000 : ℝ)|=(2241229907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s8_4 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2133395993/10000000000 : ℝ)*x 0 + (1316792833/2500000000 : ℝ)*x 1 + (2695688257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133395993/10000000000 : ℝ)^4203 ≤ (12970481239061/100000000000000 : ℝ)^3179 := by
    have hnat : (2133395993 : ℕ)^4203*100000000000000^3179 ≤ 12970481239061^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133395993 10000000000 12970481239061 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316792833/2500000000 : ℝ)^4203 ≤ (42844361819131/100000000000000 : ℝ)^3179 := by
    have hnat : (1316792833 : ℕ)^4203*100000000000000^3179 ≤ 42844361819131^3179*2500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316792833 2500000000 42844361819131 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695688257/5000000000 : ℝ)^4203 ≤ (5523144615743/12500000000000 : ℝ)^3179 := by
    have hnat : (2695688257 : ℕ)^4203*12500000000000^3179 ≤ 5523144615743^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695688257 5000000000 5523144615743 12500000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2133395993/10000000000 : ℝ), (1316792833/2500000000 : ℝ), (2695688257/5000000000 : ℝ)] ![(12970481239061/100000000000000 : ℝ), (42844361819131/100000000000000 : ℝ), (5523144615743/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2133395993/10000000000 : ℝ)|^4203 ≤ (12970481239061/100000000000000 : ℝ)^3179
        have hw : |(-2133395993/10000000000 : ℝ)|=(2133395993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316792833/2500000000 : ℝ)|^4203 ≤ (42844361819131/100000000000000 : ℝ)^3179
        have hw : |(1316792833/2500000000 : ℝ)|=(1316792833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695688257/5000000000 : ℝ)|^4203 ≤ (5523144615743/12500000000000 : ℝ)^3179
        have hw : |(2695688257/5000000000 : ℝ)|=(2695688257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s8_5 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312655009/10000000000 : ℝ)*x 0 + (-518043013/2500000000 : ℝ)*x 1 + (5391377189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312655009/10000000000 : ℝ)^4203 ≤ (43334189220401/100000000000000 : ℝ)^3179 := by
    have hnat : (5312655009 : ℕ)^4203*100000000000000^3179 ≤ 43334189220401^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312655009 10000000000 43334189220401 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518043013/2500000000 : ℝ)^4203 ≤ (6240323261039/50000000000000 : ℝ)^3179 := by
    have hnat : (518043013 : ℕ)^4203*50000000000000^3179 ≤ 6240323261039^3179*2500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518043013 2500000000 6240323261039 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391377189/10000000000 : ℝ)^4203 ≤ (883703284797/2000000000000 : ℝ)^3179 := by
    have hnat : (5391377189 : ℕ)^4203*2000000000000^3179 ≤ 883703284797^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391377189 10000000000 883703284797 2000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312655009/10000000000 : ℝ), (-518043013/2500000000 : ℝ), (5391377189/10000000000 : ℝ)] ![(43334189220401/100000000000000 : ℝ), (6240323261039/50000000000000 : ℝ), (883703284797/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312655009/10000000000 : ℝ)|^4203 ≤ (43334189220401/100000000000000 : ℝ)^3179
        have hw : |(5312655009/10000000000 : ℝ)|=(5312655009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-518043013/2500000000 : ℝ)|^4203 ≤ (6240323261039/50000000000000 : ℝ)^3179
        have hw : |(-518043013/2500000000 : ℝ)|=(518043013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391377189/10000000000 : ℝ)|^4203 ≤ (883703284797/2000000000000 : ℝ)^3179
        have hw : |(5391377189/10000000000 : ℝ)|=(5391377189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s8_6 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312655401/10000000000 : ℝ)*x 0 + (1347844171/2500000000 : ℝ)*x 1 + (-2072172209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312655401/10000000000 : ℝ)^4203 ≤ (338548386311/781250000000 : ℝ)^3179 := by
    have hnat : (5312655401 : ℕ)^4203*781250000000^3179 ≤ 338548386311^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312655401 10000000000 338548386311 781250000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347844171/2500000000 : ℝ)^4203 ≤ (8837031753593/20000000000000 : ℝ)^3179 := by
    have hnat : (1347844171 : ℕ)^4203*20000000000000^3179 ≤ 8837031753593^3179*2500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347844171 2500000000 8837031753593 20000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072172209/10000000000 : ℝ)^4203 ≤ (12480647772279/100000000000000 : ℝ)^3179 := by
    have hnat : (2072172209 : ℕ)^4203*100000000000000^3179 ≤ 12480647772279^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072172209 10000000000 12480647772279 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312655401/10000000000 : ℝ), (1347844171/2500000000 : ℝ), (-2072172209/10000000000 : ℝ)] ![(338548386311/781250000000 : ℝ), (8837031753593/20000000000000 : ℝ), (12480647772279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312655401/10000000000 : ℝ)|^4203 ≤ (338548386311/781250000000 : ℝ)^3179
        have hw : |(5312655401/10000000000 : ℝ)|=(5312655401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347844171/2500000000 : ℝ)|^4203 ≤ (8837031753593/20000000000000 : ℝ)^3179
        have hw : |(1347844171/2500000000 : ℝ)|=(1347844171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2072172209/10000000000 : ℝ)|^4203 ≤ (12480647772279/100000000000000 : ℝ)^3179
        have hw : |(-2072172209/10000000000 : ℝ)|=(2072172209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s8_7 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (544347173/1250000000 : ℝ)*x 0 + (4481826107/10000000000 : ℝ)*x 1 + (4231275557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544347173/1250000000 : ℝ)^4203 ≤ (33317460059059/100000000000000 : ℝ)^3179 := by
    have hnat : (544347173 : ℕ)^4203*100000000000000^3179 ≤ 33317460059059^3179*1250000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544347173 1250000000 33317460059059 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481826107/10000000000 : ℝ)^4203 ≤ (34608583402821/100000000000000 : ℝ)^3179 := by
    have hnat : (4481826107 : ℕ)^4203*100000000000000^3179 ≤ 34608583402821^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481826107 10000000000 34608583402821 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231275557/10000000000 : ℝ)^4203 ≤ (6414791304681/20000000000000 : ℝ)^3179 := by
    have hnat : (4231275557 : ℕ)^4203*20000000000000^3179 ≤ 6414791304681^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231275557 10000000000 6414791304681 20000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544347173/1250000000 : ℝ), (4481826107/10000000000 : ℝ), (4231275557/10000000000 : ℝ)] ![(33317460059059/100000000000000 : ℝ), (34608583402821/100000000000000 : ℝ), (6414791304681/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544347173/1250000000 : ℝ)|^4203 ≤ (33317460059059/100000000000000 : ℝ)^3179
        have hw : |(544347173/1250000000 : ℝ)|=(544347173/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4481826107/10000000000 : ℝ)|^4203 ≤ (34608583402821/100000000000000 : ℝ)^3179
        have hw : |(4481826107/10000000000 : ℝ)|=(4481826107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231275557/10000000000 : ℝ)|^4203 ≤ (6414791304681/20000000000000 : ℝ)^3179
        have hw : |(4231275557/10000000000 : ℝ)|=(4231275557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1213_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11443/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2861/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1761/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11443/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11443/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11443/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11443/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11443/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11443/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11443/100000 : ℝ) ^ (8405/2048 : ℝ) ≤ (13684976739326703/100000000000000000000 : ℝ) := by
    have hpowers : (11443/100000 : ℝ)^8405 ≤ (13684976739326703/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11443 : ℕ)^8405*100000000000000000000^2048 ≤ 13684976739326703^2048*100000^8405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11443 100000 13684976739326703 100000000000000000000 8405 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11443/100000 : ℝ)) (X := (13684976739326703/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14089/100000 : ℝ) ^ (8405/2048 : ℝ) ≤ (16068335600390927/50000000000000000000 : ℝ) := by
    have hpowers : (14089/100000 : ℝ)^8405 ≤ (16068335600390927/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14089 : ℕ)^8405*50000000000000000000^2048 ≤ 16068335600390927^2048*100000^8405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14089 100000 16068335600390927 50000000000000000000 8405 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14089/100000 : ℝ)) (X := (16068335600390927/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013684976739326703/50000000000000000000 : ℝ) ≤ (5000333419773089/5000000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (50013684976739326703/50000000000000000000 : ℝ)^2048 ≤ (5000333419773089/5000000000000000 : ℝ)^8405 := by
      have hnat : (50013684976739326703 : ℕ)^2048*5000000000000000^8405 ≤ 5000333419773089^8405*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013684976739326703 50000000000000000000 5000333419773089 5000000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000333419773089/5000000000000000 : ℝ)) (X := (50013684976739326703/50000000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045821647940108557/100000000000000000000 : ℝ) ≤ (10001116317406543/10000000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (100045821647940108557/100000000000000000000 : ℝ)^2048 ≤ (10001116317406543/10000000000000000 : ℝ)^8405 := by
      have hnat : (100045821647940108557 : ℕ)^2048*10000000000000000^8405 ≤ 10001116317406543^8405*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045821647940108557 100000000000000000000 10001116317406543 10000000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001116317406543/10000000000000000 : ℝ)) (X := (100045821647940108557/100000000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016068335600390927/25000000000000000000 : ℝ) ≤ (2500391448816727/2500000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (25016068335600390927/25000000000000000000 : ℝ)^2048 ≤ (2500391448816727/2500000000000000 : ℝ)^8405 := by
      have hnat : (25016068335600390927 : ℕ)^2048*2500000000000000^8405 ≤ 2500391448816727^8405*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016068335600390927 25000000000000000000 2500391448816727 2500000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500391448816727/2500000000000000 : ℝ)) (X := (25016068335600390927/25000000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13684976739326703/100000000000000000000 : ℝ) ≤ ((1469526539284826311/1470000000000000000 : ℝ)+2*(9988396897/5880000000000 : ℝ)*(11443/100000 : ℝ))^(8405/2048 : ℝ) := by
    rw [show (1469526539284826311/1470000000000000000 : ℝ)+2*(9988396897/5880000000000 : ℝ)*(11443/100000 : ℝ)=(5000333419773089/5000000000000000 : ℝ) by norm_num, show 1+2*(13684976739326703/100000000000000000000 : ℝ)=(50013684976739326703/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16068335600390927/50000000000000000000 : ℝ)+(13684976739326703/100000000000000000000 : ℝ) ≤ ((1469526539284826311/1470000000000000000 : ℝ)+(9988396897/5880000000000 : ℝ)*((14089/100000 : ℝ)+(11443/100000 : ℝ)))^(8405/2048 : ℝ) := by
    rw [show (1469526539284826311/1470000000000000000 : ℝ)+(9988396897/5880000000000 : ℝ)*((14089/100000 : ℝ)+(11443/100000 : ℝ))=(10001116317406543/10000000000000000 : ℝ) by norm_num, show 1+(16068335600390927/50000000000000000000 : ℝ)+(13684976739326703/100000000000000000000 : ℝ)=(100045821647940108557/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16068335600390927/50000000000000000000 : ℝ) ≤ ((1469526539284826311/1470000000000000000 : ℝ)+2*(9988396897/5880000000000 : ℝ)*(14089/100000 : ℝ))^(8405/2048 : ℝ) := by
    rw [show (1469526539284826311/1470000000000000000 : ℝ)+2*(9988396897/5880000000000 : ℝ)*(14089/100000 : ℝ)=(2500391448816727/2500000000000000 : ℝ) by norm_num, show 1+2*(16068335600390927/50000000000000000000 : ℝ)=(25016068335600390927/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1469526539284826311/1470000000000000000 : ℝ)*(X 1 0+X 2 0)+(9988396897/5880000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (11443/100000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (1469526539284826311/1470000000000000000 : ℝ)) (alpha := (9988396897/5880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1469526539284826311/1470000000000000000 : ℝ)*(X 0 1+X 2 1)+(9988396897/5880000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (11443/100000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (1469526539284826311/1470000000000000000 : ℝ)) (alpha := (9988396897/5880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1469526539284826311/1470000000000000000 : ℝ)*(X 0 2+X 1 2)+(9988396897/5880000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (11443/100000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (1469526539284826311/1470000000000000000 : ℝ)) (alpha := (9988396897/5880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2133391301/10000000000 : ℝ)*X 0 0+(1078338447/2000000000 : ℝ)*X 0 1+(5266856733/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((16701389/31250000 : ℝ)*X 1 0+(-1098346143/5000000000 : ℝ)*X 1 1+(5266856727/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068888899/2000000000 : ℝ)*X 2 0+(2633428359/5000000000 : ℝ)*X 2 1+(-2196692279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4354767987/10000000000 : ℝ)*X 0 0+(4230639453/10000000000 : ℝ)*X 0 1+(2241229907/5000000000 : ℝ)*X 0 2+(4354767987/10000000000 : ℝ)*X 1 0+(4230639453/10000000000 : ℝ)*X 1 1+(2241229907/5000000000 : ℝ)*X 1 2+(4354767987/10000000000 : ℝ)*X 2 0+(4230639453/10000000000 : ℝ)*X 2 1+(2241229907/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2133395993/10000000000 : ℝ)*X 0 0+(1316792833/2500000000 : ℝ)*X 0 1+(2695688257/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312655009/10000000000 : ℝ)*X 1 0+(-518043013/2500000000 : ℝ)*X 1 1+(5391377189/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312655401/10000000000 : ℝ)*X 2 0+(1347844171/2500000000 : ℝ)*X 2 1+(-2072172209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((544347173/1250000000 : ℝ)*X 0 0+(4481826107/10000000000 : ℝ)*X 0 1+(4231275557/10000000000 : ℝ)*X 0 2+(544347173/1250000000 : ℝ)*X 1 0+(4481826107/10000000000 : ℝ)*X 1 1+(4231275557/10000000000 : ℝ)*X 1 2+(544347173/1250000000 : ℝ)*X 2 0+(4481826107/10000000000 : ℝ)*X 2 1+(4231275557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58901615130729006751415523/12250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (175745027/20000000000000 : ℝ)*(base19) + (420940043/50000000000000 : ℝ)*(base23) + (31707517/100000000000000 : ℝ)*(lower2) + (106997103/100000000000000 : ℝ)*(upper3) + (19908813/25000000000000 : ℝ)*(upper5) + (2995424985312693/50000000000000 : ℝ)*(major0) + (2995424985312693/50000000000000 : ℝ)*(major1) + (2995424985312693/50000000000000 : ℝ)*(major2) + (1001320782673241/12500000000000 : ℝ)*(sp0) + (8010589805265367/100000000000000 : ℝ)*(sp1) + (500661865131901/6250000000000 : ℝ)*(sp2) + (992774101725351/25000000000000 : ℝ)*(sp3) + (12211302287/50000000000000 : ℝ)*(sp4) + (12690082353/100000000000000 : ℝ)*(sp7) + (1985554548491879/50000000000000 : ℝ)*(f.failure) + (4005295341995251/50000000000000 : ℝ)*(f.sum) + (337645645697/49000000000000000000000000 : ℝ)*base65 + (474971791081528159/24500000000000000000000000000000 : ℝ)*base68 + (34415959078528159/24500000000000000000000000000000 : ℝ)*base70 + (13098612707971841/24500000000000000000000000000000 : ℝ)*base71 + (98393926489/24500000000000000000000000 : ℝ)*base73 + (388030475029028159/24500000000000000000000000000000 : ℝ)*base76 + (101910236587971841/24500000000000000000000000000000 : ℝ)*base77 + (242874300561528159/24500000000000000000000000000000 : ℝ)*base80 + (6469690303/4900000000000000000000000 : ℝ)*base82 + (11206501/1250000000000000000000 : ℝ)*base89 + (11206501/1250000000000000000000 : ℝ)*base91 + (11206501/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12161036662077022179058017/3062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (90516409/100000000000000 : ℝ)*(base19) + (671729909/100000000000000 : ℝ)*(base23) + (91787259/20000000000000 : ℝ)*(lower1) + (1324973/100000000000000 : ℝ)*(upper2) + (1178777/1250000000000 : ℝ)*(upper3) + (1505297204577447/25000000000000 : ℝ)*(major0) + (1505297204577447/25000000000000 : ℝ)*(major1) + (1505297204577447/25000000000000 : ℝ)*(major2) + (512852281/20000000000000 : ℝ)*(sp1) + (11240919381/100000000000000 : ℝ)*(sp3) + (322046317054013/4000000000000 : ℝ)*(sp4) + (251598602236641/3125000000000 : ℝ)*(sp5) + (31449833025861/390625000000 : ℝ)*(sp6) + (498901042123103/12500000000000 : ℝ)*(sp7) + (1995609788952103/50000000000000 : ℝ)*(f.failure) + (322046317054013/4000000000000 : ℝ)*(f.sum) + (31084964143/6125000000000000000000000 : ℝ)*base65 + (7758628669730661/12250000000000000000000000000000 : ℝ)*base68 + (42508664565519339/12250000000000000000000000000000 : ℝ)*base69 + (145598835842230661/12250000000000000000000000000000 : ℝ)*base72 + (378811288263/49000000000000000000000000 : ℝ)*base73 + (302030954058730661/12250000000000000000000000000000 : ℝ)*base76 + (670565968490230661/12250000000000000000000000000000 : ℝ)*base78 + (655341374808730661/12250000000000000000000000000000 : ℝ)*base80 + (9086641/12250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4844443/1250000000000000000000 : ℝ)*base90 + (4844443/1250000000000000000000 : ℝ)*base92 + (4844443/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1213_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11443/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2861/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1213_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1213_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2283/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2861/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1213_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1213_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1213_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7059/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2283/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2861/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1213_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
