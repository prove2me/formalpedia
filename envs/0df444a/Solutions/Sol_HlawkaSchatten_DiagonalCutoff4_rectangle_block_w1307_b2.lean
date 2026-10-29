-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1307_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:38:36.953198+00:00
-- url     : https://prove2.me/submissions/3f08f8d2-a387-4103-b0a7-ea5b87c42278

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
theorem support_rectangle_w1307_s6_0 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2074591097/10000000000 : ℝ)*x 0 + (1082907503/2000000000 : ℝ)*x 1 + (104868947/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2074591097/10000000000 : ℝ)^4267 ≤ (2525103324359/20000000000000 : ℝ)^3243 := by
    have hnat : (2074591097 : ℕ)^4267*20000000000000^3243 ≤ 2525103324359^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074591097 10000000000 2525103324359 20000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082907503/2000000000 : ℝ)^4267 ≤ (44609925675501/100000000000000 : ℝ)^3243 := by
    have hnat : (1082907503 : ℕ)^4267*100000000000000^3243 ≤ 44609925675501^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082907503 2000000000 44609925675501 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104868947/200000000 : ℝ)^4267 ≤ (10691139421413/25000000000000 : ℝ)^3243 := by
    have hnat : (104868947 : ℕ)^4267*25000000000000^3243 ≤ 10691139421413^3243*200000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104868947 200000000 10691139421413 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2074591097/10000000000 : ℝ), (1082907503/2000000000 : ℝ), (104868947/200000000 : ℝ)] ![(2525103324359/20000000000000 : ℝ), (44609925675501/100000000000000 : ℝ), (10691139421413/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2074591097/10000000000 : ℝ)|^4267 ≤ (2525103324359/20000000000000 : ℝ)^3243
        have hw : |(-2074591097/10000000000 : ℝ)|=(2074591097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082907503/2000000000 : ℝ)|^4267 ≤ (44609925675501/100000000000000 : ℝ)^3243
        have hw : |(1082907503/2000000000 : ℝ)|=(1082907503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104868947/200000000 : ℝ)|^4267 ≤ (10691139421413/25000000000000 : ℝ)^3243
        have hw : |(104868947/200000000 : ℝ)|=(104868947/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s6_1 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534957877/1000000000 : ℝ)*x 0 + (-2161792313/10000000000 : ℝ)*x 1 + (5243446959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534957877/1000000000 : ℝ)^4267 ≤ (43907083497967/100000000000000 : ℝ)^3243 := by
    have hnat : (534957877 : ℕ)^4267*100000000000000^3243 ≤ 43907083497967^3243*1000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534957877 1000000000 43907083497967 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2161792313/10000000000 : ℝ)^4267 ≤ (13328363001187/100000000000000 : ℝ)^3243 := by
    have hnat : (2161792313 : ℕ)^4267*100000000000000^3243 ≤ 13328363001187^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161792313 10000000000 13328363001187 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243446959/10000000000 : ℝ)^4267 ≤ (21382276744903/50000000000000 : ℝ)^3243 := by
    have hnat : (5243446959 : ℕ)^4267*50000000000000^3243 ≤ 21382276744903^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243446959 10000000000 21382276744903 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534957877/1000000000 : ℝ), (-2161792313/10000000000 : ℝ), (5243446959/10000000000 : ℝ)] ![(43907083497967/100000000000000 : ℝ), (13328363001187/100000000000000 : ℝ), (21382276744903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534957877/1000000000 : ℝ)|^4267 ≤ (43907083497967/100000000000000 : ℝ)^3243
        have hw : |(534957877/1000000000 : ℝ)|=(534957877/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2161792313/10000000000 : ℝ)|^4267 ≤ (13328363001187/100000000000000 : ℝ)^3243
        have hw : |(-2161792313/10000000000 : ℝ)|=(2161792313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243446959/10000000000 : ℝ)|^4267 ≤ (21382276744903/50000000000000 : ℝ)^3243
        have hw : |(5243446959/10000000000 : ℝ)|=(5243446959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s6_2 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349578167/10000000000 : ℝ)*x 0 + (5243447227/10000000000 : ℝ)*x 1 + (-54044819/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349578167/10000000000 : ℝ)^4267 ≤ (43907076986063/100000000000000 : ℝ)^3243 := by
    have hnat : (5349578167 : ℕ)^4267*100000000000000^3243 ≤ 43907076986063^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349578167 10000000000 43907076986063 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243447227/10000000000 : ℝ)^4267 ≤ (42764556365731/100000000000000 : ℝ)^3243 := by
    have hnat : (5243447227 : ℕ)^4267*100000000000000^3243 ≤ 42764556365731^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243447227 10000000000 42764556365731 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54044819/250000000 : ℝ)^4267 ≤ (13328366627339/100000000000000 : ℝ)^3243 := by
    have hnat : (54044819 : ℕ)^4267*100000000000000^3243 ≤ 13328366627339^3243*250000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54044819 250000000 13328366627339 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349578167/10000000000 : ℝ), (5243447227/10000000000 : ℝ), (-54044819/250000000 : ℝ)] ![(43907076986063/100000000000000 : ℝ), (42764556365731/100000000000000 : ℝ), (13328366627339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349578167/10000000000 : ℝ)|^4267 ≤ (43907076986063/100000000000000 : ℝ)^3243
        have hw : |(5349578167/10000000000 : ℝ)|=(5349578167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243447227/10000000000 : ℝ)|^4267 ≤ (42764556365731/100000000000000 : ℝ)^3243
        have hw : |(5243447227/10000000000 : ℝ)|=(5243447227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54044819/250000000 : ℝ)|^4267 ≤ (13328366627339/100000000000000 : ℝ)^3243
        have hw : |(-54044819/250000000 : ℝ)|=(54044819/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s6_3 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083962879/2500000000 : ℝ)*x 0 + (130076597/312500000 : ℝ)*x 1 + (903219847/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083962879/2500000000 : ℝ)^4267 ≤ (33302596642469/100000000000000 : ℝ)^3243 := by
    have hnat : (1083962879 : ℕ)^4267*100000000000000^3243 ≤ 33302596642469^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083962879 2500000000 33302596642469 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130076597/312500000 : ℝ)^4267 ≤ (7890344689971/25000000000000 : ℝ)^3243 := by
    have hnat : (130076597 : ℕ)^4267*25000000000000^3243 ≤ 7890344689971^3243*312500000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130076597 312500000 7890344689971 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903219847/2000000000 : ℝ)^4267 ≤ (3513602457323/10000000000000 : ℝ)^3243 := by
    have hnat : (903219847 : ℕ)^4267*10000000000000^3243 ≤ 3513602457323^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903219847 2000000000 3513602457323 10000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083962879/2500000000 : ℝ), (130076597/312500000 : ℝ), (903219847/2000000000 : ℝ)] ![(33302596642469/100000000000000 : ℝ), (7890344689971/25000000000000 : ℝ), (3513602457323/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083962879/2500000000 : ℝ)|^4267 ≤ (33302596642469/100000000000000 : ℝ)^3243
        have hw : |(1083962879/2500000000 : ℝ)|=(1083962879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130076597/312500000 : ℝ)|^4267 ≤ (7890344689971/25000000000000 : ℝ)^3243
        have hw : |(130076597/312500000 : ℝ)|=(130076597/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(903219847/2000000000 : ℝ)|^4267 ≤ (3513602457323/10000000000000 : ℝ)^3243
        have hw : |(903219847/2000000000 : ℝ)|=(903219847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s6_4 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1037301991/5000000000 : ℝ)*x 0 + (5244058161/10000000000 : ℝ)*x 1 + (2706961663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037301991/5000000000 : ℝ)^4267 ≤ (12625619797439/100000000000000 : ℝ)^3243 := by
    have hnat : (1037301991 : ℕ)^4267*100000000000000^3243 ≤ 12625619797439^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037301991 5000000000 12625619797439 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244058161/10000000000 : ℝ)^4267 ≤ (2138555622893/5000000000000 : ℝ)^3243 := by
    have hnat : (5244058161 : ℕ)^4267*5000000000000^3243 ≤ 2138555622893^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244058161 10000000000 2138555622893 5000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706961663/5000000000 : ℝ)^4267 ≤ (22301633866173/50000000000000 : ℝ)^3243 := by
    have hnat : (2706961663 : ℕ)^4267*50000000000000^3243 ≤ 22301633866173^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706961663 5000000000 22301633866173 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1037301991/5000000000 : ℝ), (5244058161/10000000000 : ℝ), (2706961663/5000000000 : ℝ)] ![(12625619797439/100000000000000 : ℝ), (2138555622893/5000000000000 : ℝ), (22301633866173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1037301991/5000000000 : ℝ)|^4267 ≤ (12625619797439/100000000000000 : ℝ)^3243
        have hw : |(-1037301991/5000000000 : ℝ)|=(1037301991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244058161/10000000000 : ℝ)|^4267 ≤ (2138555622893/5000000000000 : ℝ)^3243
        have hw : |(5244058161/10000000000 : ℝ)|=(5244058161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706961663/5000000000 : ℝ)|^4267 ≤ (22301633866173/50000000000000 : ℝ)^3243
        have hw : |(2706961663/5000000000 : ℝ)|=(2706961663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s6_5 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305692673/10000000000 : ℝ)*x 0 + (-1991316507/10000000000 : ℝ)*x 1 + (216556933/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305692673/10000000000 : ℝ)^4267 ≤ (8686752941821/20000000000000 : ℝ)^3243 := by
    have hnat : (5305692673 : ℕ)^4267*20000000000000^3243 ≤ 8686752941821^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305692673 10000000000 8686752941821 20000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1991316507/10000000000 : ℝ)^4267 ≤ (11962967558671/100000000000000 : ℝ)^3243 := by
    have hnat : (1991316507 : ℕ)^4267*100000000000000^3243 ≤ 11962967558671^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991316507 10000000000 11962967558671 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216556933/400000000 : ℝ)^4267 ≤ (22301633860753/50000000000000 : ℝ)^3243 := by
    have hnat : (216556933 : ℕ)^4267*50000000000000^3243 ≤ 22301633860753^3243*400000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216556933 400000000 22301633860753 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305692673/10000000000 : ℝ), (-1991316507/10000000000 : ℝ), (216556933/400000000 : ℝ)] ![(8686752941821/20000000000000 : ℝ), (11962967558671/100000000000000 : ℝ), (22301633860753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305692673/10000000000 : ℝ)|^4267 ≤ (8686752941821/20000000000000 : ℝ)^3243
        have hw : |(5305692673/10000000000 : ℝ)|=(5305692673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1991316507/10000000000 : ℝ)|^4267 ≤ (11962967558671/100000000000000 : ℝ)^3243
        have hw : |(-1991316507/10000000000 : ℝ)|=(1991316507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216556933/400000000 : ℝ)|^4267 ≤ (22301633860753/50000000000000 : ℝ)^3243
        have hw : |(216556933/400000000 : ℝ)|=(216556933/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s6_6 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305692677/10000000000 : ℝ)*x 0 + (2706961661/5000000000 : ℝ)*x 1 + (-398263301/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305692677/10000000000 : ℝ)^4267 ≤ (43433764752189/100000000000000 : ℝ)^3243 := by
    have hnat : (5305692677 : ℕ)^4267*100000000000000^3243 ≤ 43433764752189^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305692677 10000000000 43433764752189 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706961661/5000000000 : ℝ)^4267 ≤ (22301633844493/50000000000000 : ℝ)^3243 := by
    have hnat : (2706961661 : ℕ)^4267*50000000000000^3243 ≤ 22301633844493^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706961661 5000000000 22301633844493 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398263301/2000000000 : ℝ)^4267 ≤ (5981483771431/50000000000000 : ℝ)^3243 := by
    have hnat : (398263301 : ℕ)^4267*50000000000000^3243 ≤ 5981483771431^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398263301 2000000000 5981483771431 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305692677/10000000000 : ℝ), (2706961661/5000000000 : ℝ), (-398263301/2000000000 : ℝ)] ![(43433764752189/100000000000000 : ℝ), (22301633844493/50000000000000 : ℝ), (5981483771431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305692677/10000000000 : ℝ)|^4267 ≤ (43433764752189/100000000000000 : ℝ)^3243
        have hw : |(5305692677/10000000000 : ℝ)|=(5305692677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706961661/5000000000 : ℝ)|^4267 ≤ (22301633844493/50000000000000 : ℝ)^3243
        have hw : |(2706961661/5000000000 : ℝ)|=(2706961661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-398263301/2000000000 : ℝ)|^4267 ≤ (5981483771431/50000000000000 : ℝ)^3243
        have hw : |(-398263301/2000000000 : ℝ)|=(398263301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s6_7 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083969451/2500000000 : ℝ)*x 0 + (2257417947/5000000000 : ℝ)*x 1 + (4163720649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083969451/2500000000 : ℝ)^4267 ≤ (3330286230931/10000000000000 : ℝ)^3243 := by
    have hnat : (1083969451 : ℕ)^4267*10000000000000^3243 ≤ 3330286230931^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083969451 2500000000 3330286230931 10000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257417947/5000000000 : ℝ)^4267 ≤ (17561546278389/50000000000000 : ℝ)^3243 := by
    have hnat : (2257417947 : ℕ)^4267*50000000000000^3243 ≤ 17561546278389^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257417947 5000000000 17561546278389 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4163720649/10000000000 : ℝ)^4267 ≤ (31574045111107/100000000000000 : ℝ)^3243 := by
    have hnat : (4163720649 : ℕ)^4267*100000000000000^3243 ≤ 31574045111107^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163720649 10000000000 31574045111107 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083969451/2500000000 : ℝ), (2257417947/5000000000 : ℝ), (4163720649/10000000000 : ℝ)] ![(3330286230931/10000000000000 : ℝ), (17561546278389/50000000000000 : ℝ), (31574045111107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083969451/2500000000 : ℝ)|^4267 ≤ (3330286230931/10000000000000 : ℝ)^3243
        have hw : |(1083969451/2500000000 : ℝ)|=(1083969451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2257417947/5000000000 : ℝ)|^4267 ≤ (17561546278389/50000000000000 : ℝ)^3243
        have hw : |(2257417947/5000000000 : ℝ)|=(2257417947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4163720649/10000000000 : ℝ)|^4267 ≤ (31574045111107/100000000000000 : ℝ)^3243
        have hw : |(4163720649/10000000000 : ℝ)|=(4163720649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1307_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1383/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2937/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2939/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5527/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2939/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5527/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2939/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5527/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2939/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5527/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2939/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5527/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2939/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5527/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5527/50000 : ℝ) ^ (2133/512 : ℝ) ≤ (10358267595125891/100000000000000000000 : ℝ) := by
    have hpowers : (5527/50000 : ℝ)^2133 ≤ (10358267595125891/100000000000000000000 : ℝ)^512 := by
      have hnat : (5527 : ℕ)^2133*100000000000000000000^512 ≤ 10358267595125891^512*50000^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5527 50000 10358267595125891 100000000000000000000 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5527/50000 : ℝ)) (X := (10358267595125891/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2939/20000 : ℝ) ^ (2133/512 : ℝ) ≤ (16958424607886321/50000000000000000000 : ℝ) := by
    have hpowers : (2939/20000 : ℝ)^2133 ≤ (16958424607886321/50000000000000000000 : ℝ)^512 := by
      have hnat : (2939 : ℕ)^2133*50000000000000000000^512 ≤ 16958424607886321^512*20000^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2939 20000 16958424607886321 50000000000000000000 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2939/20000 : ℝ)) (X := (16958424607886321/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010358267595125891/50000000000000000000 : ℝ) ≤ (10000497235403541/10000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (50010358267595125891/50000000000000000000 : ℝ)^512 ≤ (10000497235403541/10000000000000000 : ℝ)^2133 := by
      have hnat : (50010358267595125891 : ℕ)^512*10000000000000000^2133 ≤ 10000497235403541^2133*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010358267595125891 50000000000000000000 10000497235403541 10000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000497235403541/10000000000000000 : ℝ)) (X := (50010358267595125891/50000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044275116810898533/100000000000000000000 : ℝ) ≤ (10001062590110329/10000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (100044275116810898533/100000000000000000000 : ℝ)^512 ≤ (10001062590110329/10000000000000000 : ℝ)^2133 := by
      have hnat : (100044275116810898533 : ℕ)^512*10000000000000000^2133 ≤ 10001062590110329^2133*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044275116810898533 100000000000000000000 10001062590110329 10000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001062590110329/10000000000000000 : ℝ)) (X := (100044275116810898533/100000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016958424607886321/25000000000000000000 : ℝ) ≤ (10001627944817117/10000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (25016958424607886321/25000000000000000000 : ℝ)^512 ≤ (10001627944817117/10000000000000000 : ℝ)^2133 := by
      have hnat : (25016958424607886321 : ℕ)^512*10000000000000000^2133 ≤ 10001627944817117^2133*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016958424607886321 25000000000000000000 10001627944817117 10000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001627944817117/10000000000000000 : ℝ)) (X := (25016958424607886321/25000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10358267595125891/100000000000000000000 : ℝ) ≤ ((36399311572246623677/36410000000000000000 : ℝ)+2*(141338676697/91025000000000 : ℝ)*(5527/50000 : ℝ))^(2133/512 : ℝ) := by
    rw [show (36399311572246623677/36410000000000000000 : ℝ)+2*(141338676697/91025000000000 : ℝ)*(5527/50000 : ℝ)=(10000497235403541/10000000000000000 : ℝ) by norm_num, show 1+2*(10358267595125891/100000000000000000000 : ℝ)=(50010358267595125891/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16958424607886321/50000000000000000000 : ℝ)+(10358267595125891/100000000000000000000 : ℝ) ≤ ((36399311572246623677/36410000000000000000 : ℝ)+(141338676697/91025000000000 : ℝ)*((2939/20000 : ℝ)+(5527/50000 : ℝ)))^(2133/512 : ℝ) := by
    rw [show (36399311572246623677/36410000000000000000 : ℝ)+(141338676697/91025000000000 : ℝ)*((2939/20000 : ℝ)+(5527/50000 : ℝ))=(10001062590110329/10000000000000000 : ℝ) by norm_num, show 1+(16958424607886321/50000000000000000000 : ℝ)+(10358267595125891/100000000000000000000 : ℝ)=(100044275116810898533/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16958424607886321/50000000000000000000 : ℝ) ≤ ((36399311572246623677/36410000000000000000 : ℝ)+2*(141338676697/91025000000000 : ℝ)*(2939/20000 : ℝ))^(2133/512 : ℝ) := by
    rw [show (36399311572246623677/36410000000000000000 : ℝ)+2*(141338676697/91025000000000 : ℝ)*(2939/20000 : ℝ)=(10001627944817117/10000000000000000 : ℝ) by norm_num, show 1+2*(16958424607886321/50000000000000000000 : ℝ)=(25016958424607886321/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36399311572246623677/36410000000000000000 : ℝ)*(X 1 0+X 2 0)+(141338676697/91025000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (5527/50000 : ℝ)) (hi := (2939/20000 : ℝ)) (c := (36399311572246623677/36410000000000000000 : ℝ)) (alpha := (141338676697/91025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36399311572246623677/36410000000000000000 : ℝ)*(X 0 1+X 2 1)+(141338676697/91025000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (5527/50000 : ℝ)) (hi := (2939/20000 : ℝ)) (c := (36399311572246623677/36410000000000000000 : ℝ)) (alpha := (141338676697/91025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36399311572246623677/36410000000000000000 : ℝ)*(X 0 2+X 1 2)+(141338676697/91025000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (5527/50000 : ℝ)) (hi := (2939/20000 : ℝ)) (c := (36399311572246623677/36410000000000000000 : ℝ)) (alpha := (141338676697/91025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2074591097/10000000000 : ℝ)*X 0 0+(1082907503/2000000000 : ℝ)*X 0 1+(104868947/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534957877/1000000000 : ℝ)*X 1 0+(-2161792313/10000000000 : ℝ)*X 1 1+(5243446959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349578167/10000000000 : ℝ)*X 2 0+(5243447227/10000000000 : ℝ)*X 2 1+(-54044819/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1083962879/2500000000 : ℝ)*X 0 0+(130076597/312500000 : ℝ)*X 0 1+(903219847/2000000000 : ℝ)*X 0 2+(1083962879/2500000000 : ℝ)*X 1 0+(130076597/312500000 : ℝ)*X 1 1+(903219847/2000000000 : ℝ)*X 1 2+(1083962879/2500000000 : ℝ)*X 2 0+(130076597/312500000 : ℝ)*X 2 1+(903219847/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1037301991/5000000000 : ℝ)*X 0 0+(5244058161/10000000000 : ℝ)*X 0 1+(2706961663/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305692673/10000000000 : ℝ)*X 1 0+(-1991316507/10000000000 : ℝ)*X 1 1+(216556933/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305692677/10000000000 : ℝ)*X 2 0+(2706961661/5000000000 : ℝ)*X 2 1+(-398263301/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1083969451/2500000000 : ℝ)*X 0 0+(2257417947/5000000000 : ℝ)*X 0 1+(4163720649/10000000000 : ℝ)*X 0 2+(1083969451/2500000000 : ℝ)*X 1 0+(2257417947/5000000000 : ℝ)*X 1 1+(4163720649/10000000000 : ℝ)*X 1 2+(1083969451/2500000000 : ℝ)*X 2 0+(2257417947/5000000000 : ℝ)*X 2 1+(4163720649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2502238889139804340622005497/910250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (125377683/20000000000000 : ℝ)*(base19) + (5311593/5000000000000 : ℝ)*(base23) + (29508331/25000000000000 : ℝ)*(lower4) + (75966889/50000000000000 : ℝ)*(lower5) + (2168144826940629/50000000000000 : ℝ)*(major0) + (2168144826940629/50000000000000 : ℝ)*(major1) + (2168144826940629/50000000000000 : ℝ)*(major2) + (22831597507873/390625000000 : ℝ)*(sp0) + (2922446210299513/50000000000000 : ℝ)*(sp1) + (5844882888819963/100000000000000 : ℝ)*(sp2) + (282767847327153/10000000000000 : ℝ)*(sp3) + (4085471953/100000000000000 : ℝ)*(sp4) + (5026217809/50000000000000 : ℝ)*(sp6) + (769537161/10000000000000 : ℝ)*(sp7) + (141384308432157/5000000000000 : ℝ)*(f.failure) + (5844893047487441/100000000000000 : ℝ)*(f.sum) + (15077859167993/9102500000000000000000000000 : ℝ)*base66 + (25706494888716627167/1820500000000000000000000000000000 : ℝ)*base68 + (16976028090669127167/1820500000000000000000000000000000 : ℝ)*base70 + (30882235968220127167/1820500000000000000000000000000000 : ℝ)*base72 + (961705381147/9102500000000000000000000000 : ℝ)*base73 + (10713561715317127167/1820500000000000000000000000000000 : ℝ)*base76 + (6711164708153627167/1820500000000000000000000000000000 : ℝ)*base78 + (13026684797218627167/1820500000000000000000000000000000 : ℝ)*base80 + (32267386133977/9102500000000000000000000000 : ℝ)*base81 + (245187/125000000000000000000 : ℝ)*base89 + (245187/125000000000000000000 : ℝ)*base91 + (245187/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1450342429477221123379185651/165500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (154456071/10000000000000 : ℝ)*(base19) + (1685760689/100000000000000 : ℝ)*(base23) + (88589957/50000000000000 : ℝ)*(upper3) + (6189627/10000000000000 : ℝ)*(lower4) + (22523599/12500000000000 : ℝ)*(upper5) + (4367544358914231/100000000000000 : ℝ)*(major0) + (4367544358914231/100000000000000 : ℝ)*(major1) + (4367544358914231/100000000000000 : ℝ)*(major2) + (15561651801/50000000000000 : ℝ)*(sp1) + (33553988861/100000000000000 : ℝ)*(sp2) + (2943510561924809/50000000000000 : ℝ)*(sp4) + (2943494227992653/50000000000000 : ℝ)*(sp5) + (1471746471025017/25000000000000 : ℝ)*(sp6) + (2848067301865561/100000000000000 : ℝ)*(sp7) + (2848067301865561/100000000000000 : ℝ)*(f.failure) + (2943510561924809/50000000000000 : ℝ)*(f.sum) + (138750795377/413750000000000000000000000 : ℝ)*base65 + (3143004530739304783/331000000000000000000000000000000 : ℝ)*base68 + (1827669953514304783/331000000000000000000000000000000 : ℝ)*base70 + (145343243929304783/331000000000000000000000000000000 : ℝ)*base72 + (1501010892091/827500000000000000000000000 : ℝ)*base74 + (2096361758185695217/331000000000000000000000000000000 : ℝ)*base75 + (1974451675124304783/331000000000000000000000000000000 : ℝ)*base78 + (2114370468565695217/331000000000000000000000000000000 : ℝ)*base79 + (245069310753/1655000000000000000000000000 : ℝ)*base81 + (12715751/2500000000000000000000 : ℝ)*base89 + (12715751/2500000000000000000000 : ℝ)*base91 + (12715751/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1307_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1383/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1307_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1307_s7_0 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2074600089/10000000000 : ℝ)*x 0 + (169201521/312500000 : ℝ)*x 1 + (1310882597/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2074600089/10000000000 : ℝ)^4267 ≤ (315639715613/2500000000000 : ℝ)^3243 := by
    have hnat : (2074600089 : ℕ)^4267*2500000000000^3243 ≤ 315639715613^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074600089 10000000000 315639715613 2500000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169201521/312500000 : ℝ)^4267 ≤ (11152240645797/25000000000000 : ℝ)^3243 := by
    have hnat : (169201521 : ℕ)^4267*25000000000000^3243 ≤ 11152240645797^3243*312500000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169201521 312500000 11152240645797 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310882597/2500000000 : ℝ)^4267 ≤ (2672840548371/6250000000000 : ℝ)^3243 := by
    have hnat : (1310882597 : ℕ)^4267*6250000000000^3243 ≤ 2672840548371^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310882597 2500000000 2672840548371 6250000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2074600089/10000000000 : ℝ), (169201521/312500000 : ℝ), (1310882597/2500000000 : ℝ)] ![(315639715613/2500000000000 : ℝ), (11152240645797/25000000000000 : ℝ), (2672840548371/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2074600089/10000000000 : ℝ)|^4267 ≤ (315639715613/2500000000000 : ℝ)^3243
        have hw : |(-2074600089/10000000000 : ℝ)|=(2074600089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169201521/312500000 : ℝ)|^4267 ≤ (11152240645797/25000000000000 : ℝ)^3243
        have hw : |(169201521/312500000 : ℝ)|=(169201521/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310882597/2500000000 : ℝ)|^4267 ≤ (2672840548371/6250000000000 : ℝ)^3243
        have hw : |(1310882597/2500000000 : ℝ)|=(1310882597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s7_1 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674778633/5000000000 : ℝ)*x 0 + (-540428519/2500000000 : ℝ)*x 1 + (2621763871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674778633/5000000000 : ℝ)^4267 ≤ (2744178204537/6250000000000 : ℝ)^3243 := by
    have hnat : (2674778633 : ℕ)^4267*6250000000000^3243 ≤ 2744178204537^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674778633 5000000000 2744178204537 6250000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540428519/2500000000 : ℝ)^4267 ≤ (416491510337/3125000000000 : ℝ)^3243 := by
    have hnat : (540428519 : ℕ)^4267*3125000000000^3243 ≤ 416491510337^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540428519 2500000000 416491510337 3125000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621763871/5000000000 : ℝ)^4267 ≤ (21382710189701/50000000000000 : ℝ)^3243 := by
    have hnat : (2621763871 : ℕ)^4267*50000000000000^3243 ≤ 21382710189701^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621763871 5000000000 21382710189701 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674778633/5000000000 : ℝ), (-540428519/2500000000 : ℝ), (2621763871/5000000000 : ℝ)] ![(2744178204537/6250000000000 : ℝ), (416491510337/3125000000000 : ℝ), (21382710189701/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674778633/5000000000 : ℝ)|^4267 ≤ (2744178204537/6250000000000 : ℝ)^3243
        have hw : |(2674778633/5000000000 : ℝ)|=(2674778633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-540428519/2500000000 : ℝ)|^4267 ≤ (416491510337/3125000000000 : ℝ)^3243
        have hw : |(-540428519/2500000000 : ℝ)|=(540428519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621763871/5000000000 : ℝ)|^4267 ≤ (21382710189701/50000000000000 : ℝ)^3243
        have hw : |(2621763871/5000000000 : ℝ)|=(2621763871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s7_2 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349555559/10000000000 : ℝ)*x 0 + (209741231/400000000 : ℝ)*x 1 + (-135107021/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349555559/10000000000 : ℝ)^4267 ≤ (2195341641921/5000000000000 : ℝ)^3243 := by
    have hnat : (5349555559 : ℕ)^4267*5000000000000^3243 ≤ 2195341641921^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349555559 10000000000 2195341641921 5000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209741231/400000000 : ℝ)^4267 ≤ (21382726463439/50000000000000 : ℝ)^3243 := by
    have hnat : (209741231 : ℕ)^4267*50000000000000^3243 ≤ 21382726463439^3243*400000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209741231 400000000 21382726463439 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135107021/625000000 : ℝ)^4267 ≤ (13327714215723/100000000000000 : ℝ)^3243 := by
    have hnat : (135107021 : ℕ)^4267*100000000000000^3243 ≤ 13327714215723^3243*625000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135107021 625000000 13327714215723 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349555559/10000000000 : ℝ), (209741231/400000000 : ℝ), (-135107021/625000000 : ℝ)] ![(2195341641921/5000000000000 : ℝ), (21382726463439/50000000000000 : ℝ), (13327714215723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349555559/10000000000 : ℝ)|^4267 ≤ (2195341641921/5000000000000 : ℝ)^3243
        have hw : |(5349555559/10000000000 : ℝ)|=(5349555559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209741231/400000000 : ℝ)|^4267 ≤ (21382726463439/50000000000000 : ℝ)^3243
        have hw : |(209741231/400000000 : ℝ)|=(209741231/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-135107021/625000000 : ℝ)|^4267 ≤ (13327714215723/100000000000000 : ℝ)^3243
        have hw : |(-135107021/625000000 : ℝ)|=(135107021/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s7_3 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2167929589/5000000000 : ℝ)*x 0 + (4162623191/10000000000 : ℝ)*x 1 + (4515923957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167929589/5000000000 : ℝ)^4267 ≤ (832566851867/2500000000000 : ℝ)^3243 := by
    have hnat : (2167929589 : ℕ)^4267*2500000000000^3243 ≤ 832566851867^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167929589 5000000000 832566851867 2500000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4162623191/10000000000 : ℝ)^4267 ≤ (15781547807041/50000000000000 : ℝ)^3243 := by
    have hnat : (4162623191 : ℕ)^4267*50000000000000^3243 ≤ 15781547807041^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162623191 10000000000 15781547807041 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4515923957/10000000000 : ℝ)^4267 ≤ (17567115147913/50000000000000 : ℝ)^3243 := by
    have hnat : (4515923957 : ℕ)^4267*50000000000000^3243 ≤ 17567115147913^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515923957 10000000000 17567115147913 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2167929589/5000000000 : ℝ), (4162623191/10000000000 : ℝ), (4515923957/10000000000 : ℝ)] ![(832566851867/2500000000000 : ℝ), (15781547807041/50000000000000 : ℝ), (17567115147913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2167929589/5000000000 : ℝ)|^4267 ≤ (832566851867/2500000000000 : ℝ)^3243
        have hw : |(2167929589/5000000000 : ℝ)|=(2167929589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4162623191/10000000000 : ℝ)|^4267 ≤ (15781547807041/50000000000000 : ℝ)^3243
        have hw : |(4162623191/10000000000 : ℝ)|=(4162623191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4515923957/10000000000 : ℝ)|^4267 ≤ (17567115147913/50000000000000 : ℝ)^3243
        have hw : |(4515923957/10000000000 : ℝ)|=(4515923957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s7_4 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2074612481/10000000000 : ℝ)*x 0 + (5244138847/10000000000 : ℝ)*x 1 + (5413837169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2074612481/10000000000 : ℝ)^4267 ≤ (6312843926319/50000000000000 : ℝ)^3243 := by
    have hnat : (2074612481 : ℕ)^4267*50000000000000^3243 ≤ 6312843926319^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074612481 10000000000 6312843926319 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244138847/10000000000 : ℝ)^4267 ≤ (8554395667681/20000000000000 : ℝ)^3243 := by
    have hnat : (5244138847 : ℕ)^4267*20000000000000^3243 ≤ 8554395667681^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244138847 10000000000 8554395667681 20000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413837169/10000000000 : ℝ)^4267 ≤ (44602333790687/100000000000000 : ℝ)^3243 := by
    have hnat : (5413837169 : ℕ)^4267*100000000000000^3243 ≤ 44602333790687^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413837169 10000000000 44602333790687 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2074612481/10000000000 : ℝ), (5244138847/10000000000 : ℝ), (5413837169/10000000000 : ℝ)] ![(6312843926319/50000000000000 : ℝ), (8554395667681/20000000000000 : ℝ), (44602333790687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2074612481/10000000000 : ℝ)|^4267 ≤ (6312843926319/50000000000000 : ℝ)^3243
        have hw : |(-2074612481/10000000000 : ℝ)|=(2074612481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244138847/10000000000 : ℝ)|^4267 ≤ (8554395667681/20000000000000 : ℝ)^3243
        have hw : |(5244138847/10000000000 : ℝ)|=(5244138847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413837169/10000000000 : ℝ)|^4267 ≤ (44602333790687/100000000000000 : ℝ)^3243
        have hw : |(5413837169/10000000000 : ℝ)|=(5413837169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s7_5 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305714293/10000000000 : ℝ)*x 0 + (-1991405113/10000000000 : ℝ)*x 1 + (541383723/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305714293/10000000000 : ℝ)^4267 ≤ (43433997580983/100000000000000 : ℝ)^3243 := by
    have hnat : (5305714293 : ℕ)^4267*100000000000000^3243 ≤ 43433997580983^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305714293 10000000000 43433997580983 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1991405113/10000000000 : ℝ)^4267 ≤ (11963667949591/100000000000000 : ℝ)^3243 := by
    have hnat : (1991405113 : ℕ)^4267*100000000000000^3243 ≤ 11963667949591^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991405113 10000000000 11963667949591 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541383723/1000000000 : ℝ)^4267 ≤ (1784093378077/4000000000000 : ℝ)^3243 := by
    have hnat : (541383723 : ℕ)^4267*4000000000000^3243 ≤ 1784093378077^3243*1000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541383723 1000000000 1784093378077 4000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305714293/10000000000 : ℝ), (-1991405113/10000000000 : ℝ), (541383723/1000000000 : ℝ)] ![(43433997580983/100000000000000 : ℝ), (11963667949591/100000000000000 : ℝ), (1784093378077/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305714293/10000000000 : ℝ)|^4267 ≤ (43433997580983/100000000000000 : ℝ)^3243
        have hw : |(5305714293/10000000000 : ℝ)|=(5305714293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1991405113/10000000000 : ℝ)|^4267 ≤ (11963667949591/100000000000000 : ℝ)^3243
        have hw : |(-1991405113/10000000000 : ℝ)|=(1991405113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541383723/1000000000 : ℝ)|^4267 ≤ (1784093378077/4000000000000 : ℝ)^3243
        have hw : |(541383723/1000000000 : ℝ)|=(541383723/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s7_6 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652857131/5000000000 : ℝ)*x 0 + (541383717/1000000000 : ℝ)*x 1 + (-1991405239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652857131/5000000000 : ℝ)^4267 ≤ (21716998623539/50000000000000 : ℝ)^3243 := by
    have hnat : (2652857131 : ℕ)^4267*50000000000000^3243 ≤ 21716998623539^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652857131 5000000000 21716998623539 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541383717/1000000000 : ℝ)^4267 ≤ (44602333801527/100000000000000 : ℝ)^3243 := by
    have hnat : (541383717 : ℕ)^4267*100000000000000^3243 ≤ 44602333801527^3243*1000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541383717 1000000000 44602333801527 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1991405239/10000000000 : ℝ)^4267 ≤ (2990917236393/25000000000000 : ℝ)^3243 := by
    have hnat : (1991405239 : ℕ)^4267*25000000000000^3243 ≤ 2990917236393^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991405239 10000000000 2990917236393 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652857131/5000000000 : ℝ), (541383717/1000000000 : ℝ), (-1991405239/10000000000 : ℝ)] ![(21716998623539/50000000000000 : ℝ), (44602333801527/100000000000000 : ℝ), (2990917236393/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652857131/5000000000 : ℝ)|^4267 ≤ (21716998623539/50000000000000 : ℝ)^3243
        have hw : |(2652857131/5000000000 : ℝ)|=(2652857131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541383717/1000000000 : ℝ)|^4267 ≤ (44602333801527/100000000000000 : ℝ)^3243
        have hw : |(541383717/1000000000 : ℝ)|=(541383717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1991405239/10000000000 : ℝ)|^4267 ≤ (2990917236393/25000000000000 : ℝ)^3243
        have hw : |(-1991405239/10000000000 : ℝ)|=(1991405239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s7_7 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083970939/2500000000 : ℝ)*x 0 + (4514662843/10000000000 : ℝ)*x 1 + (4163892151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083970939/2500000000 : ℝ)^4267 ≤ (8325730615091/25000000000000 : ℝ)^3243 := by
    have hnat : (1083970939 : ℕ)^4267*25000000000000^3243 ≤ 8325730615091^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083970939 2500000000 8325730615091 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514662843/10000000000 : ℝ)^4267 ≤ (2195082577061/6250000000000 : ℝ)^3243 := by
    have hnat : (4514662843 : ℕ)^4267*6250000000000^3243 ≤ 2195082577061^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514662843 10000000000 2195082577061 6250000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4163892151/10000000000 : ℝ)^4267 ≤ (15787878146839/50000000000000 : ℝ)^3243 := by
    have hnat : (4163892151 : ℕ)^4267*50000000000000^3243 ≤ 15787878146839^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163892151 10000000000 15787878146839 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083970939/2500000000 : ℝ), (4514662843/10000000000 : ℝ), (4163892151/10000000000 : ℝ)] ![(8325730615091/25000000000000 : ℝ), (2195082577061/6250000000000 : ℝ), (15787878146839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083970939/2500000000 : ℝ)|^4267 ≤ (8325730615091/25000000000000 : ℝ)^3243
        have hw : |(1083970939/2500000000 : ℝ)|=(1083970939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514662843/10000000000 : ℝ)|^4267 ≤ (2195082577061/6250000000000 : ℝ)^3243
        have hw : |(4514662843/10000000000 : ℝ)|=(4514662843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4163892151/10000000000 : ℝ)|^4267 ≤ (15787878146839/50000000000000 : ℝ)^3243
        have hw : |(4163892151/10000000000 : ℝ)|=(4163892151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1307_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1383/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2213/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14683/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2937/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1383/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2937/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1383/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2937/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1383/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2937/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1383/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2937/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1383/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2937/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1383/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1383/12500 : ℝ) ^ (2133/512 : ℝ) ≤ (10397361626811357/100000000000000000000 : ℝ) := by
    have hpowers : (1383/12500 : ℝ)^2133 ≤ (10397361626811357/100000000000000000000 : ℝ)^512 := by
      have hnat : (1383 : ℕ)^2133*100000000000000000000^512 ≤ 10397361626811357^512*12500^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1383 12500 10397361626811357 100000000000000000000 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1383/12500 : ℝ)) (X := (10397361626811357/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2937/20000 : ℝ) ^ (2133/512 : ℝ) ≤ (16910399433944589/50000000000000000000 : ℝ) := by
    have hpowers : (2937/20000 : ℝ)^2133 ≤ (16910399433944589/50000000000000000000 : ℝ)^512 := by
      have hnat : (2937 : ℕ)^2133*50000000000000000000^512 ≤ 16910399433944589^512*20000^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2937 20000 16910399433944589 50000000000000000000 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2937/20000 : ℝ)) (X := (16910399433944589/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010397361626811357/50000000000000000000 : ℝ) ≤ (10000499111914329/10000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (50010397361626811357/50000000000000000000 : ℝ)^512 ≤ (10000499111914329/10000000000000000 : ℝ)^2133 := by
      have hnat : (50010397361626811357 : ℕ)^512*10000000000000000^2133 ≤ 10000499111914329^2133*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010397361626811357 50000000000000000000 10000499111914329 10000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000499111914329/10000000000000000 : ℝ)) (X := (50010397361626811357/50000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008843632098940107/20000000000000000000 : ℝ) ≤ (5000530611702331/5000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (20008843632098940107/20000000000000000000 : ℝ)^512 ≤ (5000530611702331/5000000000000000 : ℝ)^2133 := by
      have hnat : (20008843632098940107 : ℕ)^512*5000000000000000^2133 ≤ 5000530611702331^2133*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008843632098940107 20000000000000000000 5000530611702331 5000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000530611702331/5000000000000000 : ℝ)) (X := (20008843632098940107/20000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016910399433944589/25000000000000000000 : ℝ) ≤ (2000324666978999/2000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (25016910399433944589/25000000000000000000 : ℝ)^512 ≤ (2000324666978999/2000000000000000 : ℝ)^2133 := by
      have hnat : (25016910399433944589 : ℕ)^512*2000000000000000^2133 ≤ 2000324666978999^2133*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016910399433944589 25000000000000000000 2000324666978999 2000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000324666978999/2000000000000000 : ℝ)) (X := (25016910399433944589/25000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10397361626811357/100000000000000000000 : ℝ) ≤ ((2413291258745579779/2414000000000000000 : ℝ)+2*(562111490333/362100000000000 : ℝ)*(1383/12500 : ℝ))^(2133/512 : ℝ) := by
    rw [show (2413291258745579779/2414000000000000000 : ℝ)+2*(562111490333/362100000000000 : ℝ)*(1383/12500 : ℝ)=(10000499111914329/10000000000000000 : ℝ) by norm_num, show 1+2*(10397361626811357/100000000000000000000 : ℝ)=(50010397361626811357/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16910399433944589/50000000000000000000 : ℝ)+(10397361626811357/100000000000000000000 : ℝ) ≤ ((2413291258745579779/2414000000000000000 : ℝ)+(562111490333/362100000000000 : ℝ)*((2937/20000 : ℝ)+(1383/12500 : ℝ)))^(2133/512 : ℝ) := by
    rw [show (2413291258745579779/2414000000000000000 : ℝ)+(562111490333/362100000000000 : ℝ)*((2937/20000 : ℝ)+(1383/12500 : ℝ))=(5000530611702331/5000000000000000 : ℝ) by norm_num, show 1+(16910399433944589/50000000000000000000 : ℝ)+(10397361626811357/100000000000000000000 : ℝ)=(20008843632098940107/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16910399433944589/50000000000000000000 : ℝ) ≤ ((2413291258745579779/2414000000000000000 : ℝ)+2*(562111490333/362100000000000 : ℝ)*(2937/20000 : ℝ))^(2133/512 : ℝ) := by
    rw [show (2413291258745579779/2414000000000000000 : ℝ)+2*(562111490333/362100000000000 : ℝ)*(2937/20000 : ℝ)=(2000324666978999/2000000000000000 : ℝ) by norm_num, show 1+2*(16910399433944589/50000000000000000000 : ℝ)=(25016910399433944589/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2413291258745579779/2414000000000000000 : ℝ)*(X 1 0+X 2 0)+(562111490333/362100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (1383/12500 : ℝ)) (hi := (2937/20000 : ℝ)) (c := (2413291258745579779/2414000000000000000 : ℝ)) (alpha := (562111490333/362100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2413291258745579779/2414000000000000000 : ℝ)*(X 0 1+X 2 1)+(562111490333/362100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (1383/12500 : ℝ)) (hi := (2937/20000 : ℝ)) (c := (2413291258745579779/2414000000000000000 : ℝ)) (alpha := (562111490333/362100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2413291258745579779/2414000000000000000 : ℝ)*(X 0 2+X 1 2)+(562111490333/362100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (1383/12500 : ℝ)) (hi := (2937/20000 : ℝ)) (c := (2413291258745579779/2414000000000000000 : ℝ)) (alpha := (562111490333/362100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2074600089/10000000000 : ℝ)*X 0 0+(169201521/312500000 : ℝ)*X 0 1+(1310882597/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674778633/5000000000 : ℝ)*X 1 0+(-540428519/2500000000 : ℝ)*X 1 1+(2621763871/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349555559/10000000000 : ℝ)*X 2 0+(209741231/400000000 : ℝ)*X 2 1+(-135107021/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2167929589/5000000000 : ℝ)*X 0 0+(4162623191/10000000000 : ℝ)*X 0 1+(4515923957/10000000000 : ℝ)*X 0 2+(2167929589/5000000000 : ℝ)*X 1 0+(4162623191/10000000000 : ℝ)*X 1 1+(4515923957/10000000000 : ℝ)*X 1 2+(2167929589/5000000000 : ℝ)*X 2 0+(4162623191/10000000000 : ℝ)*X 2 1+(4515923957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2074612481/10000000000 : ℝ)*X 0 0+(5244138847/10000000000 : ℝ)*X 0 1+(5413837169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305714293/10000000000 : ℝ)*X 1 0+(-1991405113/10000000000 : ℝ)*X 1 1+(541383723/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652857131/5000000000 : ℝ)*X 2 0+(541383717/1000000000 : ℝ)*X 2 1+(-1991405239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1083970939/2500000000 : ℝ)*X 0 0+(4514662843/10000000000 : ℝ)*X 0 1+(4163892151/10000000000 : ℝ)*X 0 2+(1083970939/2500000000 : ℝ)*X 1 0+(4514662843/10000000000 : ℝ)*X 1 1+(4163892151/10000000000 : ℝ)*X 1 2+(1083970939/2500000000 : ℝ)*X 2 0+(4514662843/10000000000 : ℝ)*X 2 1+(4163892151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (931279148952153698458206073/120700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3399103199/100000000000000 : ℝ)*(base19) + (193955887/20000000000000 : ℝ)*(base23) + (362195323/100000000000000 : ℝ)*(lower2) + (791701877/100000000000000 : ℝ)*(upper5) + (4340643170355643/100000000000000 : ℝ)*(major0) + (4340643170355643/100000000000000 : ℝ)*(major1) + (4340643170355643/100000000000000 : ℝ)*(major2) + (1462685743126431/25000000000000 : ℝ)*(sp0) + (1170148721065719/20000000000000 : ℝ)*(sp1) + (365672501584691/6250000000000 : ℝ)*(sp2) + (1415247410099621/50000000000000 : ℝ)*(sp3) + (563207149/3125000000000 : ℝ)*(sp4) + (13990702697/100000000000000 : ℝ)*(sp5) + (756704729/2500000000000 : ℝ)*(sp7) + (1415262544194201/50000000000000 : ℝ)*(f.failure) + (5850760995134491/100000000000000 : ℝ)*(f.sum) + (33334277697959/18105000000000000000000000000 : ℝ)*base65 + (4835520698688791309/724200000000000000000000000000000 : ℝ)*base68 + (10572408837123191309/724200000000000000000000000000000 : ℝ)*base70 + (3258825338092991309/724200000000000000000000000000000 : ℝ)*base72 + (22656422620793/9052500000000000000000000000 : ℝ)*base74 + (4926091633246391309/724200000000000000000000000000000 : ℝ)*base76 + (3611646028067591309/724200000000000000000000000000000 : ℝ)*base78 + (4317789666787991309/724200000000000000000000000000000 : ℝ)*base80 + (1524867443371/18105000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (3849991/1250000000000000000000 : ℝ)*base89 + (3849991/1250000000000000000000 : ℝ)*base91 + (3849991/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (506969187420566660379/71000000000000000000000000 : ℝ) := by norm_num
    linear_combination (620458637/50000000000000 : ℝ)*(base19) + (1330028491/100000000000000 : ℝ)*(base23) + (422522937/100000000000000 : ℝ)*(lower1) + (36505577/20000000000000 : ℝ)*(upper3) + (64877317/100000000000000 : ℝ)*(lower4) + (21648453/20000000000000 : ℝ)*(upper5) + (218590866954871/5000000000000 : ℝ)*(major0) + (218590866954871/5000000000000 : ℝ)*(major1) + (218590866954871/5000000000000 : ℝ)*(major2) + (30571671/20000000000000 : ℝ)*(sp2) + (1178556147226271/20000000000000 : ℝ)*(sp4) + (5892779495214081/100000000000000 : ℝ)*(sp5) + (589277925324451/10000000000000 : ℝ)*(sp6) + (1425426852024879/50000000000000 : ℝ)*(sp7) + (1425426852024879/50000000000000 : ℝ)*(f.failure) + (1178556147226271/20000000000000 : ℝ)*(f.sum) + (829218489307/213000000000000000000000000 : ℝ)*base65 + (41234650666690031/2130000000000000000000000000000 : ℝ)*base67 + (8437349928070031/2130000000000000000000000000000 : ℝ)*base69 + (282712365680569969/2130000000000000000000000000000 : ℝ)*base72 + (670904844583/213000000000000000000000000 : ℝ)*base73 + (7692504554479969/2130000000000000000000000000000 : ℝ)*base76 + (5788706302270031/2130000000000000000000000000000 : ℝ)*base77 + (11471270951509969/2130000000000000000000000000000 : ℝ)*base80 + (354593856343/53250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (12097711/1250000000000000000000 : ℝ)*base90 + (12097711/1250000000000000000000 : ℝ)*base92 + (12097711/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1307_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1383/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2213/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1307_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1307_s8_0 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-414920809/2000000000 : ℝ)*x 0 + (2707217829/5000000000 : ℝ)*x 1 + (655442573/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414920809/2000000000 : ℝ)^4267 ≤ (12625620301907/100000000000000 : ℝ)^3243 := by
    have hnat : (414920809 : ℕ)^4267*100000000000000^3243 ≤ 12625620301907^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414920809 2000000000 12625620301907 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707217829/5000000000 : ℝ)^4267 ≤ (22304410753419/50000000000000 : ℝ)^3243 := by
    have hnat : (2707217829 : ℕ)^4267*50000000000000^3243 ≤ 22304410753419^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707217829 5000000000 22304410753419 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655442573/1250000000 : ℝ)^4267 ≤ (1069138954711/2500000000000 : ℝ)^3243 := by
    have hnat : (655442573 : ℕ)^4267*2500000000000^3243 ≤ 1069138954711^3243*1250000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655442573 1250000000 1069138954711 2500000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-414920809/2000000000 : ℝ), (2707217829/5000000000 : ℝ), (655442573/1250000000 : ℝ)] ![(12625620301907/100000000000000 : ℝ), (22304410753419/50000000000000 : ℝ), (1069138954711/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-414920809/2000000000 : ℝ)|^4267 ≤ (12625620301907/100000000000000 : ℝ)^3243
        have hw : |(-414920809/2000000000 : ℝ)|=(414920809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707217829/5000000000 : ℝ)|^4267 ≤ (22304410753419/50000000000000 : ℝ)^3243
        have hw : |(2707217829/5000000000 : ℝ)|=(2707217829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655442573/1250000000 : ℝ)|^4267 ≤ (1069138954711/2500000000000 : ℝ)^3243
        have hw : |(655442573/1250000000 : ℝ)|=(655442573/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s8_1 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674776071/5000000000 : ℝ)*x 0 + (-2161703911/10000000000 : ℝ)*x 1 + (655442573/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674776071/5000000000 : ℝ)^4267 ≤ (43906795937683/100000000000000 : ℝ)^3243 := by
    have hnat : (2674776071 : ℕ)^4267*100000000000000^3243 ≤ 43906795937683^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674776071 5000000000 43906795937683 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2161703911/10000000000 : ℝ)^4267 ≤ (2665529174259/20000000000000 : ℝ)^3243 := by
    have hnat : (2161703911 : ℕ)^4267*20000000000000^3243 ≤ 2665529174259^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161703911 10000000000 2665529174259 20000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655442573/1250000000 : ℝ)^4267 ≤ (1069138954711/2500000000000 : ℝ)^3243 := by
    have hnat : (655442573 : ℕ)^4267*2500000000000^3243 ≤ 1069138954711^3243*1250000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655442573 1250000000 1069138954711 2500000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674776071/5000000000 : ℝ), (-2161703911/10000000000 : ℝ), (655442573/1250000000 : ℝ)] ![(43906795937683/100000000000000 : ℝ), (2665529174259/20000000000000 : ℝ), (1069138954711/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674776071/5000000000 : ℝ)|^4267 ≤ (43906795937683/100000000000000 : ℝ)^3243
        have hw : |(2674776071/5000000000 : ℝ)|=(2674776071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2161703911/10000000000 : ℝ)|^4267 ≤ (2665529174259/20000000000000 : ℝ)^3243
        have hw : |(-2161703911/10000000000 : ℝ)|=(2161703911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655442573/1250000000 : ℝ)|^4267 ≤ (1069138954711/2500000000000 : ℝ)^3243
        have hw : |(655442573/1250000000 : ℝ)|=(655442573/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s8_2 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674776071/5000000000 : ℝ)*x 0 + (655442573/1250000000 : ℝ)*x 1 + (-2161703911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674776071/5000000000 : ℝ)^4267 ≤ (43906795937683/100000000000000 : ℝ)^3243 := by
    have hnat : (2674776071 : ℕ)^4267*100000000000000^3243 ≤ 43906795937683^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674776071 5000000000 43906795937683 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655442573/1250000000 : ℝ)^4267 ≤ (1069138954711/2500000000000 : ℝ)^3243 := by
    have hnat : (655442573 : ℕ)^4267*2500000000000^3243 ≤ 1069138954711^3243*1250000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655442573 1250000000 1069138954711 2500000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2161703911/10000000000 : ℝ)^4267 ≤ (2665529174259/20000000000000 : ℝ)^3243 := by
    have hnat : (2161703911 : ℕ)^4267*20000000000000^3243 ≤ 2665529174259^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161703911 10000000000 2665529174259 20000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674776071/5000000000 : ℝ), (655442573/1250000000 : ℝ), (-2161703911/10000000000 : ℝ)] ![(43906795937683/100000000000000 : ℝ), (1069138954711/2500000000000 : ℝ), (2665529174259/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674776071/5000000000 : ℝ)|^4267 ≤ (43906795937683/100000000000000 : ℝ)^3243
        have hw : |(2674776071/5000000000 : ℝ)|=(2674776071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655442573/1250000000 : ℝ)|^4267 ≤ (1069138954711/2500000000000 : ℝ)^3243
        have hw : |(655442573/1250000000 : ℝ)|=(655442573/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2161703911/10000000000 : ℝ)|^4267 ≤ (2665529174259/20000000000000 : ℝ)^3243
        have hw : |(-2161703911/10000000000 : ℝ)|=(2161703911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s8_3 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3468687/8000000 : ℝ)*x 0 + (520331513/1250000000 : ℝ)*x 1 + (4515896201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3468687/8000000 : ℝ)^4267 ≤ (33302669749309/100000000000000 : ℝ)^3243 := by
    have hnat : (3468687 : ℕ)^4267*100000000000000^3243 ≤ 33302669749309^3243*8000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3468687 8000000 33302669749309 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520331513/1250000000 : ℝ)^4267 ≤ (3156338407157/10000000000000 : ℝ)^3243 := by
    have hnat : (520331513 : ℕ)^4267*10000000000000^3243 ≤ 3156338407157^3243*1250000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520331513 1250000000 3156338407157 10000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4515896201/10000000000 : ℝ)^4267 ≤ (8783486541639/25000000000000 : ℝ)^3243 := by
    have hnat : (4515896201 : ℕ)^4267*25000000000000^3243 ≤ 8783486541639^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515896201 10000000000 8783486541639 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3468687/8000000 : ℝ), (520331513/1250000000 : ℝ), (4515896201/10000000000 : ℝ)] ![(33302669749309/100000000000000 : ℝ), (3156338407157/10000000000000 : ℝ), (8783486541639/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3468687/8000000 : ℝ)|^4267 ≤ (33302669749309/100000000000000 : ℝ)^3243
        have hw : |(3468687/8000000 : ℝ)|=(3468687/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(520331513/1250000000 : ℝ)|^4267 ≤ (3156338407157/10000000000000 : ℝ)^3243
        have hw : |(520331513/1250000000 : ℝ)|=(520331513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4515896201/10000000000 : ℝ)|^4267 ≤ (8783486541639/25000000000000 : ℝ)^3243
        have hw : |(4515896201/10000000000 : ℝ)|=(4515896201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s8_4 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2074616543/10000000000 : ℝ)*x 0 + (32775939/62500000 : ℝ)*x 1 + (541382289/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2074616543/10000000000 : ℝ)^4267 ≤ (6312860189437/50000000000000 : ℝ)^3243 := by
    have hnat : (2074616543 : ℕ)^4267*50000000000000^3243 ≤ 6312860189437^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074616543 10000000000 6312860189437 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32775939/62500000 : ℝ)^4267 ≤ (2673256287659/6250000000000 : ℝ)^3243 := by
    have hnat : (32775939 : ℕ)^4267*6250000000000^3243 ≤ 2673256287659^3243*62500000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32775939 62500000 2673256287659 6250000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541382289/1000000000 : ℝ)^4267 ≤ (44602179006817/100000000000000 : ℝ)^3243 := by
    have hnat : (541382289 : ℕ)^4267*100000000000000^3243 ≤ 44602179006817^3243*1000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541382289 1000000000 44602179006817 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2074616543/10000000000 : ℝ), (32775939/62500000 : ℝ), (541382289/1000000000 : ℝ)] ![(6312860189437/50000000000000 : ℝ), (2673256287659/6250000000000 : ℝ), (44602179006817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2074616543/10000000000 : ℝ)|^4267 ≤ (6312860189437/50000000000000 : ℝ)^3243
        have hw : |(-2074616543/10000000000 : ℝ)|=(2074616543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32775939/62500000 : ℝ)|^4267 ≤ (2673256287659/6250000000000 : ℝ)^3243
        have hw : |(32775939/62500000 : ℝ)|=(32775939/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541382289/1000000000 : ℝ)|^4267 ≤ (44602179006817/100000000000000 : ℝ)^3243
        have hw : |(541382289/1000000000 : ℝ)|=(541382289/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_s8_5 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (867176927/2000000000 : ℝ)*x 0 + (2257318037/5000000000 : ℝ)*x 1 + (2081959361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867176927/2000000000 : ℝ)^4267 ≤ (33302931343561/100000000000000 : ℝ)^3243 := by
    have hnat : (867176927 : ℕ)^4267*100000000000000^3243 ≤ 33302931343561^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867176927 2000000000 33302931343561 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257318037/5000000000 : ℝ)^4267 ≤ (7024209446293/20000000000000 : ℝ)^3243 := by
    have hnat : (2257318037 : ℕ)^4267*20000000000000^3243 ≤ 7024209446293^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257318037 5000000000 7024209446293 20000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081959361/5000000000 : ℝ)^4267 ≤ (7894005352783/25000000000000 : ℝ)^3243 := by
    have hnat : (2081959361 : ℕ)^4267*25000000000000^3243 ≤ 7894005352783^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081959361 5000000000 7894005352783 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867176927/2000000000 : ℝ), (2257318037/5000000000 : ℝ), (2081959361/5000000000 : ℝ)] ![(33302931343561/100000000000000 : ℝ), (7024209446293/20000000000000 : ℝ), (7894005352783/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867176927/2000000000 : ℝ)|^4267 ≤ (33302931343561/100000000000000 : ℝ)^3243
        have hw : |(867176927/2000000000 : ℝ)|=(867176927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2257318037/5000000000 : ℝ)|^4267 ≤ (7024209446293/20000000000000 : ℝ)^3243
        have hw : |(2257318037/5000000000 : ℝ)|=(2257318037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2081959361/5000000000 : ℝ)|^4267 ≤ (7894005352783/25000000000000 : ℝ)^3243
        have hw : |(2081959361/5000000000 : ℝ)|=(2081959361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1307_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2213/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5533/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14683/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14683/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2213/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14683/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2213/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14683/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2213/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14683/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2213/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14683/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2213/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14683/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2213/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2213/20000 : ℝ) ^ (2133/512 : ℝ) ≤ (650079824249359/6250000000000000000 : ℝ) := by
    have hpowers : (2213/20000 : ℝ)^2133 ≤ (650079824249359/6250000000000000000 : ℝ)^512 := by
      have hnat : (2213 : ℕ)^2133*6250000000000000000^512 ≤ 650079824249359^512*20000^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2213 20000 650079824249359 6250000000000000000 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2213/20000 : ℝ)) (X := (650079824249359/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14683/100000 : ℝ) ^ (2133/512 : ℝ) ≤ (1690080681545007/5000000000000000000 : ℝ) := by
    have hpowers : (14683/100000 : ℝ)^2133 ≤ (1690080681545007/5000000000000000000 : ℝ)^512 := by
      have hnat : (14683 : ℕ)^2133*5000000000000000000^512 ≤ 1690080681545007^512*100000^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14683 100000 1690080681545007 5000000000000000000 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14683/100000 : ℝ)) (X := (1690080681545007/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125650079824249359/3125000000000000000 : ℝ) ≤ (10000499299860931/10000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (3125650079824249359/3125000000000000000 : ℝ)^512 ≤ (10000499299860931/10000000000000000 : ℝ)^2133 := by
      have hnat : (3125650079824249359 : ℕ)^512*10000000000000000^2133 ≤ 10000499299860931^2133*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125650079824249359 3125000000000000000 10000499299860931 10000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000499299860931/10000000000000000 : ℝ)) (X := (3125650079824249359/3125000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011050722704722471/25000000000000000000 : ℝ) ≤ (78133287945299/78125000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (25011050722704722471/25000000000000000000 : ℝ)^512 ≤ (78133287945299/78125000000000 : ℝ)^2133 := by
      have hnat : (25011050722704722471 : ℕ)^512*78125000000000^2133 ≤ 78133287945299^2133*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011050722704722471 25000000000000000000 78133287945299 78125000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78133287945299/78125000000000 : ℝ)) (X := (25011050722704722471/25000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501690080681545007/2500000000000000000 : ℝ) ≤ (10001622414135613/10000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (2501690080681545007/2500000000000000000 : ℝ)^512 ≤ (10001622414135613/10000000000000000 : ℝ)^2133 := by
      have hnat : (2501690080681545007 : ℕ)^512*10000000000000000^2133 ≤ 10001622414135613^2133*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501690080681545007 2500000000000000000 10001622414135613 10000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001622414135613/10000000000000000 : ℝ)) (X := (2501690080681545007/2500000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(650079824249359/6250000000000000000 : ℝ) ≤ ((3014114933953957669/3015000000000000000 : ℝ)+2*(187185712447/120600000000000 : ℝ)*(2213/20000 : ℝ))^(2133/512 : ℝ) := by
    rw [show (3014114933953957669/3015000000000000000 : ℝ)+2*(187185712447/120600000000000 : ℝ)*(2213/20000 : ℝ)=(10000499299860931/10000000000000000 : ℝ) by norm_num, show 1+2*(650079824249359/6250000000000000000 : ℝ)=(3125650079824249359/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1690080681545007/5000000000000000000 : ℝ)+(650079824249359/6250000000000000000 : ℝ) ≤ ((3014114933953957669/3015000000000000000 : ℝ)+(187185712447/120600000000000 : ℝ)*((14683/100000 : ℝ)+(2213/20000 : ℝ)))^(2133/512 : ℝ) := by
    rw [show (3014114933953957669/3015000000000000000 : ℝ)+(187185712447/120600000000000 : ℝ)*((14683/100000 : ℝ)+(2213/20000 : ℝ))=(78133287945299/78125000000000 : ℝ) by norm_num, show 1+(1690080681545007/5000000000000000000 : ℝ)+(650079824249359/6250000000000000000 : ℝ)=(25011050722704722471/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1690080681545007/5000000000000000000 : ℝ) ≤ ((3014114933953957669/3015000000000000000 : ℝ)+2*(187185712447/120600000000000 : ℝ)*(14683/100000 : ℝ))^(2133/512 : ℝ) := by
    rw [show (3014114933953957669/3015000000000000000 : ℝ)+2*(187185712447/120600000000000 : ℝ)*(14683/100000 : ℝ)=(10001622414135613/10000000000000000 : ℝ) by norm_num, show 1+2*(1690080681545007/5000000000000000000 : ℝ)=(2501690080681545007/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3014114933953957669/3015000000000000000 : ℝ)*(X 1 0+X 2 0)+(187185712447/120600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (2213/20000 : ℝ)) (hi := (14683/100000 : ℝ)) (c := (3014114933953957669/3015000000000000000 : ℝ)) (alpha := (187185712447/120600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3014114933953957669/3015000000000000000 : ℝ)*(X 0 1+X 2 1)+(187185712447/120600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (2213/20000 : ℝ)) (hi := (14683/100000 : ℝ)) (c := (3014114933953957669/3015000000000000000 : ℝ)) (alpha := (187185712447/120600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3014114933953957669/3015000000000000000 : ℝ)*(X 0 2+X 1 2)+(187185712447/120600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (2213/20000 : ℝ)) (hi := (14683/100000 : ℝ)) (c := (3014114933953957669/3015000000000000000 : ℝ)) (alpha := (187185712447/120600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-414920809/2000000000 : ℝ)*X 0 0+(2707217829/5000000000 : ℝ)*X 0 1+(655442573/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674776071/5000000000 : ℝ)*X 1 0+(-2161703911/10000000000 : ℝ)*X 1 1+(655442573/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674776071/5000000000 : ℝ)*X 2 0+(655442573/1250000000 : ℝ)*X 2 1+(-2161703911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3468687/8000000 : ℝ)*X 0 0+(520331513/1250000000 : ℝ)*X 0 1+(4515896201/10000000000 : ℝ)*X 0 2+(3468687/8000000 : ℝ)*X 1 0+(520331513/1250000000 : ℝ)*X 1 1+(4515896201/10000000000 : ℝ)*X 1 2+(3468687/8000000 : ℝ)*X 2 0+(520331513/1250000000 : ℝ)*X 2 1+(4515896201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2074616543/10000000000 : ℝ)*X 0 0+(32775939/62500000 : ℝ)*X 0 1+(541382289/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((867176927/2000000000 : ℝ)*X 0 0+(2257318037/5000000000 : ℝ)*X 0 1+(2081959361/5000000000 : ℝ)*X 0 2+(867176927/2000000000 : ℝ)*X 1 0+(2257318037/5000000000 : ℝ)*X 1 1+(2081959361/5000000000 : ℝ)*X 1 2+(867176927/2000000000 : ℝ)*X 2 0+(2257318037/5000000000 : ℝ)*X 2 1+(2081959361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10367179172332216375517327/4187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (94228407/20000000000000 : ℝ)*(base19) + (87807879/20000000000000 : ℝ)*(base23) + (8586737/50000000000000 : ℝ)*(lower2) + (62352663/100000000000000 : ℝ)*(upper3) + (3854863/10000000000000 : ℝ)*(upper5) + (2170619083135151/50000000000000 : ℝ)*(major0) + (2170619083135151/50000000000000 : ℝ)*(major1) + (2170619083135151/50000000000000 : ℝ)*(major2) + (1462888416836251/25000000000000 : ℝ)*(sp0) + (5851562694790277/100000000000000 : ℝ)*(sp1) + (5851562726892917/100000000000000 : ℝ)*(sp2) + (353863513190049/12500000000000 : ℝ)*(sp3) + (9498587309/100000000000000 : ℝ)*(sp4) + (124464077/2500000000000 : ℝ)*(sp5) + (2830913084083471/100000000000000 : ℝ)*(f.failure) + (5851563165932313/100000000000000 : ℝ)*(f.sum) + (542468874001/1507500000000000000000000000 : ℝ)*base65 + (61698527862348019/150750000000000000000000000000000 : ℝ)*base67 + (331578652348848019/150750000000000000000000000000000 : ℝ)*base69 + (792893365021848019/150750000000000000000000000000000 : ℝ)*base71 + (12262036394309/1507500000000000000000000000 : ℝ)*base74 + (2941550121732348019/150750000000000000000000000000000 : ℝ)*base75 + (198416758138151981/150750000000000000000000000000000 : ℝ)*base78 + (1190426077410348019/150750000000000000000000000000000 : ℝ)*base79 + (10698965156489/1507500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (12247439/2500000000000000000000 : ℝ)*base90 + (12247439/2500000000000000000000 : ℝ)*base92 + (12247439/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1307_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2213/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5533/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1307_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1307_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5533/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1307_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1307_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1307_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5527/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5533/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1307_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
