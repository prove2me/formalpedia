-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1188_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:52:15.963024+00:00
-- url     : https://prove2.me/submissions/52ed242b-880a-4d2b-86c7-82ff8650fa20

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
theorem support_rectangle_w1188_s0_0 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-234667107/1250000000 : ℝ)*x 0 + (6043759327/10000000000 : ℝ)*x 1 + (478626233/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (234667107/1250000000 : ℝ)^8381 ≤ (5464951806979/50000000000000 : ℝ)^6333 := by
    have hnat : (234667107 : ℕ)^8381*50000000000000^6333 ≤ 5464951806979^6333*1250000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234667107 1250000000 5464951806979 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6043759327/10000000000 : ℝ)^8381 ≤ (51355277655617/100000000000000 : ℝ)^6333 := by
    have hnat : (6043759327 : ℕ)^8381*100000000000000^6333 ≤ 51355277655617^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6043759327 10000000000 51355277655617 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (478626233/1000000000 : ℝ)^8381 ≤ (37714818711377/100000000000000 : ℝ)^6333 := by
    have hnat : (478626233 : ℕ)^8381*100000000000000^6333 ≤ 37714818711377^6333*1000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478626233 1000000000 37714818711377 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-234667107/1250000000 : ℝ), (6043759327/10000000000 : ℝ), (478626233/1000000000 : ℝ)] ![(5464951806979/50000000000000 : ℝ), (51355277655617/100000000000000 : ℝ), (37714818711377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-234667107/1250000000 : ℝ)|^8381 ≤ (5464951806979/50000000000000 : ℝ)^6333
        have hw : |(-234667107/1250000000 : ℝ)|=(234667107/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6043759327/10000000000 : ℝ)|^8381 ≤ (51355277655617/100000000000000 : ℝ)^6333
        have hw : |(6043759327/10000000000 : ℝ)|=(6043759327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(478626233/1000000000 : ℝ)|^8381 ≤ (37714818711377/100000000000000 : ℝ)^6333
        have hw : |(478626233/1000000000 : ℝ)|=(478626233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s0_1 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2757100907/5000000000 : ℝ)*x 0 + (-2597705607/10000000000 : ℝ)*x 1 + (74785349/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757100907/5000000000 : ℝ)^8381 ≤ (22743218093093/50000000000000 : ℝ)^6333 := by
    have hnat : (2757100907 : ℕ)^8381*50000000000000^6333 ≤ 22743218093093^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757100907 5000000000 22743218093093 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2597705607/10000000000 : ℝ)^8381 ≤ (3359749006197/20000000000000 : ℝ)^6333 := by
    have hnat : (2597705607 : ℕ)^8381*20000000000000^6333 ≤ 3359749006197^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597705607 10000000000 3359749006197 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74785349/156250000 : ℝ)^8381 ≤ (7542963754789/20000000000000 : ℝ)^6333 := by
    have hnat : (74785349 : ℕ)^8381*20000000000000^6333 ≤ 7542963754789^6333*156250000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74785349 156250000 7542963754789 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757100907/5000000000 : ℝ), (-2597705607/10000000000 : ℝ), (74785349/156250000 : ℝ)] ![(22743218093093/50000000000000 : ℝ), (3359749006197/20000000000000 : ℝ), (7542963754789/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757100907/5000000000 : ℝ)|^8381 ≤ (22743218093093/50000000000000 : ℝ)^6333
        have hw : |(2757100907/5000000000 : ℝ)|=(2757100907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2597705607/10000000000 : ℝ)|^8381 ≤ (3359749006197/20000000000000 : ℝ)^6333
        have hw : |(-2597705607/10000000000 : ℝ)|=(2597705607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(74785349/156250000 : ℝ)|^8381 ≤ (7542963754789/20000000000000 : ℝ)^6333
        have hw : |(74785349/156250000 : ℝ)|=(74785349/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s0_2 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5514202097/10000000000 : ℝ)*x 0 + (4674084/9765625 : ℝ)*x 1 + (-519541127/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5514202097/10000000000 : ℝ)^8381 ≤ (45486439275571/100000000000000 : ℝ)^6333 := by
    have hnat : (5514202097 : ℕ)^8381*100000000000000^6333 ≤ 45486439275571^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514202097 10000000000 45486439275571 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4674084/9765625 : ℝ)^8381 ≤ (37714815436979/100000000000000 : ℝ)^6333 := by
    have hnat : (4674084 : ℕ)^8381*100000000000000^6333 ≤ 37714815436979^6333*9765625^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4674084 9765625 37714815436979 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519541127/2000000000 : ℝ)^8381 ≤ (16798745270609/100000000000000 : ℝ)^6333 := by
    have hnat : (519541127 : ℕ)^8381*100000000000000^6333 ≤ 16798745270609^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519541127 2000000000 16798745270609 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5514202097/10000000000 : ℝ), (4674084/9765625 : ℝ), (-519541127/2000000000 : ℝ)] ![(45486439275571/100000000000000 : ℝ), (37714815436979/100000000000000 : ℝ), (16798745270609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5514202097/10000000000 : ℝ)|^8381 ≤ (45486439275571/100000000000000 : ℝ)^6333
        have hw : |(5514202097/10000000000 : ℝ)|=(5514202097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4674084/9765625 : ℝ)|^8381 ≤ (37714815436979/100000000000000 : ℝ)^6333
        have hw : |(4674084/9765625 : ℝ)|=(4674084/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-519541127/2000000000 : ℝ)|^8381 ≤ (16798745270609/100000000000000 : ℝ)^6333
        have hw : |(-519541127/2000000000 : ℝ)|=(519541127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s0_3 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4197295819/10000000000 : ℝ)*x 0 + (623808563/2000000000 : ℝ)*x 1 + (2821696367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4197295819/10000000000 : ℝ)^8381 ≤ (31698844361069/100000000000000 : ℝ)^6333 := by
    have hnat : (4197295819 : ℕ)^8381*100000000000000^6333 ≤ 31698844361069^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4197295819 10000000000 31698844361069 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623808563/2000000000 : ℝ)^8381 ≤ (10699542477113/50000000000000 : ℝ)^6333 := by
    have hnat : (623808563 : ℕ)^8381*50000000000000^6333 ≤ 10699542477113^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623808563 2000000000 10699542477113 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2821696367/5000000000 : ℝ)^8381 ≤ (11725517667997/25000000000000 : ℝ)^6333 := by
    have hnat : (2821696367 : ℕ)^8381*25000000000000^6333 ≤ 11725517667997^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2821696367 5000000000 11725517667997 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4197295819/10000000000 : ℝ), (623808563/2000000000 : ℝ), (2821696367/5000000000 : ℝ)] ![(31698844361069/100000000000000 : ℝ), (10699542477113/50000000000000 : ℝ), (11725517667997/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4197295819/10000000000 : ℝ)|^8381 ≤ (31698844361069/100000000000000 : ℝ)^6333
        have hw : |(4197295819/10000000000 : ℝ)|=(4197295819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623808563/2000000000 : ℝ)|^8381 ≤ (10699542477113/50000000000000 : ℝ)^6333
        have hw : |(623808563/2000000000 : ℝ)|=(623808563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2821696367/5000000000 : ℝ)|^8381 ≤ (11725517667997/25000000000000 : ℝ)^6333
        have hw : |(2821696367/5000000000 : ℝ)|=(2821696367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s0_4 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-94117423/500000000 : ℝ)*x 0 + (18822959/39062500 : ℝ)*x 1 + (6010201237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94117423/500000000 : ℝ)^8381 ≤ (10968533598359/100000000000000 : ℝ)^6333 := by
    have hnat : (94117423 : ℕ)^8381*100000000000000^6333 ≤ 10968533598359^6333*500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94117423 500000000 10968533598359 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18822959/39062500 : ℝ)^8381 ≤ (38053214411269/100000000000000 : ℝ)^6333 := by
    have hnat : (18822959 : ℕ)^8381*100000000000000^6333 ≤ 38053214411269^6333*39062500^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18822959 39062500 38053214411269 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6010201237/10000000000 : ℝ)^8381 ≤ (50978251975883/100000000000000 : ℝ)^6333 := by
    have hnat : (6010201237 : ℕ)^8381*100000000000000^6333 ≤ 50978251975883^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6010201237 10000000000 50978251975883 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-94117423/500000000 : ℝ), (18822959/39062500 : ℝ), (6010201237/10000000000 : ℝ)] ![(10968533598359/100000000000000 : ℝ), (38053214411269/100000000000000 : ℝ), (50978251975883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-94117423/500000000 : ℝ)|^8381 ≤ (10968533598359/100000000000000 : ℝ)^6333
        have hw : |(-94117423/500000000 : ℝ)|=(94117423/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(18822959/39062500 : ℝ)|^8381 ≤ (38053214411269/100000000000000 : ℝ)^6333
        have hw : |(18822959/39062500 : ℝ)|=(18822959/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6010201237/10000000000 : ℝ)|^8381 ≤ (50978251975883/100000000000000 : ℝ)^6333
        have hw : |(6010201237/10000000000 : ℝ)|=(6010201237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s0_5 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (646536837/1250000000 : ℝ)*x 0 + (-1373766777/10000000000 : ℝ)*x 1 + (751275111/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646536837/1250000000 : ℝ)^8381 ≤ (41791946210363/100000000000000 : ℝ)^6333 := by
    have hnat : (646536837 : ℕ)^8381*100000000000000^6333 ≤ 41791946210363^6333*1250000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646536837 1250000000 41791946210363 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1373766777/10000000000 : ℝ)^8381 ≤ (7229805723613/100000000000000 : ℝ)^6333 := by
    have hnat : (1373766777 : ℕ)^8381*100000000000000^6333 ≤ 7229805723613^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373766777 10000000000 7229805723613 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (751275111/1250000000 : ℝ)^8381 ≤ (10195649611679/20000000000000 : ℝ)^6333 := by
    have hnat : (751275111 : ℕ)^8381*20000000000000^6333 ≤ 10195649611679^6333*1250000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751275111 1250000000 10195649611679 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646536837/1250000000 : ℝ), (-1373766777/10000000000 : ℝ), (751275111/1250000000 : ℝ)] ![(41791946210363/100000000000000 : ℝ), (7229805723613/100000000000000 : ℝ), (10195649611679/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646536837/1250000000 : ℝ)|^8381 ≤ (41791946210363/100000000000000 : ℝ)^6333
        have hw : |(646536837/1250000000 : ℝ)|=(646536837/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1373766777/10000000000 : ℝ)|^8381 ≤ (7229805723613/100000000000000 : ℝ)^6333
        have hw : |(-1373766777/10000000000 : ℝ)|=(1373766777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(751275111/1250000000 : ℝ)|^8381 ≤ (10195649611679/20000000000000 : ℝ)^6333
        have hw : |(751275111/1250000000 : ℝ)|=(751275111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s0_6 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (41378357/80000000 : ℝ)*x 0 + (6010201087/10000000000 : ℝ)*x 1 + (-274753313/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41378357/80000000 : ℝ)^8381 ≤ (41791945451167/100000000000000 : ℝ)^6333 := by
    have hnat : (41378357 : ℕ)^8381*100000000000000^6333 ≤ 41791945451167^6333*80000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41378357 80000000 41791945451167 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6010201087/10000000000 : ℝ)^8381 ≤ (50978250292149/100000000000000 : ℝ)^6333 := by
    have hnat : (6010201087 : ℕ)^8381*100000000000000^6333 ≤ 50978250292149^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6010201087 10000000000 50978250292149 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274753313/2000000000 : ℝ)^8381 ≤ (1445960849421/20000000000000 : ℝ)^6333 := by
    have hnat : (274753313 : ℕ)^8381*20000000000000^6333 ≤ 1445960849421^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274753313 2000000000 1445960849421 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41378357/80000000 : ℝ), (6010201087/10000000000 : ℝ), (-274753313/2000000000 : ℝ)] ![(41791945451167/100000000000000 : ℝ), (50978250292149/100000000000000 : ℝ), (1445960849421/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41378357/80000000 : ℝ)|^8381 ≤ (41791945451167/100000000000000 : ℝ)^6333
        have hw : |(41378357/80000000 : ℝ)|=(41378357/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6010201087/10000000000 : ℝ)|^8381 ≤ (50978250292149/100000000000000 : ℝ)^6333
        have hw : |(6010201087/10000000000 : ℝ)|=(6010201087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-274753313/2000000000 : ℝ)|^8381 ≤ (1445960849421/20000000000000 : ℝ)^6333
        have hw : |(-274753313/2000000000 : ℝ)|=(274753313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s0_7 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2103678213/5000000000 : ℝ)*x 0 + (5578320787/10000000000 : ℝ)*x 1 + (199150559/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103678213/5000000000 : ℝ)^8381 ≤ (3179943384543/10000000000000 : ℝ)^6333 := by
    have hnat : (2103678213 : ℕ)^8381*10000000000000^6333 ≤ 3179943384543^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103678213 5000000000 3179943384543 10000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5578320787/10000000000 : ℝ)^8381 ≤ (11546926769901/25000000000000 : ℝ)^6333 := by
    have hnat : (5578320787 : ℕ)^8381*25000000000000^6333 ≤ 11546926769901^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5578320787 10000000000 11546926769901 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199150559/625000000 : ℝ)^8381 ≤ (11006429526101/50000000000000 : ℝ)^6333 := by
    have hnat : (199150559 : ℕ)^8381*50000000000000^6333 ≤ 11006429526101^6333*625000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199150559 625000000 11006429526101 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2103678213/5000000000 : ℝ), (5578320787/10000000000 : ℝ), (199150559/625000000 : ℝ)] ![(3179943384543/10000000000000 : ℝ), (11546926769901/25000000000000 : ℝ), (11006429526101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2103678213/5000000000 : ℝ)|^8381 ≤ (3179943384543/10000000000000 : ℝ)^6333
        have hw : |(2103678213/5000000000 : ℝ)|=(2103678213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5578320787/10000000000 : ℝ)|^8381 ≤ (11546926769901/25000000000000 : ℝ)^6333
        have hw : |(5578320787/10000000000 : ℝ)|=(5578320787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(199150559/625000000 : ℝ)|^8381 ≤ (11006429526101/50000000000000 : ℝ)^6333
        have hw : |(199150559/625000000 : ℝ)|=(199150559/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1188_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (601/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (691/2500 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (2095/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2095 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2095*1^512 ≤ 0^512*1^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2095/512 : ℝ) ≤ (294184867285156437/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2095 ≤ (294184867285156437/12500000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2095*12500000000000000000^512 ≤ 294184867285156437^512*5^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 294184867285156437 12500000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (294184867285156437/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2095 := by
      have hnat : (1 : ℕ)^512*1^2095 ≤ 1^2095*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12794184867285156437/12500000000000000000 : ℝ) ≤ (5028506259742903/5000000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (12794184867285156437/12500000000000000000 : ℝ)^512 ≤ (5028506259742903/5000000000000000 : ℝ)^2095 := by
      have hnat : (12794184867285156437 : ℕ)^512*5000000000000000^2095 ≤ 5028506259742903^2095*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12794184867285156437 12500000000000000000 5028506259742903 5000000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028506259742903/5000000000000000 : ℝ)) (X := (12794184867285156437/12500000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6544184867285156437/6250000000000000000 : ℝ) ≤ (2528506259742903/2500000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (6544184867285156437/6250000000000000000 : ℝ)^512 ≤ (2528506259742903/2500000000000000 : ℝ)^2095 := by
      have hnat : (6544184867285156437 : ℕ)^512*2500000000000000^2095 ≤ 2528506259742903^2095*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6544184867285156437 6250000000000000000 2528506259742903 2500000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2528506259742903/2500000000000000 : ℝ)) (X := (6544184867285156437/6250000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(28506259742903/2000000000000000 : ℝ)*(0 : ℝ))^(2095/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(28506259742903/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(294184867285156437/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(28506259742903/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2095/512 : ℝ) := by
    rw [show (1 : ℝ)+(28506259742903/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5028506259742903/5000000000000000 : ℝ) by norm_num, show 1+(294184867285156437/12500000000000000000 : ℝ)+(0 : ℝ)=(12794184867285156437/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(294184867285156437/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(28506259742903/2000000000000000 : ℝ)*(2/5 : ℝ))^(2095/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(28506259742903/2000000000000000 : ℝ)*(2/5 : ℝ)=(2528506259742903/2500000000000000 : ℝ) by norm_num, show 1+2*(294184867285156437/12500000000000000000 : ℝ)=(6544184867285156437/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(28506259742903/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28506259742903/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(28506259742903/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28506259742903/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(28506259742903/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28506259742903/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-234667107/1250000000 : ℝ)*X 0 0+(6043759327/10000000000 : ℝ)*X 0 1+(478626233/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2757100907/5000000000 : ℝ)*X 1 0+(-2597705607/10000000000 : ℝ)*X 1 1+(74785349/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5514202097/10000000000 : ℝ)*X 2 0+(4674084/9765625 : ℝ)*X 2 1+(-519541127/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4197295819/10000000000 : ℝ)*X 0 0+(623808563/2000000000 : ℝ)*X 0 1+(2821696367/5000000000 : ℝ)*X 0 2+(4197295819/10000000000 : ℝ)*X 1 0+(623808563/2000000000 : ℝ)*X 1 1+(2821696367/5000000000 : ℝ)*X 1 2+(4197295819/10000000000 : ℝ)*X 2 0+(623808563/2000000000 : ℝ)*X 2 1+(2821696367/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-94117423/500000000 : ℝ)*X 0 0+(18822959/39062500 : ℝ)*X 0 1+(6010201237/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((646536837/1250000000 : ℝ)*X 1 0+(-1373766777/10000000000 : ℝ)*X 1 1+(751275111/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41378357/80000000 : ℝ)*X 2 0+(6010201087/10000000000 : ℝ)*X 2 1+(-274753313/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2103678213/5000000000 : ℝ)*X 0 0+(5578320787/10000000000 : ℝ)*X 0 1+(199150559/625000000 : ℝ)*X 0 2+(2103678213/5000000000 : ℝ)*X 1 0+(5578320787/10000000000 : ℝ)*X 1 1+(199150559/625000000 : ℝ)*X 1 2+(2103678213/5000000000 : ℝ)*X 2 0+(5578320787/10000000000 : ℝ)*X 2 1+(199150559/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (689960178800505160096383/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33416417/50000000000000 : ℝ)*(base1) + (1655856397/100000000000000 : ℝ)*(base19) + (315650837/20000000000000 : ℝ)*(base23) + (14801929/12500000000000 : ℝ)*(base24) + (387706881/100000000000000 : ℝ)*(upper3) + (595693043281871/100000000000000 : ℝ)*(major0) + (595693043281871/100000000000000 : ℝ)*(major1) + (595693043281871/100000000000000 : ℝ)*(major2) + (397618036870089/50000000000000 : ℝ)*(sp0) + (795237979519643/100000000000000 : ℝ)*(sp1) + (397618969353211/50000000000000 : ℝ)*(sp2) + (198071623909139/50000000000000 : ℝ)*(sp3) + (453558587/12500000000000 : ℝ)*(sp4) + (2906549859/100000000000000 : ℝ)*(sp7) + (396146221200971/100000000000000 : ℝ)*(f.failure) + (19880990884401/2500000000000 : ℝ)*(f.sum) + (13637687988487/100000000000000000000000000000 : ℝ)*base66 + (82085497788487/200000000000000000000000000000 : ℝ)*base68 + (1453463292811513/200000000000000000000000000000 : ℝ)*base69 + (142972617211513/200000000000000000000000000000 : ℝ)*base71 + (19118490611513/100000000000000000000000000000 : ℝ)*base73 + (377624421611513/200000000000000000000000000000 : ℝ)*base75 + (266865710811513/200000000000000000000000000000 : ℝ)*base77 + (1148252149811513/200000000000000000000000000000 : ℝ)*base79 + (245959523011513/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (8594087/2500000000000000000000 : ℝ)*base90 + (8594087/2500000000000000000000 : ℝ)*base92 + (8594087/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (387925098754624906460433/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1624161/2000000000000 : ℝ)*(base1) + (1958685407/100000000000000 : ℝ)*(base19) + (1951554273/100000000000000 : ℝ)*(base23) + (210651713/100000000000000 : ℝ)*(upper3) + (117338541/50000000000000 : ℝ)*(upper5) + (628668730340163/100000000000000 : ℝ)*(major0) + (628668730340163/100000000000000 : ℝ)*(major1) + (628668730340163/100000000000000 : ℝ)*(major2) + (805149107/20000000000000 : ℝ)*(sp1) + (4092142683/100000000000000 : ℝ)*(sp2) + (52453853586029/6250000000000 : ℝ)*(sp4) + (839255591737473/100000000000000 : ℝ)*(sp5) + (419627766235729/50000000000000 : ℝ)*(sp6) + (209037772343561/50000000000000 : ℝ)*(sp7) + (104518906473793/25000000000000 : ℝ)*(f.failure) + (167852315233683/20000000000000 : ℝ)*(f.sum) + (95193938086811/100000000000000000000000000000 : ℝ)*base66 + (1570421941113189/200000000000000000000000000000 : ℝ)*base67 + (1064375087913189/200000000000000000000000000000 : ℝ)*base69 + (184778181113189/200000000000000000000000000000 : ℝ)*base71 + (197780540313189/100000000000000000000000000000 : ℝ)*base73 + (1050243124713189/200000000000000000000000000000 : ℝ)*base75 + (1348903020513189/200000000000000000000000000000 : ℝ)*base77 + (2444934357513189/200000000000000000000000000000 : ℝ)*base79 + (224853754186811/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (920379/625000000000000000000 : ℝ)*base89 + (920379/625000000000000000000 : ℝ)*base91 + (920379/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1188_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (601/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (691/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1188_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1188_s1_0 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1039334171/5000000000 : ℝ)*x 0 + (5689399183/10000000000 : ℝ)*x 1 + (1002348623/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039334171/5000000000 : ℝ)^8381 ≤ (6253697537049/50000000000000 : ℝ)^6333 := by
    have hnat : (1039334171 : ℕ)^8381*50000000000000^6333 ≤ 6253697537049^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039334171 5000000000 6253697537049 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5689399183/10000000000 : ℝ)^8381 ≤ (9481748755979/20000000000000 : ℝ)^6333 := by
    have hnat : (5689399183 : ℕ)^8381*20000000000000^6333 ≤ 9481748755979^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5689399183 10000000000 9481748755979 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002348623/2000000000 : ℝ)^8381 ≤ (10020965283379/25000000000000 : ℝ)^6333 := by
    have hnat : (1002348623 : ℕ)^8381*25000000000000^6333 ≤ 10020965283379^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002348623 2000000000 10020965283379 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1039334171/5000000000 : ℝ), (5689399183/10000000000 : ℝ), (1002348623/2000000000 : ℝ)] ![(6253697537049/50000000000000 : ℝ), (9481748755979/20000000000000 : ℝ), (10020965283379/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1039334171/5000000000 : ℝ)|^8381 ≤ (6253697537049/50000000000000 : ℝ)^6333
        have hw : |(-1039334171/5000000000 : ℝ)|=(1039334171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5689399183/10000000000 : ℝ)|^8381 ≤ (9481748755979/20000000000000 : ℝ)^6333
        have hw : |(5689399183/10000000000 : ℝ)|=(5689399183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1002348623/2000000000 : ℝ)|^8381 ≤ (10020965283379/25000000000000 : ℝ)^6333
        have hw : |(1002348623/2000000000 : ℝ)|=(1002348623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s1_1 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2708301911/5000000000 : ℝ)*x 0 + (-1221760777/5000000000 : ℝ)*x 1 + (626467923/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2708301911/5000000000 : ℝ)^8381 ≤ (44424063725473/100000000000000 : ℝ)^6333 := by
    have hnat : (2708301911 : ℕ)^8381*100000000000000^6333 ≤ 44424063725473^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708301911 5000000000 44424063725473 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1221760777/5000000000 : ℝ)^8381 ≤ (3098414456601/20000000000000 : ℝ)^6333 := by
    have hnat : (1221760777 : ℕ)^8381*20000000000000^6333 ≤ 3098414456601^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221760777 5000000000 3098414456601 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (626467923/1250000000 : ℝ)^8381 ≤ (1603354559229/4000000000000 : ℝ)^6333 := by
    have hnat : (626467923 : ℕ)^8381*4000000000000^6333 ≤ 1603354559229^6333*1250000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626467923 1250000000 1603354559229 4000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2708301911/5000000000 : ℝ), (-1221760777/5000000000 : ℝ), (626467923/1250000000 : ℝ)] ![(44424063725473/100000000000000 : ℝ), (3098414456601/20000000000000 : ℝ), (1603354559229/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2708301911/5000000000 : ℝ)|^8381 ≤ (44424063725473/100000000000000 : ℝ)^6333
        have hw : |(2708301911/5000000000 : ℝ)|=(2708301911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1221760777/5000000000 : ℝ)|^8381 ≤ (3098414456601/20000000000000 : ℝ)^6333
        have hw : |(-1221760777/5000000000 : ℝ)|=(1221760777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(626467923/1250000000 : ℝ)|^8381 ≤ (1603354559229/4000000000000 : ℝ)^6333
        have hw : |(626467923/1250000000 : ℝ)|=(626467923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s1_2 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5416602931/10000000000 : ℝ)*x 0 + (2505871987/5000000000 : ℝ)*x 1 + (-1221760981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5416602931/10000000000 : ℝ)^8381 ≤ (2776503378427/6250000000000 : ℝ)^6333 := by
    have hnat : (5416602931 : ℕ)^8381*6250000000000^6333 ≤ 2776503378427^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416602931 10000000000 2776503378427 6250000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2505871987/5000000000 : ℝ)^8381 ≤ (20041935112767/50000000000000 : ℝ)^6333 := by
    have hnat : (2505871987 : ℕ)^8381*50000000000000^6333 ≤ 20041935112767^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2505871987 5000000000 20041935112767 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1221760981/5000000000 : ℝ)^8381 ≤ (3098415141253/20000000000000 : ℝ)^6333 := by
    have hnat : (1221760981 : ℕ)^8381*20000000000000^6333 ≤ 3098415141253^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221760981 5000000000 3098415141253 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5416602931/10000000000 : ℝ), (2505871987/5000000000 : ℝ), (-1221760981/5000000000 : ℝ)] ![(2776503378427/6250000000000 : ℝ), (20041935112767/50000000000000 : ℝ), (3098415141253/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5416602931/10000000000 : ℝ)|^8381 ≤ (2776503378427/6250000000000 : ℝ)^6333
        have hw : |(5416602931/10000000000 : ℝ)|=(5416602931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2505871987/5000000000 : ℝ)|^8381 ≤ (20041935112767/50000000000000 : ℝ)^6333
        have hw : |(2505871987/5000000000 : ℝ)|=(2505871987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1221760981/5000000000 : ℝ)|^8381 ≤ (3098415141253/20000000000000 : ℝ)^6333
        have hw : |(-1221760981/5000000000 : ℝ)|=(1221760981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s1_3 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1078378403/2500000000 : ℝ)*x 0 + (3685582243/10000000000 : ℝ)*x 1 + (2522968239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078378403/2500000000 : ℝ)^8381 ≤ (1027048404409/3125000000000 : ℝ)^6333 := by
    have hnat : (1078378403 : ℕ)^8381*3125000000000^6333 ≤ 1027048404409^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078378403 2500000000 1027048404409 3125000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3685582243/10000000000 : ℝ)^8381 ≤ (26688274315389/100000000000000 : ℝ)^6333 := by
    have hnat : (3685582243 : ℕ)^8381*100000000000000^6333 ≤ 26688274315389^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3685582243 10000000000 26688274315389 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2522968239/5000000000 : ℝ)^8381 ≤ (20223088360801/50000000000000 : ℝ)^6333 := by
    have hnat : (2522968239 : ℕ)^8381*50000000000000^6333 ≤ 20223088360801^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2522968239 5000000000 20223088360801 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078378403/2500000000 : ℝ), (3685582243/10000000000 : ℝ), (2522968239/5000000000 : ℝ)] ![(1027048404409/3125000000000 : ℝ), (26688274315389/100000000000000 : ℝ), (20223088360801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078378403/2500000000 : ℝ)|^8381 ≤ (1027048404409/3125000000000 : ℝ)^6333
        have hw : |(1078378403/2500000000 : ℝ)|=(1078378403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3685582243/10000000000 : ℝ)|^8381 ≤ (26688274315389/100000000000000 : ℝ)^6333
        have hw : |(3685582243/10000000000 : ℝ)|=(3685582243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2522968239/5000000000 : ℝ)|^8381 ≤ (20223088360801/50000000000000 : ℝ)^6333
        have hw : |(2522968239/5000000000 : ℝ)|=(2522968239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s1_4 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2079412669/10000000000 : ℝ)*x 0 + (5020834533/10000000000 : ℝ)*x 1 + (5680130579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079412669/10000000000 : ℝ)^8381 ≤ (12513322374447/100000000000000 : ℝ)^6333 := by
    have hnat : (2079412669 : ℕ)^8381*100000000000000^6333 ≤ 12513322374447^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079412669 10000000000 12513322374447 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5020834533/10000000000 : ℝ)^8381 ≤ (40180116740969/100000000000000 : ℝ)^6333 := by
    have hnat : (5020834533 : ℕ)^8381*100000000000000^6333 ≤ 40180116740969^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5020834533 10000000000 40180116740969 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5680130579/10000000000 : ℝ)^8381 ≤ (9461312174033/20000000000000 : ℝ)^6333 := by
    have hnat : (5680130579 : ℕ)^8381*20000000000000^6333 ≤ 9461312174033^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5680130579 10000000000 9461312174033 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2079412669/10000000000 : ℝ), (5020834533/10000000000 : ℝ), (5680130579/10000000000 : ℝ)] ![(12513322374447/100000000000000 : ℝ), (40180116740969/100000000000000 : ℝ), (9461312174033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2079412669/10000000000 : ℝ)|^8381 ≤ (12513322374447/100000000000000 : ℝ)^6333
        have hw : |(-2079412669/10000000000 : ℝ)|=(2079412669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5020834533/10000000000 : ℝ)|^8381 ≤ (40180116740969/100000000000000 : ℝ)^6333
        have hw : |(5020834533/10000000000 : ℝ)|=(5020834533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5680130579/10000000000 : ℝ)|^8381 ≤ (9461312174033/20000000000000 : ℝ)^6333
        have hw : |(5680130579/10000000000 : ℝ)|=(5680130579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s1_5 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2621234761/5000000000 : ℝ)*x 0 + (-443783403/2500000000 : ℝ)*x 1 + (2840065771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2621234761/5000000000 : ℝ)^8381 ≤ (42543960049219/100000000000000 : ℝ)^6333 := by
    have hnat : (2621234761 : ℕ)^8381*100000000000000^6333 ≤ 42543960049219^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621234761 5000000000 42543960049219 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443783403/2500000000 : ℝ)^8381 ≤ (10149468460197/100000000000000 : ℝ)^6333 := by
    have hnat : (443783403 : ℕ)^8381*100000000000000^6333 ≤ 10149468460197^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443783403 2500000000 10149468460197 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2840065771/5000000000 : ℝ)^8381 ≤ (47306571484083/100000000000000 : ℝ)^6333 := by
    have hnat : (2840065771 : ℕ)^8381*100000000000000^6333 ≤ 47306571484083^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2840065771 5000000000 47306571484083 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2621234761/5000000000 : ℝ), (-443783403/2500000000 : ℝ), (2840065771/5000000000 : ℝ)] ![(42543960049219/100000000000000 : ℝ), (10149468460197/100000000000000 : ℝ), (47306571484083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2621234761/5000000000 : ℝ)|^8381 ≤ (42543960049219/100000000000000 : ℝ)^6333
        have hw : |(2621234761/5000000000 : ℝ)|=(2621234761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-443783403/2500000000 : ℝ)|^8381 ≤ (10149468460197/100000000000000 : ℝ)^6333
        have hw : |(-443783403/2500000000 : ℝ)|=(443783403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2840065771/5000000000 : ℝ)|^8381 ≤ (47306571484083/100000000000000 : ℝ)^6333
        have hw : |(2840065771/5000000000 : ℝ)|=(2840065771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s1_6 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5242469329/10000000000 : ℝ)*x 0 + (5680132319/10000000000 : ℝ)*x 1 + (-110945797/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5242469329/10000000000 : ℝ)^8381 ≤ (1701758319059/4000000000000 : ℝ)^6333 := by
    have hnat : (5242469329 : ℕ)^8381*4000000000000^6333 ≤ 1701758319059^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242469329 10000000000 1701758319059 4000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5680132319/10000000000 : ℝ)^8381 ≤ (1182664501199/2500000000000 : ℝ)^6333 := by
    have hnat : (5680132319 : ℕ)^8381*2500000000000^6333 ≤ 1182664501199^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5680132319 10000000000 1182664501199 2500000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110945797/625000000 : ℝ)^8381 ≤ (5074730976477/50000000000000 : ℝ)^6333 := by
    have hnat : (110945797 : ℕ)^8381*50000000000000^6333 ≤ 5074730976477^6333*625000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110945797 625000000 5074730976477 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5242469329/10000000000 : ℝ), (5680132319/10000000000 : ℝ), (-110945797/625000000 : ℝ)] ![(1701758319059/4000000000000 : ℝ), (1182664501199/2500000000000 : ℝ), (5074730976477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5242469329/10000000000 : ℝ)|^8381 ≤ (1701758319059/4000000000000 : ℝ)^6333
        have hw : |(5242469329/10000000000 : ℝ)|=(5242469329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5680132319/10000000000 : ℝ)|^8381 ≤ (1182664501199/2500000000000 : ℝ)^6333
        have hw : |(5680132319/10000000000 : ℝ)|=(5680132319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-110945797/625000000 : ℝ)|^8381 ≤ (5074730976477/50000000000000 : ℝ)^6333
        have hw : |(-110945797/625000000 : ℝ)|=(110945797/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s1_7 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4315006039/10000000000 : ℝ)*x 0 + (251384323/500000000 : ℝ)*x 1 + (370418639/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315006039/10000000000 : ℝ)^8381 ≤ (32880598142729/100000000000000 : ℝ)^6333 := by
    have hnat : (4315006039 : ℕ)^8381*100000000000000^6333 ≤ 32880598142729^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315006039 10000000000 32880598142729 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (251384323/500000000 : ℝ)^8381 ≤ (2515793684121/6250000000000 : ℝ)^6333 := by
    have hnat : (251384323 : ℕ)^8381*6250000000000^6333 ≤ 2515793684121^6333*500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251384323 500000000 2515793684121 6250000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (370418639/1000000000 : ℝ)^8381 ≤ (26866702897053/100000000000000 : ℝ)^6333 := by
    have hnat : (370418639 : ℕ)^8381*100000000000000^6333 ≤ 26866702897053^6333*1000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370418639 1000000000 26866702897053 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315006039/10000000000 : ℝ), (251384323/500000000 : ℝ), (370418639/1000000000 : ℝ)] ![(32880598142729/100000000000000 : ℝ), (2515793684121/6250000000000 : ℝ), (26866702897053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315006039/10000000000 : ℝ)|^8381 ≤ (32880598142729/100000000000000 : ℝ)^6333
        have hw : |(4315006039/10000000000 : ℝ)|=(4315006039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(251384323/500000000 : ℝ)|^8381 ≤ (2515793684121/6250000000000 : ℝ)^6333
        have hw : |(251384323/500000000 : ℝ)|=(251384323/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(370418639/1000000000 : ℝ)|^8381 ≤ (26866702897053/100000000000000 : ℝ)^6333
        have hw : |(370418639/1000000000 : ℝ)|=(370418639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1188_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (691/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (601/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5903/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2529/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (691/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (601/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (691/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (601/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (691/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (601/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (691/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (601/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (691/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (601/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (691/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (601/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (601/100000 : ℝ) ^ (2095/512 : ℝ) ≤ (40792047991/50000000000000000000 : ℝ) := by
    have hpowers : (601/100000 : ℝ)^2095 ≤ (40792047991/50000000000000000000 : ℝ)^512 := by
      have hnat : (601 : ℕ)^2095*50000000000000000000^512 ≤ 40792047991^512*100000^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        601 100000 40792047991 50000000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (601/100000 : ℝ)) (X := (40792047991/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hpowhi : (691/2500 : ℝ) ^ (2095/512 : ℝ) ≤ (51866517862845571/10000000000000000000 : ℝ) := by
    have hpowers : (691/2500 : ℝ)^2095 ≤ (51866517862845571/10000000000000000000 : ℝ)^512 := by
      have hnat : (691 : ℕ)^2095*10000000000000000000^512 ≤ 51866517862845571^512*2500^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        691 2500 51866517862845571 10000000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (691/2500 : ℝ)) (X := (51866517862845571/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000040792047991/25000000000000000000 : ℝ) ≤ (10000000003987691/10000000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (25000000040792047991/25000000000000000000 : ℝ)^512 ≤ (10000000003987691/10000000000000000 : ℝ)^2095 := by
      have hnat : (25000000040792047991 : ℕ)^512*10000000000000000^2095 ≤ 10000000003987691^2095*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000040792047991 25000000000000000000 10000000003987691 10000000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000003987691/10000000000000000 : ℝ)) (X := (25000000040792047991/25000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25129666315053137923/25000000000000000000 : ℝ) ≤ (2503162742462343/2500000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (25129666315053137923/25000000000000000000 : ℝ)^512 ≤ (2503162742462343/2500000000000000 : ℝ)^2095 := by
      have hnat : (25129666315053137923 : ℕ)^512*2500000000000000^2095 ≤ 2503162742462343^2095*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25129666315053137923 25000000000000000000 2503162742462343 2500000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503162742462343/2500000000000000 : ℝ)) (X := (25129666315053137923/25000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5051866517862845571/5000000000000000000 : ℝ) ≤ (10025301935711053/10000000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (5051866517862845571/5000000000000000000 : ℝ)^512 ≤ (10025301935711053/10000000000000000 : ℝ)^2095 := by
      have hnat : (5051866517862845571 : ℕ)^512*10000000000000000^2095 ≤ 10025301935711053^2095*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5051866517862845571 5000000000000000000 10025301935711053 10000000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10025301935711053/10000000000000000 : ℝ)) (X := (5051866517862845571/5000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(40792047991/50000000000000000000 : ℝ) ≤ ((270374793646857436387/270390000000000000000 : ℝ)+2*(12650965861681/2703900000000000 : ℝ)*(601/100000 : ℝ))^(2095/512 : ℝ) := by
    rw [show (270374793646857436387/270390000000000000000 : ℝ)+2*(12650965861681/2703900000000000 : ℝ)*(601/100000 : ℝ)=(10000000003987691/10000000000000000 : ℝ) by norm_num, show 1+2*(40792047991/50000000000000000000 : ℝ)=(25000000040792047991/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(51866517862845571/10000000000000000000 : ℝ)+(40792047991/50000000000000000000 : ℝ) ≤ ((270374793646857436387/270390000000000000000 : ℝ)+(12650965861681/2703900000000000 : ℝ)*((691/2500 : ℝ)+(601/100000 : ℝ)))^(2095/512 : ℝ) := by
    rw [show (270374793646857436387/270390000000000000000 : ℝ)+(12650965861681/2703900000000000 : ℝ)*((691/2500 : ℝ)+(601/100000 : ℝ))=(2503162742462343/2500000000000000 : ℝ) by norm_num, show 1+(51866517862845571/10000000000000000000 : ℝ)+(40792047991/50000000000000000000 : ℝ)=(25129666315053137923/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(51866517862845571/10000000000000000000 : ℝ) ≤ ((270374793646857436387/270390000000000000000 : ℝ)+2*(12650965861681/2703900000000000 : ℝ)*(691/2500 : ℝ))^(2095/512 : ℝ) := by
    rw [show (270374793646857436387/270390000000000000000 : ℝ)+2*(12650965861681/2703900000000000 : ℝ)*(691/2500 : ℝ)=(10025301935711053/10000000000000000 : ℝ) by norm_num, show 1+2*(51866517862845571/10000000000000000000 : ℝ)=(5051866517862845571/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (270374793646857436387/270390000000000000000 : ℝ)*(X 1 0+X 2 0)+(12650965861681/2703900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (601/100000 : ℝ)) (hi := (691/2500 : ℝ)) (c := (270374793646857436387/270390000000000000000 : ℝ)) (alpha := (12650965861681/2703900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (270374793646857436387/270390000000000000000 : ℝ)*(X 0 1+X 2 1)+(12650965861681/2703900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (601/100000 : ℝ)) (hi := (691/2500 : ℝ)) (c := (270374793646857436387/270390000000000000000 : ℝ)) (alpha := (12650965861681/2703900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (270374793646857436387/270390000000000000000 : ℝ)*(X 0 2+X 1 2)+(12650965861681/2703900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (601/100000 : ℝ)) (hi := (691/2500 : ℝ)) (c := (270374793646857436387/270390000000000000000 : ℝ)) (alpha := (12650965861681/2703900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1039334171/5000000000 : ℝ)*X 0 0+(5689399183/10000000000 : ℝ)*X 0 1+(1002348623/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2708301911/5000000000 : ℝ)*X 1 0+(-1221760777/5000000000 : ℝ)*X 1 1+(626467923/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5416602931/10000000000 : ℝ)*X 2 0+(2505871987/5000000000 : ℝ)*X 2 1+(-1221760981/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1078378403/2500000000 : ℝ)*X 0 0+(3685582243/10000000000 : ℝ)*X 0 1+(2522968239/5000000000 : ℝ)*X 0 2+(1078378403/2500000000 : ℝ)*X 1 0+(3685582243/10000000000 : ℝ)*X 1 1+(2522968239/5000000000 : ℝ)*X 1 2+(1078378403/2500000000 : ℝ)*X 2 0+(3685582243/10000000000 : ℝ)*X 2 1+(2522968239/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2079412669/10000000000 : ℝ)*X 0 0+(5020834533/10000000000 : ℝ)*X 0 1+(5680130579/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2621234761/5000000000 : ℝ)*X 1 0+(-443783403/2500000000 : ℝ)*X 1 1+(2840065771/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5242469329/10000000000 : ℝ)*X 2 0+(5680132319/10000000000 : ℝ)*X 2 1+(-110945797/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4315006039/10000000000 : ℝ)*X 0 0+(251384323/500000000 : ℝ)*X 0 1+(370418639/1000000000 : ℝ)*X 0 2+(4315006039/10000000000 : ℝ)*X 1 0+(251384323/500000000 : ℝ)*X 1 1+(370418639/1000000000 : ℝ)*X 1 2+(4315006039/10000000000 : ℝ)*X 2 0+(251384323/500000000 : ℝ)*X 2 1+(370418639/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20616503540122723654687249167/4506500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (238482021/20000000000000 : ℝ)*(base19) + (938448763/100000000000000 : ℝ)*(base23) + (120594847/50000000000000 : ℝ)*(upper3) + (6076981/100000000000000 : ℝ)*(upper4) + (9897477/50000000000000 : ℝ)*(upper5) + (1105399604002647/100000000000000 : ℝ)*(major0) + (1105399604002647/100000000000000 : ℝ)*(major1) + (1105399604002647/100000000000000 : ℝ)*(major2) + (147568323315281/10000000000000 : ℝ)*(sp0) + (737843962610127/50000000000000 : ℝ)*(sp1) + (368922044795399/25000000000000 : ℝ)*(sp2) + (367552936696343/50000000000000 : ℝ)*(sp3) + (5884477549/100000000000000 : ℝ)*(sp4) + (2032243837/50000000000000 : ℝ)*(sp7) + (18377748447009/2500000000000 : ℝ)*(f.failure) + (1475689117630359/100000000000000 : ℝ)*(f.sum) + (29829685675809/11266250000000000000000000000 : ℝ)*base66 + (24551884522157394537/9013000000000000000000000000000000 : ℝ)*base68 + (19186519564809394537/9013000000000000000000000000000000 : ℝ)*base70 + (52966208124330394537/9013000000000000000000000000000000 : ℝ)*base72 + (212056901388439/45065000000000000000000000000 : ℝ)*base73 + (36789138531504394537/9013000000000000000000000000000000 : ℝ)*base76 + (35540898328474394537/9013000000000000000000000000000000 : ℝ)*base78 + (56945946367698394537/9013000000000000000000000000000000 : ℝ)*base80 + (76901045117829/45065000000000000000000000000 : ℝ)*base81 + (303027/62500000000000000000 : ℝ)*base89 + (303027/62500000000000000000 : ℝ)*base91 + (303027/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (498503573561572135347304967/140828125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14752593/1000000000000 : ℝ)*(base19) + (1830326191/100000000000000 : ℝ)*(base23) + (147821127/100000000000000 : ℝ)*(upper2) + (69936091/25000000000000 : ℝ)*(upper3) + (37091509/25000000000000 : ℝ)*(upper5) + (35505313179197/3125000000000 : ℝ)*(major0) + (35505313179197/3125000000000 : ℝ)*(major1) + (35505313179197/3125000000000 : ℝ)*(major2) + (150694747/2000000000000 : ℝ)*(sp1) + (5708283687/50000000000000 : ℝ)*(sp2) + (189595890663657/12500000000000 : ℝ)*(sp4) + (758379057656303/50000000000000 : ℝ)*(sp5) + (1516753878415691/100000000000000 : ℝ)*(sp6) + (47223300010373/6250000000000 : ℝ)*(sp7) + (47223300010373/6250000000000 : ℝ)*(f.failure) + (189595890663657/12500000000000 : ℝ)*(f.sum) + (42681205973767/16899375000000000000000000000 : ℝ)*base66 + (9158212547399808761/844968750000000000000000000000000 : ℝ)*base68 + (7441560528919308761/844968750000000000000000000000000 : ℝ)*base70 + (10496724211718058761/844968750000000000000000000000000 : ℝ)*base72 + (124627164071009/33798750000000000000000000000 : ℝ)*base74 + (8061490127340933761/844968750000000000000000000000000 : ℝ)*base76 + (9578808042922402511/844968750000000000000000000000000 : ℝ)*base78 + (11309489682556777511/844968750000000000000000000000000 : ℝ)*base80 + (57694866391381/33798750000000000000000000000 : ℝ)*base81 + (2220119/156250000000000000000 : ℝ)*base89 + (2220119/156250000000000000000 : ℝ)*base91 + (2220119/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1188_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (691/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (601/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5903/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2529/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1188_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1188_s2_0 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2129469501/10000000000 : ℝ)*x 0 + (2751138243/5000000000 : ℝ)*x 1 + (2583259357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129469501/10000000000 : ℝ)^8381 ≤ (2582701281937/20000000000000 : ℝ)^6333 := by
    have hnat : (2129469501 : ℕ)^8381*20000000000000^6333 ≤ 2582701281937^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129469501 10000000000 2582701281937 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2751138243/5000000000 : ℝ)^8381 ≤ (5669537279081/12500000000000 : ℝ)^6333 := by
    have hnat : (2751138243 : ℕ)^8381*12500000000000^6333 ≤ 5669537279081^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751138243 5000000000 5669537279081 12500000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2583259357/5000000000 : ℝ)^8381 ≤ (10432548835339/25000000000000 : ℝ)^6333 := by
    have hnat : (2583259357 : ℕ)^8381*25000000000000^6333 ≤ 10432548835339^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583259357 5000000000 10432548835339 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2129469501/10000000000 : ℝ), (2751138243/5000000000 : ℝ), (2583259357/5000000000 : ℝ)] ![(2582701281937/20000000000000 : ℝ), (5669537279081/12500000000000 : ℝ), (10432548835339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2129469501/10000000000 : ℝ)|^8381 ≤ (2582701281937/20000000000000 : ℝ)^6333
        have hw : |(-2129469501/10000000000 : ℝ)|=(2129469501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2751138243/5000000000 : ℝ)|^8381 ≤ (5669537279081/12500000000000 : ℝ)^6333
        have hw : |(2751138243/5000000000 : ℝ)|=(2751138243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2583259357/5000000000 : ℝ)|^8381 ≤ (10432548835339/25000000000000 : ℝ)^6333
        have hw : |(2583259357/5000000000 : ℝ)|=(2583259357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s2_1 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2685956291/5000000000 : ℝ)*x 0 + (-230372389/1000000000 : ℝ)*x 1 + (2583261301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685956291/5000000000 : ℝ)^8381 ≤ (10984911755483/25000000000000 : ℝ)^6333 := by
    have hnat : (2685956291 : ℕ)^8381*25000000000000^6333 ≤ 10984911755483^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685956291 5000000000 10984911755483 25000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (230372389/1000000000 : ℝ)^8381 ≤ (14330116066717/100000000000000 : ℝ)^6333 := by
    have hnat : (230372389 : ℕ)^8381*100000000000000^6333 ≤ 14330116066717^6333*1000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230372389 1000000000 14330116066717 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2583261301/5000000000 : ℝ)^8381 ≤ (20865118450177/50000000000000 : ℝ)^6333 := by
    have hnat : (2583261301 : ℕ)^8381*50000000000000^6333 ≤ 20865118450177^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583261301 5000000000 20865118450177 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685956291/5000000000 : ℝ), (-230372389/1000000000 : ℝ), (2583261301/5000000000 : ℝ)] ![(10984911755483/25000000000000 : ℝ), (14330116066717/100000000000000 : ℝ), (20865118450177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685956291/5000000000 : ℝ)|^8381 ≤ (10984911755483/25000000000000 : ℝ)^6333
        have hw : |(2685956291/5000000000 : ℝ)|=(2685956291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-230372389/1000000000 : ℝ)|^8381 ≤ (14330116066717/100000000000000 : ℝ)^6333
        have hw : |(-230372389/1000000000 : ℝ)|=(230372389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2583261301/5000000000 : ℝ)|^8381 ≤ (20865118450177/50000000000000 : ℝ)^6333
        have hw : |(2583261301/5000000000 : ℝ)|=(2583261301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s2_2 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (214876563/400000000 : ℝ)*x 0 + (516652049/1000000000 : ℝ)*x 1 + (-2303724669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214876563/400000000 : ℝ)^8381 ≤ (2196983159157/5000000000000 : ℝ)^6333 := by
    have hnat : (214876563 : ℕ)^8381*5000000000000^6333 ≤ 2196983159157^6333*400000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214876563 400000000 2196983159157 5000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516652049/1000000000 : ℝ)^8381 ≤ (8346042865019/20000000000000 : ℝ)^6333 := by
    have hnat : (516652049 : ℕ)^8381*20000000000000^6333 ≤ 8346042865019^6333*1000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516652049 1000000000 8346042865019 20000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2303724669/10000000000 : ℝ)^8381 ≤ (286602449589/2000000000000 : ℝ)^6333 := by
    have hnat : (2303724669 : ℕ)^8381*2000000000000^6333 ≤ 286602449589^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2303724669 10000000000 286602449589 2000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214876563/400000000 : ℝ), (516652049/1000000000 : ℝ), (-2303724669/10000000000 : ℝ)] ![(2196983159157/5000000000000 : ℝ), (8346042865019/20000000000000 : ℝ), (286602449589/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214876563/400000000 : ℝ)|^8381 ≤ (2196983159157/5000000000000 : ℝ)^6333
        have hw : |(214876563/400000000 : ℝ)|=(214876563/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(516652049/1000000000 : ℝ)|^8381 ≤ (8346042865019/20000000000000 : ℝ)^6333
        have hw : |(516652049/1000000000 : ℝ)|=(516652049/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2303724669/10000000000 : ℝ)|^8381 ≤ (286602449589/2000000000000 : ℝ)^6333
        have hw : |(-2303724669/10000000000 : ℝ)|=(2303724669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s2_3 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174239257/5000000000 : ℝ)*x 0 + (4024279289/10000000000 : ℝ)*x 1 + (4698288629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174239257/5000000000 : ℝ)^8381 ≤ (33218566405813/100000000000000 : ℝ)^6333 := by
    have hnat : (2174239257 : ℕ)^8381*100000000000000^6333 ≤ 33218566405813^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174239257 5000000000 33218566405813 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4024279289/10000000000 : ℝ)^8381 ≤ (1499063428143/5000000000000 : ℝ)^6333 := by
    have hnat : (4024279289 : ℕ)^8381*5000000000000^6333 ≤ 1499063428143^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024279289 10000000000 1499063428143 5000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4698288629/10000000000 : ℝ)^8381 ≤ (36800165014077/100000000000000 : ℝ)^6333 := by
    have hnat : (4698288629 : ℕ)^8381*100000000000000^6333 ≤ 36800165014077^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4698288629 10000000000 36800165014077 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174239257/5000000000 : ℝ), (4024279289/10000000000 : ℝ), (4698288629/10000000000 : ℝ)] ![(33218566405813/100000000000000 : ℝ), (1499063428143/5000000000000 : ℝ), (36800165014077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174239257/5000000000 : ℝ)|^8381 ≤ (33218566405813/100000000000000 : ℝ)^6333
        have hw : |(2174239257/5000000000 : ℝ)|=(2174239257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4024279289/10000000000 : ℝ)|^8381 ≤ (1499063428143/5000000000000 : ℝ)^6333
        have hw : |(4024279289/10000000000 : ℝ)|=(4024279289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4698288629/10000000000 : ℝ)|^8381 ≤ (36800165014077/100000000000000 : ℝ)^6333
        have hw : |(4698288629/10000000000 : ℝ)|=(4698288629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s2_4 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064779577/5000000000 : ℝ)*x 0 + (5168761573/10000000000 : ℝ)*x 1 + (5500012573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064779577/5000000000 : ℝ)^8381 ≤ (12914225903217/100000000000000 : ℝ)^6333 := by
    have hnat : (1064779577 : ℕ)^8381*100000000000000^6333 ≤ 12914225903217^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064779577 5000000000 12914225903217 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5168761573/10000000000 : ℝ)^8381 ≤ (20877085518473/50000000000000 : ℝ)^6333 := by
    have hnat : (5168761573 : ℕ)^8381*50000000000000^6333 ≤ 20877085518473^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168761573 10000000000 20877085518473 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5500012573/10000000000 : ℝ)^8381 ≤ (1813264121683/4000000000000 : ℝ)^6333 := by
    have hnat : (5500012573 : ℕ)^8381*4000000000000^6333 ≤ 1813264121683^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500012573 10000000000 1813264121683 4000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064779577/5000000000 : ℝ), (5168761573/10000000000 : ℝ), (5500012573/10000000000 : ℝ)] ![(12914225903217/100000000000000 : ℝ), (20877085518473/50000000000000 : ℝ), (1813264121683/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064779577/5000000000 : ℝ)|^8381 ≤ (12914225903217/100000000000000 : ℝ)^6333
        have hw : |(-1064779577/5000000000 : ℝ)|=(1064779577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5168761573/10000000000 : ℝ)|^8381 ≤ (20877085518473/50000000000000 : ℝ)^6333
        have hw : |(5168761573/10000000000 : ℝ)|=(5168761573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5500012573/10000000000 : ℝ)|^8381 ≤ (1813264121683/4000000000000 : ℝ)^6333
        have hw : |(5500012573/10000000000 : ℝ)|=(5500012573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s2_5 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2643232277/5000000000 : ℝ)*x 0 + (-985116187/5000000000 : ℝ)*x 1 + (687501573/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643232277/5000000000 : ℝ)^8381 ≤ (21508544643711/50000000000000 : ℝ)^6333 := by
    have hnat : (2643232277 : ℕ)^8381*50000000000000^6333 ≤ 21508544643711^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643232277 5000000000 21508544643711 50000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (985116187/5000000000 : ℝ)^8381 ≤ (11651307531697/100000000000000 : ℝ)^6333 := by
    have hnat : (985116187 : ℕ)^8381*100000000000000^6333 ≤ 11651307531697^6333*5000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985116187 5000000000 11651307531697 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (687501573/1250000000 : ℝ)^8381 ≤ (45331603162057/100000000000000 : ℝ)^6333 := by
    have hnat : (687501573 : ℕ)^8381*100000000000000^6333 ≤ 45331603162057^6333*1250000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687501573 1250000000 45331603162057 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643232277/5000000000 : ℝ), (-985116187/5000000000 : ℝ), (687501573/1250000000 : ℝ)] ![(21508544643711/50000000000000 : ℝ), (11651307531697/100000000000000 : ℝ), (45331603162057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643232277/5000000000 : ℝ)|^8381 ≤ (21508544643711/50000000000000 : ℝ)^6333
        have hw : |(2643232277/5000000000 : ℝ)|=(2643232277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-985116187/5000000000 : ℝ)|^8381 ≤ (11651307531697/100000000000000 : ℝ)^6333
        have hw : |(-985116187/5000000000 : ℝ)|=(985116187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(687501573/1250000000 : ℝ)|^8381 ≤ (45331603162057/100000000000000 : ℝ)^6333
        have hw : |(687501573/1250000000 : ℝ)|=(687501573/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s2_6 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5286464713/10000000000 : ℝ)*x 0 + (5500012591/10000000000 : ℝ)*x 1 + (-394046429/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286464713/10000000000 : ℝ)^8381 ≤ (1075427274991/2500000000000 : ℝ)^6333 := by
    have hnat : (5286464713 : ℕ)^8381*2500000000000^6333 ≤ 1075427274991^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286464713 10000000000 1075427274991 2500000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5500012591/10000000000 : ℝ)^8381 ≤ (45331603238409/100000000000000 : ℝ)^6333 := by
    have hnat : (5500012591 : ℕ)^8381*100000000000000^6333 ≤ 45331603238409^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500012591 10000000000 45331603238409 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394046429/2000000000 : ℝ)^8381 ≤ (1456413217441/12500000000000 : ℝ)^6333 := by
    have hnat : (394046429 : ℕ)^8381*12500000000000^6333 ≤ 1456413217441^6333*2000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394046429 2000000000 1456413217441 12500000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286464713/10000000000 : ℝ), (5500012591/10000000000 : ℝ), (-394046429/2000000000 : ℝ)] ![(1075427274991/2500000000000 : ℝ), (45331603238409/100000000000000 : ℝ), (1456413217441/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286464713/10000000000 : ℝ)|^8381 ≤ (1075427274991/2500000000000 : ℝ)^6333
        have hw : |(5286464713/10000000000 : ℝ)|=(5286464713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5500012591/10000000000 : ℝ)|^8381 ≤ (45331603238409/100000000000000 : ℝ)^6333
        have hw : |(5500012591/10000000000 : ℝ)|=(5500012591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-394046429/2000000000 : ℝ)|^8381 ≤ (1456413217441/12500000000000 : ℝ)^6333
        have hw : |(-394046429/2000000000 : ℝ)|=(394046429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1188_s2_7 (p : ℝ) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348660601/10000000000 : ℝ)*x 0 + (1173447223/2500000000 : ℝ)*x 1 + (1007205457/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348660601/10000000000 : ℝ)^8381 ≤ (2076275451737/6250000000000 : ℝ)^6333 := by
    have hnat : (4348660601 : ℕ)^8381*6250000000000^6333 ≤ 2076275451737^6333*10000000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348660601 10000000000 2076275451737 6250000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1173447223/2500000000 : ℝ)^8381 ≤ (36753529552231/100000000000000 : ℝ)^6333 := by
    have hnat : (1173447223 : ℕ)^8381*100000000000000^6333 ≤ 36753529552231^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173447223 2500000000 36753529552231 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007205457/2500000000 : ℝ)^8381 ≤ (30026063212767/100000000000000 : ℝ)^6333 := by
    have hnat : (1007205457 : ℕ)^8381*100000000000000^6333 ≤ 30026063212767^6333*2500000000^8381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007205457 2500000000 30026063212767 100000000000000 8381 6333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8381/2048 : ℝ)) 8381 6333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348660601/10000000000 : ℝ), (1173447223/2500000000 : ℝ), (1007205457/2500000000 : ℝ)] ![(2076275451737/6250000000000 : ℝ), (36753529552231/100000000000000 : ℝ), (30026063212767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348660601/10000000000 : ℝ)|^8381 ≤ (2076275451737/6250000000000 : ℝ)^6333
        have hw : |(4348660601/10000000000 : ℝ)|=(4348660601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1173447223/2500000000 : ℝ)|^8381 ≤ (36753529552231/100000000000000 : ℝ)^6333
        have hw : |(1173447223/2500000000 : ℝ)|=(1173447223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1007205457/2500000000 : ℝ)|^8381 ≤ (30026063212767/100000000000000 : ℝ)^6333
        have hw : |(1007205457/2500000000 : ℝ)|=(1007205457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1188_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2529/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5903/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9273/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16369/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2529/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5903/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2529/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5903/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2529/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5903/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2529/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5903/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2529/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5903/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2529/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5903/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5903/100000 : ℝ) ^ (2095/512 : ℝ) ≤ (234109729656267/25000000000000000000 : ℝ) := by
    have hpowers : (5903/100000 : ℝ)^2095 ≤ (234109729656267/25000000000000000000 : ℝ)^512 := by
      have hnat : (5903 : ℕ)^2095*25000000000000000000^512 ≤ 234109729656267^512*100000^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5903 100000 234109729656267 25000000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5903/100000 : ℝ)) (X := (234109729656267/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2529/12500 : ℝ) ^ (2095/512 : ℝ) ≤ (28938884934036843/20000000000000000000 : ℝ) := by
    have hpowers : (2529/12500 : ℝ)^2095 ≤ (28938884934036843/20000000000000000000 : ℝ)^512 := by
      have hnat : (2529 : ℕ)^2095*20000000000000000000^512 ≤ 28938884934036843^512*12500^2095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2529 12500 28938884934036843 20000000000000000000 2095 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2529/12500 : ℝ)) (X := (28938884934036843/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500234109729656267/12500000000000000000 : ℝ) ≤ (10000045771201321/10000000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (12500234109729656267/12500000000000000000 : ℝ)^512 ≤ (10000045771201321/10000000000000000 : ℝ)^2095 := by
      have hnat : (12500234109729656267 : ℕ)^512*10000000000000000^2095 ≤ 10000045771201321^2095*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500234109729656267 12500000000000000000 10000045771201321 10000000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000045771201321/10000000000000000 : ℝ)) (X := (12500234109729656267/12500000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100145630863588809283/100000000000000000000 : ℝ) ≤ (10003557136637073/10000000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (100145630863588809283/100000000000000000000 : ℝ)^512 ≤ (10003557136637073/10000000000000000 : ℝ)^2095 := by
      have hnat : (100145630863588809283 : ℕ)^512*10000000000000000^2095 ≤ 10003557136637073^2095*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100145630863588809283 100000000000000000000 10003557136637073 10000000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003557136637073/10000000000000000 : ℝ)) (X := (100145630863588809283/100000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10028938884934036843/10000000000000000000 : ℝ) ≤ (400282740082913/400000000000000 : ℝ) ^ (2095/512 : ℝ) := by
    have hpowers : (10028938884934036843/10000000000000000000 : ℝ)^512 ≤ (400282740082913/400000000000000 : ℝ)^2095 := by
      have hnat : (10028938884934036843 : ℕ)^512*400000000000000^2095 ≤ 400282740082913^2095*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10028938884934036843 10000000000000000000 400282740082913 400000000000000 512 2095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400282740082913/400000000000000 : ℝ)) (X := (10028938884934036843/10000000000000000000 : ℝ)) (by norm_num) 2095 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(234109729656267/25000000000000000000 : ℝ) ≤ ((6228226116313445239/6230000000000000000 : ℝ)+2*(19083507803/7787500000000 : ℝ)*(5903/100000 : ℝ))^(2095/512 : ℝ) := by
    rw [show (6228226116313445239/6230000000000000000 : ℝ)+2*(19083507803/7787500000000 : ℝ)*(5903/100000 : ℝ)=(10000045771201321/10000000000000000 : ℝ) by norm_num, show 1+2*(234109729656267/25000000000000000000 : ℝ)=(12500234109729656267/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28938884934036843/20000000000000000000 : ℝ)+(234109729656267/25000000000000000000 : ℝ) ≤ ((6228226116313445239/6230000000000000000 : ℝ)+(19083507803/7787500000000 : ℝ)*((2529/12500 : ℝ)+(5903/100000 : ℝ)))^(2095/512 : ℝ) := by
    rw [show (6228226116313445239/6230000000000000000 : ℝ)+(19083507803/7787500000000 : ℝ)*((2529/12500 : ℝ)+(5903/100000 : ℝ))=(10003557136637073/10000000000000000 : ℝ) by norm_num, show 1+(28938884934036843/20000000000000000000 : ℝ)+(234109729656267/25000000000000000000 : ℝ)=(100145630863588809283/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28938884934036843/20000000000000000000 : ℝ) ≤ ((6228226116313445239/6230000000000000000 : ℝ)+2*(19083507803/7787500000000 : ℝ)*(2529/12500 : ℝ))^(2095/512 : ℝ) := by
    rw [show (6228226116313445239/6230000000000000000 : ℝ)+2*(19083507803/7787500000000 : ℝ)*(2529/12500 : ℝ)=(400282740082913/400000000000000 : ℝ) by norm_num, show 1+2*(28938884934036843/20000000000000000000 : ℝ)=(10028938884934036843/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6228226116313445239/6230000000000000000 : ℝ)*(X 1 0+X 2 0)+(19083507803/7787500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (5903/100000 : ℝ)) (hi := (2529/12500 : ℝ)) (c := (6228226116313445239/6230000000000000000 : ℝ)) (alpha := (19083507803/7787500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6228226116313445239/6230000000000000000 : ℝ)*(X 0 1+X 2 1)+(19083507803/7787500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (5903/100000 : ℝ)) (hi := (2529/12500 : ℝ)) (c := (6228226116313445239/6230000000000000000 : ℝ)) (alpha := (19083507803/7787500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6228226116313445239/6230000000000000000 : ℝ)*(X 0 2+X 1 2)+(19083507803/7787500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2095/512 : ℝ)) (lo := (5903/100000 : ℝ)) (hi := (2529/12500 : ℝ)) (c := (6228226116313445239/6230000000000000000 : ℝ)) (alpha := (19083507803/7787500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2129469501/10000000000 : ℝ)*X 0 0+(2751138243/5000000000 : ℝ)*X 0 1+(2583259357/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2685956291/5000000000 : ℝ)*X 1 0+(-230372389/1000000000 : ℝ)*X 1 1+(2583261301/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214876563/400000000 : ℝ)*X 2 0+(516652049/1000000000 : ℝ)*X 2 1+(-2303724669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2174239257/5000000000 : ℝ)*X 0 0+(4024279289/10000000000 : ℝ)*X 0 1+(4698288629/10000000000 : ℝ)*X 0 2+(2174239257/5000000000 : ℝ)*X 1 0+(4024279289/10000000000 : ℝ)*X 1 1+(4698288629/10000000000 : ℝ)*X 1 2+(2174239257/5000000000 : ℝ)*X 2 0+(4024279289/10000000000 : ℝ)*X 2 1+(4698288629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1064779577/5000000000 : ℝ)*X 0 0+(5168761573/10000000000 : ℝ)*X 0 1+(5500012573/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643232277/5000000000 : ℝ)*X 1 0+(-985116187/5000000000 : ℝ)*X 1 1+(687501573/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5286464713/10000000000 : ℝ)*X 2 0+(5500012591/10000000000 : ℝ)*X 2 1+(-394046429/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4348660601/10000000000 : ℝ)*X 0 0+(1173447223/2500000000 : ℝ)*X 0 1+(1007205457/2500000000 : ℝ)*X 0 2+(4348660601/10000000000 : ℝ)*X 1 0+(1173447223/2500000000 : ℝ)*X 1 1+(1007205457/2500000000 : ℝ)*X 1 2+(4348660601/10000000000 : ℝ)*X 2 0+(1173447223/2500000000 : ℝ)*X 2 1+(1007205457/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1188_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (182007234641572366461414087/22250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (143913019/12500000000000 : ℝ)*(base19) + (206428929/12500000000000 : ℝ)*(base23) + (68301953/100000000000000 : ℝ)*(upper2) + (4698589/800000000000 : ℝ)*(upper3) + (244314423/100000000000000 : ℝ)*(upper4) + (2231048492165277/100000000000000 : ℝ)*(major0) + (2231048492165277/100000000000000 : ℝ)*(major1) + (2231048492165277/100000000000000 : ℝ)*(major2) + (297837691159061/10000000000000 : ℝ)*(sp0) + (148920477944569/5000000000000 : ℝ)*(sp1) + (29784090587641/1000000000000 : ℝ)*(sp2) + (1483668878067347/100000000000000 : ℝ)*(sp3) + (16899302461/50000000000000 : ℝ)*(sp4) + (8561698829/50000000000000 : ℝ)*(sp7) + (296737200293001/20000000000000 : ℝ)*(f.failure) + (744602677548883/25000000000000 : ℝ)*(f.sum) + (4210246038689/1557500000000000000000000000 : ℝ)*base65 + (663341048633433797/623000000000000000000000000000000 : ℝ)*base68 + (853970294237433797/623000000000000000000000000000000 : ℝ)*base70 + (1333407447026433797/623000000000000000000000000000000 : ℝ)*base72 + (3635211452737/3115000000000000000000000000 : ℝ)*base74 + (3284673893659433797/623000000000000000000000000000000 : ℝ)*base76 + (721642569153566203/623000000000000000000000000000000 : ℝ)*base77 + (1051314444415433797/623000000000000000000000000000000 : ℝ)*base80 + (12611925526057/3115000000000000000000000000 : ℝ)*base82 + (2472003/500000000000000000000 : ℝ)*base89 + (2472003/500000000000000000000 : ℝ)*base91 + (2472003/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (496563853402796683185048243/311500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36660079/6250000000000 : ℝ)*(base19) + (828562301/100000000000000 : ℝ)*(base23) + (23251473/50000000000000 : ℝ)*(upper2) + (45039841/50000000000000 : ℝ)*(upper3) + (9192857/25000000000000 : ℝ)*(upper5) + (2261346159290121/100000000000000 : ℝ)*(major0) + (2261346159290121/100000000000000 : ℝ)*(major1) + (2261346159290121/100000000000000 : ℝ)*(major2) + (5313289819/100000000000000 : ℝ)*(sp1) + (9225490993/100000000000000 : ℝ)*(sp2) + (754714447264541/25000000000000 : ℝ)*(sp4) + (1509425944603541/50000000000000 : ℝ)*(sp5) + (301884773500487/10000000000000 : ℝ)*(sp6) + (75191723819261/5000000000000 : ℝ)*(sp7) + (75191723819261/5000000000000 : ℝ)*(f.failure) + (754714447264541/25000000000000 : ℝ)*(f.sum) + (4902343241361/778750000000000000000000000 : ℝ)*base65 + (5610427295301583919/623000000000000000000000000000000 : ℝ)*base67 + (223489635141583919/623000000000000000000000000000000 : ℝ)*base69 + (99629027739583919/623000000000000000000000000000000 : ℝ)*base71 + (9259026173087/1557500000000000000000000000 : ℝ)*base73 + (893931235200416081/623000000000000000000000000000000 : ℝ)*base76 + (6601752500262583919/623000000000000000000000000000000 : ℝ)*base77 + (3202613419162416081/623000000000000000000000000000000 : ℝ)*base80 + (2592931980391/3115000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1019217/125000000000000000000 : ℝ)*base90 + (1019217/125000000000000000000 : ℝ)*base92 + (1019217/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1188_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2529/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5903/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9273/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1188_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1188_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9273/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1188_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1188_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1188_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2095/512 : ℝ) ≤ p) (hpb : p ≤ (8381/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37593003/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9273/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1188_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
