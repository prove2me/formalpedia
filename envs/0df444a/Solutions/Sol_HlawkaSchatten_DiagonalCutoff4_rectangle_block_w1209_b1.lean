-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1209_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:06:23.359117+00:00
-- url     : https://prove2.me/submissions/60a0e170-656e-43cb-8c4d-9780b8998df1

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
theorem support_rectangle_w1209_s3_0 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2132120513/10000000000 : ℝ)*x 0 + (542262699/1000000000 : ℝ)*x 1 + (5237993077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132120513/10000000000 : ℝ)^4201 ≤ (202440138217/1562500000000 : ℝ)^3177 := by
    have hnat : (2132120513 : ℕ)^4201*1562500000000^3177 ≤ 202440138217^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132120513 10000000000 202440138217 1562500000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542262699/1000000000 : ℝ)^4201 ≤ (11129639844479/25000000000000 : ℝ)^3177 := by
    have hnat : (542262699 : ℕ)^4201*25000000000000^3177 ≤ 11129639844479^3177*1000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542262699 1000000000 11129639844479 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5237993077/10000000000 : ℝ)^4201 ≤ (21262635879563/50000000000000 : ℝ)^3177 := by
    have hnat : (5237993077 : ℕ)^4201*50000000000000^3177 ≤ 21262635879563^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237993077 10000000000 21262635879563 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2132120513/10000000000 : ℝ), (542262699/1000000000 : ℝ), (5237993077/10000000000 : ℝ)] ![(202440138217/1562500000000 : ℝ), (11129639844479/25000000000000 : ℝ), (21262635879563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2132120513/10000000000 : ℝ)|^4201 ≤ (202440138217/1562500000000 : ℝ)^3177
        have hw : |(-2132120513/10000000000 : ℝ)|=(2132120513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542262699/1000000000 : ℝ)|^4201 ≤ (11129639844479/25000000000000 : ℝ)^3177
        have hw : |(542262699/1000000000 : ℝ)|=(542262699/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5237993077/10000000000 : ℝ)|^4201 ≤ (21262635879563/50000000000000 : ℝ)^3177
        have hw : |(5237993077/10000000000 : ℝ)|=(5237993077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s3_1 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338056871/2500000000 : ℝ)*x 0 + (-222636807/1000000000 : ℝ)*x 1 + (2618996621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338056871/2500000000 : ℝ)^4201 ≤ (43755911332441/100000000000000 : ℝ)^3177 := by
    have hnat : (1338056871 : ℕ)^4201*100000000000000^3177 ≤ 43755911332441^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338056871 2500000000 43755911332441 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222636807/1000000000 : ℝ)^4201 ≤ (13718815121829/100000000000000 : ℝ)^3177 := by
    have hnat : (222636807 : ℕ)^4201*100000000000000^3177 ≤ 13718815121829^3177*1000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222636807 1000000000 13718815121829 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2618996621/5000000000 : ℝ)^4201 ≤ (8505054706093/20000000000000 : ℝ)^3177 := by
    have hnat : (2618996621 : ℕ)^4201*20000000000000^3177 ≤ 8505054706093^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618996621 5000000000 8505054706093 20000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338056871/2500000000 : ℝ), (-222636807/1000000000 : ℝ), (2618996621/5000000000 : ℝ)] ![(43755911332441/100000000000000 : ℝ), (13718815121829/100000000000000 : ℝ), (8505054706093/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338056871/2500000000 : ℝ)|^4201 ≤ (43755911332441/100000000000000 : ℝ)^3177
        have hw : |(1338056871/2500000000 : ℝ)|=(1338056871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-222636807/1000000000 : ℝ)|^4201 ≤ (13718815121829/100000000000000 : ℝ)^3177
        have hw : |(-222636807/1000000000 : ℝ)|=(222636807/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2618996621/5000000000 : ℝ)|^4201 ≤ (8505054706093/20000000000000 : ℝ)^3177
        have hw : |(2618996621/5000000000 : ℝ)|=(2618996621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s3_2 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352227377/10000000000 : ℝ)*x 0 + (5237993511/10000000000 : ℝ)*x 1 + (-1113183929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352227377/10000000000 : ℝ)^4201 ≤ (43755910175739/100000000000000 : ℝ)^3177 := by
    have hnat : (5352227377 : ℕ)^4201*100000000000000^3177 ≤ 43755910175739^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352227377 10000000000 43755910175739 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237993511/10000000000 : ℝ)^4201 ≤ (10631319104571/25000000000000 : ℝ)^3177 := by
    have hnat : (5237993511 : ℕ)^4201*25000000000000^3177 ≤ 10631319104571^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237993511 10000000000 10631319104571 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1113183929/5000000000 : ℝ)^4201 ≤ (13718813394437/100000000000000 : ℝ)^3177 := by
    have hnat : (1113183929 : ℕ)^4201*100000000000000^3177 ≤ 13718813394437^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113183929 5000000000 13718813394437 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352227377/10000000000 : ℝ), (5237993511/10000000000 : ℝ), (-1113183929/5000000000 : ℝ)] ![(43755910175739/100000000000000 : ℝ), (10631319104571/25000000000000 : ℝ), (13718813394437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352227377/10000000000 : ℝ)|^4201 ≤ (43755910175739/100000000000000 : ℝ)^3177
        have hw : |(5352227377/10000000000 : ℝ)|=(5352227377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237993511/10000000000 : ℝ)|^4201 ≤ (10631319104571/25000000000000 : ℝ)^3177
        have hw : |(5237993511/10000000000 : ℝ)|=(5237993511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1113183929/5000000000 : ℝ)|^4201 ≤ (13718813394437/100000000000000 : ℝ)^3177
        have hw : |(-1113183929/5000000000 : ℝ)|=(1113183929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s3_3 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (870690637/2000000000 : ℝ)*x 0 + (2085633137/5000000000 : ℝ)*x 1 + (2271711691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870690637/2000000000 : ℝ)^4201 ≤ (33298450446353/100000000000000 : ℝ)^3177 := by
    have hnat : (870690637 : ℕ)^4201*100000000000000^3177 ≤ 33298450446353^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870690637 2000000000 33298450446353 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085633137/5000000000 : ℝ)^4201 ≤ (31468347679827/100000000000000 : ℝ)^3177 := by
    have hnat : (2085633137 : ℕ)^4201*100000000000000^3177 ≤ 31468347679827^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085633137 5000000000 31468347679827 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2271711691/5000000000 : ℝ)^4201 ≤ (35233201859941/100000000000000 : ℝ)^3177 := by
    have hnat : (2271711691 : ℕ)^4201*100000000000000^3177 ≤ 35233201859941^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271711691 5000000000 35233201859941 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870690637/2000000000 : ℝ), (2085633137/5000000000 : ℝ), (2271711691/5000000000 : ℝ)] ![(33298450446353/100000000000000 : ℝ), (31468347679827/100000000000000 : ℝ), (35233201859941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870690637/2000000000 : ℝ)|^4201 ≤ (33298450446353/100000000000000 : ℝ)^3177
        have hw : |(870690637/2000000000 : ℝ)|=(870690637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085633137/5000000000 : ℝ)|^4201 ≤ (31468347679827/100000000000000 : ℝ)^3177
        have hw : |(2085633137/5000000000 : ℝ)|=(2085633137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2271711691/5000000000 : ℝ)|^4201 ≤ (35233201859941/100000000000000 : ℝ)^3177
        have hw : |(2271711691/5000000000 : ℝ)|=(2271711691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s3_4 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2132135763/10000000000 : ℝ)*x 0 + (5238678047/10000000000 : ℝ)*x 1 + (542193831/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132135763/10000000000 : ℝ)^4201 ≤ (3239072845963/25000000000000 : ℝ)^3177 := by
    have hnat : (2132135763 : ℕ)^4201*25000000000000^3177 ≤ 3239072845963^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132135763 10000000000 3239072845963 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238678047/10000000000 : ℝ)^4201 ≤ (42532625331099/100000000000000 : ℝ)^3177 := by
    have hnat : (5238678047 : ℕ)^4201*100000000000000^3177 ≤ 42532625331099^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238678047 10000000000 42532625331099 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542193831/1000000000 : ℝ)^4201 ≤ (8902216654491/20000000000000 : ℝ)^3177 := by
    have hnat : (542193831 : ℕ)^4201*20000000000000^3177 ≤ 8902216654491^3177*1000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542193831 1000000000 8902216654491 20000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2132135763/10000000000 : ℝ), (5238678047/10000000000 : ℝ), (542193831/1000000000 : ℝ)] ![(3239072845963/25000000000000 : ℝ), (42532625331099/100000000000000 : ℝ), (8902216654491/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2132135763/10000000000 : ℝ)|^4201 ≤ (3239072845963/25000000000000 : ℝ)^3177
        have hw : |(-2132135763/10000000000 : ℝ)|=(2132135763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238678047/10000000000 : ℝ)|^4201 ≤ (42532625331099/100000000000000 : ℝ)^3177
        have hw : |(5238678047/10000000000 : ℝ)|=(5238678047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542193831/1000000000 : ℝ)|^4201 ≤ (8902216654491/20000000000000 : ℝ)^3177
        have hw : |(542193831/1000000000 : ℝ)|=(542193831/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s3_5 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652614329/5000000000 : ℝ)*x 0 + (-1021211531/5000000000 : ℝ)*x 1 + (5421937991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652614329/5000000000 : ℝ)^4201 ≤ (864971209707/2000000000000 : ℝ)^3177 := by
    have hnat : (2652614329 : ℕ)^4201*2000000000000^3177 ≤ 864971209707^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652614329 5000000000 864971209707 2000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1021211531/5000000000 : ℝ)^4201 ≤ (12240359686737/100000000000000 : ℝ)^3177 := by
    have hnat : (1021211531 : ℕ)^4201*100000000000000^3177 ≤ 12240359686737^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021211531 5000000000 12240359686737 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421937991/10000000000 : ℝ)^4201 ≤ (44511079809557/100000000000000 : ℝ)^3177 := by
    have hnat : (5421937991 : ℕ)^4201*100000000000000^3177 ≤ 44511079809557^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421937991 10000000000 44511079809557 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652614329/5000000000 : ℝ), (-1021211531/5000000000 : ℝ), (5421937991/10000000000 : ℝ)] ![(864971209707/2000000000000 : ℝ), (12240359686737/100000000000000 : ℝ), (44511079809557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652614329/5000000000 : ℝ)|^4201 ≤ (864971209707/2000000000000 : ℝ)^3177
        have hw : |(2652614329/5000000000 : ℝ)|=(2652614329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1021211531/5000000000 : ℝ)|^4201 ≤ (12240359686737/100000000000000 : ℝ)^3177
        have hw : |(-1021211531/5000000000 : ℝ)|=(1021211531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421937991/10000000000 : ℝ)|^4201 ≤ (44511079809557/100000000000000 : ℝ)^3177
        have hw : |(5421937991/10000000000 : ℝ)|=(5421937991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s3_6 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305228527/10000000000 : ℝ)*x 0 + (5421937981/10000000000 : ℝ)*x 1 + (-1021211627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305228527/10000000000 : ℝ)^4201 ≤ (43248559073221/100000000000000 : ℝ)^3177 := by
    have hnat : (5305228527 : ℕ)^4201*100000000000000^3177 ≤ 43248559073221^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305228527 10000000000 43248559073221 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421937981/10000000000 : ℝ)^4201 ≤ (22255539850501/50000000000000 : ℝ)^3177 := by
    have hnat : (5421937981 : ℕ)^4201*50000000000000^3177 ≤ 22255539850501^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421937981 10000000000 22255539850501 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021211627/5000000000 : ℝ)^4201 ≤ (12240361208283/100000000000000 : ℝ)^3177 := by
    have hnat : (1021211627 : ℕ)^4201*100000000000000^3177 ≤ 12240361208283^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021211627 5000000000 12240361208283 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305228527/10000000000 : ℝ), (5421937981/10000000000 : ℝ), (-1021211627/5000000000 : ℝ)] ![(43248559073221/100000000000000 : ℝ), (22255539850501/50000000000000 : ℝ), (12240361208283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305228527/10000000000 : ℝ)|^4201 ≤ (43248559073221/100000000000000 : ℝ)^3177
        have hw : |(5305228527/10000000000 : ℝ)|=(5305228527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421937981/10000000000 : ℝ)|^4201 ≤ (22255539850501/50000000000000 : ℝ)^3177
        have hw : |(5421937981/10000000000 : ℝ)|=(5421937981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1021211627/5000000000 : ℝ)|^4201 ≤ (12240361208283/100000000000000 : ℝ)^3177
        have hw : |(-1021211627/5000000000 : ℝ)|=(1021211627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s3_7 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2176742023/5000000000 : ℝ)*x 0 + (4542042311/10000000000 : ℝ)*x 1 + (1043163621/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176742023/5000000000 : ℝ)^4201 ≤ (33298762576777/100000000000000 : ℝ)^3177 := by
    have hnat : (2176742023 : ℕ)^4201*100000000000000^3177 ≤ 33298762576777^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176742023 5000000000 33298762576777 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4542042311/10000000000 : ℝ)^4201 ≤ (35219040691161/100000000000000 : ℝ)^3177 := by
    have hnat : (4542042311 : ℕ)^4201*100000000000000^3177 ≤ 35219040691161^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542042311 10000000000 35219040691161 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043163621/2500000000 : ℝ)^4201 ≤ (15741098364409/50000000000000 : ℝ)^3177 := by
    have hnat : (1043163621 : ℕ)^4201*50000000000000^3177 ≤ 15741098364409^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043163621 2500000000 15741098364409 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176742023/5000000000 : ℝ), (4542042311/10000000000 : ℝ), (1043163621/2500000000 : ℝ)] ![(33298762576777/100000000000000 : ℝ), (35219040691161/100000000000000 : ℝ), (15741098364409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176742023/5000000000 : ℝ)|^4201 ≤ (33298762576777/100000000000000 : ℝ)^3177
        have hw : |(2176742023/5000000000 : ℝ)|=(2176742023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4542042311/10000000000 : ℝ)|^4201 ≤ (35219040691161/100000000000000 : ℝ)^3177
        have hw : |(4542042311/10000000000 : ℝ)|=(4542042311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043163621/2500000000 : ℝ)|^4201 ≤ (15741098364409/50000000000000 : ℝ)^3177
        have hw : |(1043163621/2500000000 : ℝ)|=(1043163621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1209_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16311/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1353/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3683/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16311/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9363/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16311/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9363/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16311/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9363/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16311/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9363/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16311/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9363/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16311/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9363/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9363/100000 : ℝ) ^ (8401/2048 : ℝ) ≤ (3017603657390939/50000000000000000000 : ℝ) := by
    have hpowers : (9363/100000 : ℝ)^8401 ≤ (3017603657390939/50000000000000000000 : ℝ)^2048 := by
      have hnat : (9363 : ℕ)^8401*50000000000000000000^2048 ≤ 3017603657390939^2048*100000^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9363 100000 3017603657390939 50000000000000000000 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9363/100000 : ℝ)) (X := (3017603657390939/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16311/100000 : ℝ) ^ (8401/2048 : ℝ) ≤ (58824111967484869/100000000000000000000 : ℝ) := by
    have hpowers : (16311/100000 : ℝ)^8401 ≤ (58824111967484869/100000000000000000000 : ℝ)^2048 := by
      have hnat : (16311 : ℕ)^8401*100000000000000000000^2048 ≤ 58824111967484869^2048*100000^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16311 100000 58824111967484869 100000000000000000000 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16311/100000 : ℝ)) (X := (58824111967484869/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003017603657390939/25000000000000000000 : ℝ) ≤ (10000294239745569/10000000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (25003017603657390939/25000000000000000000 : ℝ)^2048 ≤ (10000294239745569/10000000000000000 : ℝ)^8401 := by
      have hnat : (25003017603657390939 : ℕ)^2048*10000000000000000^8401 ≤ 10000294239745569^8401*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003017603657390939 25000000000000000000 10000294239745569 10000000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000294239745569/10000000000000000 : ℝ)) (X := (25003017603657390939/25000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100064859319282266747/100000000000000000000 : ℝ) ≤ (10001580756131889/10000000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (100064859319282266747/100000000000000000000 : ℝ)^2048 ≤ (10001580756131889/10000000000000000 : ℝ)^8401 := by
      have hnat : (100064859319282266747 : ℕ)^2048*10000000000000000^8401 ≤ 10001580756131889^8401*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100064859319282266747 100000000000000000000 10001580756131889 10000000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001580756131889/10000000000000000 : ℝ)) (X := (100064859319282266747/100000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50058824111967484869/50000000000000000000 : ℝ) ≤ (10002867272518209/10000000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (50058824111967484869/50000000000000000000 : ℝ)^2048 ≤ (10002867272518209/10000000000000000 : ℝ)^8401 := by
      have hnat : (50058824111967484869 : ℕ)^2048*10000000000000000^8401 ≤ 10002867272518209^8401*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50058824111967484869 50000000000000000000 10002867272518209 10000000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002867272518209/10000000000000000 : ℝ)) (X := (50058824111967484869/50000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3017603657390939/50000000000000000000 : ℝ) ≤ ((1929387585330610697/1930000000000000000 : ℝ)+2*(5360484943/2895000000000 : ℝ)*(9363/100000 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (1929387585330610697/1930000000000000000 : ℝ)+2*(5360484943/2895000000000 : ℝ)*(9363/100000 : ℝ)=(10000294239745569/10000000000000000 : ℝ) by norm_num, show 1+2*(3017603657390939/50000000000000000000 : ℝ)=(25003017603657390939/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(58824111967484869/100000000000000000000 : ℝ)+(3017603657390939/50000000000000000000 : ℝ) ≤ ((1929387585330610697/1930000000000000000 : ℝ)+(5360484943/2895000000000 : ℝ)*((16311/100000 : ℝ)+(9363/100000 : ℝ)))^(8401/2048 : ℝ) := by
    rw [show (1929387585330610697/1930000000000000000 : ℝ)+(5360484943/2895000000000 : ℝ)*((16311/100000 : ℝ)+(9363/100000 : ℝ))=(10001580756131889/10000000000000000 : ℝ) by norm_num, show 1+(58824111967484869/100000000000000000000 : ℝ)+(3017603657390939/50000000000000000000 : ℝ)=(100064859319282266747/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(58824111967484869/100000000000000000000 : ℝ) ≤ ((1929387585330610697/1930000000000000000 : ℝ)+2*(5360484943/2895000000000 : ℝ)*(16311/100000 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (1929387585330610697/1930000000000000000 : ℝ)+2*(5360484943/2895000000000 : ℝ)*(16311/100000 : ℝ)=(10002867272518209/10000000000000000 : ℝ) by norm_num, show 1+2*(58824111967484869/100000000000000000000 : ℝ)=(50058824111967484869/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1929387585330610697/1930000000000000000 : ℝ)*(X 1 0+X 2 0)+(5360484943/2895000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (9363/100000 : ℝ)) (hi := (16311/100000 : ℝ)) (c := (1929387585330610697/1930000000000000000 : ℝ)) (alpha := (5360484943/2895000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1929387585330610697/1930000000000000000 : ℝ)*(X 0 1+X 2 1)+(5360484943/2895000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (9363/100000 : ℝ)) (hi := (16311/100000 : ℝ)) (c := (1929387585330610697/1930000000000000000 : ℝ)) (alpha := (5360484943/2895000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1929387585330610697/1930000000000000000 : ℝ)*(X 0 2+X 1 2)+(5360484943/2895000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (9363/100000 : ℝ)) (hi := (16311/100000 : ℝ)) (c := (1929387585330610697/1930000000000000000 : ℝ)) (alpha := (5360484943/2895000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2132120513/10000000000 : ℝ)*X 0 0+(542262699/1000000000 : ℝ)*X 0 1+(5237993077/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338056871/2500000000 : ℝ)*X 1 0+(-222636807/1000000000 : ℝ)*X 1 1+(2618996621/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352227377/10000000000 : ℝ)*X 2 0+(5237993511/10000000000 : ℝ)*X 2 1+(-1113183929/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870690637/2000000000 : ℝ)*X 0 0+(2085633137/5000000000 : ℝ)*X 0 1+(2271711691/5000000000 : ℝ)*X 0 2+(870690637/2000000000 : ℝ)*X 1 0+(2085633137/5000000000 : ℝ)*X 1 1+(2271711691/5000000000 : ℝ)*X 1 2+(870690637/2000000000 : ℝ)*X 2 0+(2085633137/5000000000 : ℝ)*X 2 1+(2271711691/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2132135763/10000000000 : ℝ)*X 0 0+(5238678047/10000000000 : ℝ)*X 0 1+(542193831/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652614329/5000000000 : ℝ)*X 1 0+(-1021211531/5000000000 : ℝ)*X 1 1+(5421937991/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305228527/10000000000 : ℝ)*X 2 0+(5421937981/10000000000 : ℝ)*X 2 1+(-1021211627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2176742023/5000000000 : ℝ)*X 0 0+(4542042311/10000000000 : ℝ)*X 0 1+(1043163621/2500000000 : ℝ)*X 0 2+(2176742023/5000000000 : ℝ)*X 1 0+(4542042311/10000000000 : ℝ)*X 1 1+(1043163621/2500000000 : ℝ)*X 1 2+(2176742023/5000000000 : ℝ)*X 2 0+(4542042311/10000000000 : ℝ)*X 2 1+(1043163621/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1156085105985055077783454311/96500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2020047263/100000000000000 : ℝ)*(base19) + (1671060563/100000000000000 : ℝ)*(base23) + (64416069/50000000000000 : ℝ)*(lower2) + (87396659/50000000000000 : ℝ)*(upper3) + (209083883/100000000000000 : ℝ)*(upper5) + (4051646706415579/100000000000000 : ℝ)*(major0) + (4051646706415579/100000000000000 : ℝ)*(major1) + (4051646706415579/100000000000000 : ℝ)*(major2) + (1083233484587509/20000000000000 : ℝ)*(sp0) + (1083242610828859/20000000000000 : ℝ)*(sp1) + (1083242680626199/20000000000000 : ℝ)*(sp2) + (671764366045903/25000000000000 : ℝ)*(sp3) + (23825627007/50000000000000 : ℝ)*(sp4) + (2559389679/12500000000000 : ℝ)*(sp7) + (671769484825261/25000000000000 : ℝ)*(f.failure) + (2708107537095779/50000000000000 : ℝ)*(f.sum) + (825670260313/579000000000000000000000000 : ℝ)*base65 + (6194141640763454311/579000000000000000000000000000000 : ℝ)*base68 + (1064667916345545689/579000000000000000000000000000000 : ℝ)*base69 + (968875442059454311/579000000000000000000000000000000 : ℝ)*base72 + (1075332545911/289500000000000000000000000 : ℝ)*base74 + (2488080309130545689/579000000000000000000000000000000 : ℝ)*base75 + (2994121129975545689/579000000000000000000000000000000 : ℝ)*base77 + (1258049685013545689/579000000000000000000000000000000 : ℝ)*base79 + (16800452381/57900000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (14540647/2500000000000000000000 : ℝ)*base89 + (14540647/2500000000000000000000 : ℝ)*base91 + (14540647/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (415900910801362642639/96500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1023194281/100000000000000 : ℝ)*(base19) + (514741861/50000000000000 : ℝ)*(base23) + (53884631/50000000000000 : ℝ)*(lower4) + (42348687/25000000000000 : ℝ)*(upper5) + (2040976975572407/50000000000000 : ℝ)*(major0) + (2040976975572407/50000000000000 : ℝ)*(major1) + (2040976975572407/50000000000000 : ℝ)*(major2) + (717252993/20000000000000 : ℝ)*(sp0) + (9794317043/50000000000000 : ℝ)*(sp1) + (786121081/6250000000000 : ℝ)*(sp2) + (5456726275041297/100000000000000 : ℝ)*(sp4) + (2728354624738947/50000000000000 : ℝ)*(sp5) + (5456716253885243/100000000000000 : ℝ)*(sp6) + (1353588948660781/50000000000000 : ℝ)*(sp7) + (1353588948660781/50000000000000 : ℝ)*(f.failure) + (5456729861306261/100000000000000 : ℝ)*(f.sum) + (146859985769/144750000000000000000000000 : ℝ)*base66 + (957266911614213037/289500000000000000000000000000000 : ℝ)*base67 + (2088764454419786963/289500000000000000000000000000000 : ℝ)*base70 + (116505748702713037/289500000000000000000000000000000 : ℝ)*base71 + (779075506511/289500000000000000000000000 : ℝ)*base73 + (1763969306614286963/289500000000000000000000000000000 : ℝ)*base76 + (952841759738786963/289500000000000000000000000000000 : ℝ)*base78 + (1843921940079213037/289500000000000000000000000000000 : ℝ)*base79 + (392035144643/289500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (8948313/5000000000000000000000 : ℝ)*base90 + (8948313/5000000000000000000000 : ℝ)*base92 + (8948313/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1209_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16311/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1353/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1209_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1209_s4_0 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2134629027/10000000000 : ℝ)*x 0 + (1349715719/2500000000 : ℝ)*x 1 + (5260114051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134629027/10000000000 : ℝ)^4201 ≤ (6488164623363/50000000000000 : ℝ)^3177 := by
    have hnat : (2134629027 : ℕ)^4201*50000000000000^3177 ≤ 6488164623363^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134629027 10000000000 6488164623363 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349715719/2500000000 : ℝ)^4201 ≤ (11065190079857/25000000000000 : ℝ)^3177 := by
    have hnat : (1349715719 : ℕ)^4201*25000000000000^3177 ≤ 11065190079857^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349715719 2500000000 11065190079857 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260114051/10000000000 : ℝ)^4201 ≤ (4276291041577/10000000000000 : ℝ)^3177 := by
    have hnat : (5260114051 : ℕ)^4201*10000000000000^3177 ≤ 4276291041577^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260114051 10000000000 4276291041577 10000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2134629027/10000000000 : ℝ), (1349715719/2500000000 : ℝ), (5260114051/10000000000 : ℝ)] ![(6488164623363/50000000000000 : ℝ), (11065190079857/25000000000000 : ℝ), (4276291041577/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2134629027/10000000000 : ℝ)|^4201 ≤ (6488164623363/50000000000000 : ℝ)^3177
        have hw : |(-2134629027/10000000000 : ℝ)|=(2134629027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349715719/2500000000 : ℝ)|^4201 ≤ (11065190079857/25000000000000 : ℝ)^3177
        have hw : |(1349715719/2500000000 : ℝ)|=(1349715719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260114051/10000000000 : ℝ)|^4201 ≤ (4276291041577/10000000000000 : ℝ)^3177
        have hw : |(5260114051/10000000000 : ℝ)|=(5260114051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s4_1 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673127213/5000000000 : ℝ)*x 0 + (-275636719/1250000000 : ℝ)*x 1 + (82189281/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673127213/5000000000 : ℝ)^4201 ≤ (43691352415939/100000000000000 : ℝ)^3177 := by
    have hnat : (2673127213 : ℕ)^4201*100000000000000^3177 ≤ 43691352415939^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673127213 5000000000 43691352415939 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275636719/1250000000 : ℝ)^4201 ≤ (13545737872047/100000000000000 : ℝ)^3177 := by
    have hnat : (275636719 : ℕ)^4201*100000000000000^3177 ≤ 13545737872047^3177*1250000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275636719 1250000000 13545737872047 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82189281/156250000 : ℝ)^4201 ≤ (21381454847761/50000000000000 : ℝ)^3177 := by
    have hnat : (82189281 : ℕ)^4201*50000000000000^3177 ≤ 21381454847761^3177*156250000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82189281 156250000 21381454847761 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673127213/5000000000 : ℝ), (-275636719/1250000000 : ℝ), (82189281/156250000 : ℝ)] ![(43691352415939/100000000000000 : ℝ), (13545737872047/100000000000000 : ℝ), (21381454847761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673127213/5000000000 : ℝ)|^4201 ≤ (43691352415939/100000000000000 : ℝ)^3177
        have hw : |(2673127213/5000000000 : ℝ)|=(2673127213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-275636719/1250000000 : ℝ)|^4201 ≤ (13545737872047/100000000000000 : ℝ)^3177
        have hw : |(-275636719/1250000000 : ℝ)|=(275636719/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82189281/156250000 : ℝ)|^4201 ≤ (21381454847761/50000000000000 : ℝ)^3177
        have hw : |(82189281/156250000 : ℝ)|=(82189281/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s4_2 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346254131/10000000000 : ℝ)*x 0 + (328757111/625000000 : ℝ)*x 1 + (-2205094421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346254131/10000000000 : ℝ)^4201 ≤ (43691349228049/100000000000000 : ℝ)^3177 := by
    have hnat : (5346254131 : ℕ)^4201*100000000000000^3177 ≤ 43691349228049^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346254131 10000000000 43691349228049 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328757111/625000000 : ℝ)^4201 ≤ (21381453729763/50000000000000 : ℝ)^3177 := by
    have hnat : (328757111 : ℕ)^4201*50000000000000^3177 ≤ 21381453729763^3177*625000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328757111 625000000 21381453729763 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205094421/10000000000 : ℝ)^4201 ≤ (13545743306267/100000000000000 : ℝ)^3177 := by
    have hnat : (2205094421 : ℕ)^4201*100000000000000^3177 ≤ 13545743306267^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205094421 10000000000 13545743306267 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346254131/10000000000 : ℝ), (328757111/625000000 : ℝ), (-2205094421/10000000000 : ℝ)] ![(43691349228049/100000000000000 : ℝ), (21381453729763/50000000000000 : ℝ), (13545743306267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346254131/10000000000 : ℝ)|^4201 ≤ (43691349228049/100000000000000 : ℝ)^3177
        have hw : |(5346254131/10000000000 : ℝ)|=(5346254131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328757111/625000000 : ℝ)|^4201 ≤ (21381453729763/50000000000000 : ℝ)^3177
        have hw : |(328757111/625000000 : ℝ)|=(328757111/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2205094421/10000000000 : ℝ)|^4201 ≤ (13545743306267/100000000000000 : ℝ)^3177
        have hw : |(-2205094421/10000000000 : ℝ)|=(2205094421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s4_3 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4354952819/10000000000 : ℝ)*x 0 + (1054329471/2500000000 : ℝ)*x 1 + (449698759/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354952819/10000000000 : ℝ)^4201 ≤ (33313618679563/100000000000000 : ℝ)^3177 := by
    have hnat : (4354952819 : ℕ)^4201*100000000000000^3177 ≤ 33313618679563^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354952819 10000000000 33313618679563 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054329471/2500000000 : ℝ)^4201 ≤ (31928558064823/100000000000000 : ℝ)^3177 := by
    have hnat : (1054329471 : ℕ)^4201*100000000000000^3177 ≤ 31928558064823^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054329471 2500000000 31928558064823 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449698759/1000000000 : ℝ)^4201 ≤ (34757823239899/100000000000000 : ℝ)^3177 := by
    have hnat : (449698759 : ℕ)^4201*100000000000000^3177 ≤ 34757823239899^3177*1000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449698759 1000000000 34757823239899 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354952819/10000000000 : ℝ), (1054329471/2500000000 : ℝ), (449698759/1000000000 : ℝ)] ![(33313618679563/100000000000000 : ℝ), (31928558064823/100000000000000 : ℝ), (34757823239899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354952819/10000000000 : ℝ)|^4201 ≤ (33313618679563/100000000000000 : ℝ)^3177
        have hw : |(4354952819/10000000000 : ℝ)|=(4354952819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054329471/2500000000 : ℝ)|^4201 ≤ (31928558064823/100000000000000 : ℝ)^3177
        have hw : |(1054329471/2500000000 : ℝ)|=(1054329471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449698759/1000000000 : ℝ)|^4201 ≤ (34757823239899/100000000000000 : ℝ)^3177
        have hw : |(449698759/1000000000 : ℝ)|=(449698759/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s4_4 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-533658753/2500000000 : ℝ)*x 0 + (2630250687/5000000000 : ℝ)*x 1 + (5398474343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533658753/2500000000 : ℝ)^4201 ≤ (12976377356051/100000000000000 : ℝ)^3177 := by
    have hnat : (533658753 : ℕ)^4201*100000000000000^3177 ≤ 12976377356051^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533658753 2500000000 12976377356051 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630250687/5000000000 : ℝ)^4201 ≤ (10691768544693/25000000000000 : ℝ)^3177 := by
    have hnat : (2630250687 : ℕ)^4201*25000000000000^3177 ≤ 10691768544693^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630250687 5000000000 10691768544693 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398474343/10000000000 : ℝ)^4201 ≤ (691508569529/1562500000000 : ℝ)^3177 := by
    have hnat : (5398474343 : ℕ)^4201*1562500000000^3177 ≤ 691508569529^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398474343 10000000000 691508569529 1562500000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-533658753/2500000000 : ℝ), (2630250687/5000000000 : ℝ), (5398474343/10000000000 : ℝ)] ![(12976377356051/100000000000000 : ℝ), (10691768544693/25000000000000 : ℝ), (691508569529/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-533658753/2500000000 : ℝ)|^4201 ≤ (12976377356051/100000000000000 : ℝ)^3177
        have hw : |(-533658753/2500000000 : ℝ)|=(533658753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630250687/5000000000 : ℝ)|^4201 ≤ (10691768544693/25000000000000 : ℝ)^3177
        have hw : |(2630250687/5000000000 : ℝ)|=(2630250687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398474343/10000000000 : ℝ)|^4201 ≤ (691508569529/1562500000000 : ℝ)^3177
        have hw : |(5398474343/10000000000 : ℝ)|=(5398474343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s4_5 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5310933321/10000000000 : ℝ)*x 0 + (-103336727/500000000 : ℝ)*x 1 + (1349618503/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310933321/10000000000 : ℝ)^4201 ≤ (43310065176957/100000000000000 : ℝ)^3177 := by
    have hnat : (5310933321 : ℕ)^4201*100000000000000^3177 ≤ 43310065176957^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310933321 10000000000 43310065176957 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103336727/500000000 : ℝ)^4201 ≤ (12433389944717/100000000000000 : ℝ)^3177 := by
    have hnat : (103336727 : ℕ)^4201*100000000000000^3177 ≤ 12433389944717^3177*500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103336727 500000000 12433389944717 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349618503/2500000000 : ℝ)^4201 ≤ (44256544861711/100000000000000 : ℝ)^3177 := by
    have hnat : (1349618503 : ℕ)^4201*100000000000000^3177 ≤ 44256544861711^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349618503 2500000000 44256544861711 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310933321/10000000000 : ℝ), (-103336727/500000000 : ℝ), (1349618503/2500000000 : ℝ)] ![(43310065176957/100000000000000 : ℝ), (12433389944717/100000000000000 : ℝ), (44256544861711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310933321/10000000000 : ℝ)|^4201 ≤ (43310065176957/100000000000000 : ℝ)^3177
        have hw : |(5310933321/10000000000 : ℝ)|=(5310933321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103336727/500000000 : ℝ)|^4201 ≤ (12433389944717/100000000000000 : ℝ)^3177
        have hw : |(-103336727/500000000 : ℝ)|=(103336727/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349618503/2500000000 : ℝ)|^4201 ≤ (44256544861711/100000000000000 : ℝ)^3177
        have hw : |(1349618503/2500000000 : ℝ)|=(1349618503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s4_6 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062186771/2000000000 : ℝ)*x 0 + (5398473747/10000000000 : ℝ)*x 1 + (-1033367089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062186771/2000000000 : ℝ)^4201 ≤ (43310070935263/100000000000000 : ℝ)^3177 := by
    have hnat : (1062186771 : ℕ)^4201*100000000000000^3177 ≤ 43310070935263^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062186771 2000000000 43310070935263 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398473747/10000000000 : ℝ)^4201 ≤ (44256541989027/100000000000000 : ℝ)^3177 := by
    have hnat : (5398473747 : ℕ)^4201*100000000000000^3177 ≤ 44256541989027^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398473747 10000000000 44256541989027 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1033367089/5000000000 : ℝ)^4201 ≤ (6216693532503/50000000000000 : ℝ)^3177 := by
    have hnat : (1033367089 : ℕ)^4201*50000000000000^3177 ≤ 6216693532503^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033367089 5000000000 6216693532503 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062186771/2000000000 : ℝ), (5398473747/10000000000 : ℝ), (-1033367089/5000000000 : ℝ)] ![(43310070935263/100000000000000 : ℝ), (44256541989027/100000000000000 : ℝ), (6216693532503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062186771/2000000000 : ℝ)|^4201 ≤ (43310070935263/100000000000000 : ℝ)^3177
        have hw : |(1062186771/2000000000 : ℝ)|=(1062186771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398473747/10000000000 : ℝ)|^4201 ≤ (44256541989027/100000000000000 : ℝ)^3177
        have hw : |(5398473747/10000000000 : ℝ)|=(5398473747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1033367089/5000000000 : ℝ)|^4201 ≤ (6216693532503/50000000000000 : ℝ)^3177
        have hw : |(-1033367089/5000000000 : ℝ)|=(1033367089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s4_7 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1088741753/2500000000 : ℝ)*x 0 + (4496206121/10000000000 : ℝ)*x 1 + (1054525327/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088741753/2500000000 : ℝ)^4201 ≤ (4164220280557/12500000000000 : ℝ)^3177 := by
    have hnat : (1088741753 : ℕ)^4201*12500000000000^3177 ≤ 4164220280557^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088741753 2500000000 4164220280557 12500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496206121/10000000000 : ℝ)^4201 ≤ (34749836566237/100000000000000 : ℝ)^3177 := by
    have hnat : (4496206121 : ℕ)^4201*100000000000000^3177 ≤ 34749836566237^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496206121 10000000000 34749836566237 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054525327/2500000000 : ℝ)^4201 ≤ (31936401174851/100000000000000 : ℝ)^3177 := by
    have hnat : (1054525327 : ℕ)^4201*100000000000000^3177 ≤ 31936401174851^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054525327 2500000000 31936401174851 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088741753/2500000000 : ℝ), (4496206121/10000000000 : ℝ), (1054525327/2500000000 : ℝ)] ![(4164220280557/12500000000000 : ℝ), (34749836566237/100000000000000 : ℝ), (31936401174851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088741753/2500000000 : ℝ)|^4201 ≤ (4164220280557/12500000000000 : ℝ)^3177
        have hw : |(1088741753/2500000000 : ℝ)|=(1088741753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496206121/10000000000 : ℝ)|^4201 ≤ (34749836566237/100000000000000 : ℝ)^3177
        have hw : |(4496206121/10000000000 : ℝ)|=(4496206121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054525327/2500000000 : ℝ)|^4201 ≤ (31936401174851/100000000000000 : ℝ)^3177
        have hw : |(1054525327/2500000000 : ℝ)|=(1054525327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1209_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1353/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (353/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3683/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1353/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3683/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1353/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3683/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1353/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3683/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1353/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3683/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1353/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3683/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1353/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1353/12500 : ℝ) ^ (8401/2048 : ℝ) ≤ (10939806824787307/100000000000000000000 : ℝ) := by
    have hpowers : (1353/12500 : ℝ)^8401 ≤ (10939806824787307/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1353 : ℕ)^8401*100000000000000000000^2048 ≤ 10939806824787307^2048*12500^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1353 12500 10939806824787307 100000000000000000000 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1353/12500 : ℝ)) (X := (10939806824787307/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3683/25000 : ℝ) ^ (8401/2048 : ℝ) ≤ (9685171315955401/25000000000000000000 : ℝ) := by
    have hpowers : (3683/25000 : ℝ)^8401 ≤ (9685171315955401/25000000000000000000 : ℝ)^2048 := by
      have hnat : (3683 : ℕ)^8401*25000000000000000000^2048 ≤ 9685171315955401^2048*25000^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3683 25000 9685171315955401 25000000000000000000 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3683/25000 : ℝ)) (X := (9685171315955401/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010939806824787307/50000000000000000000 : ℝ) ≤ (100005333382001/100000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (50010939806824787307/50000000000000000000 : ℝ)^2048 ≤ (100005333382001/100000000000000 : ℝ)^8401 := by
      have hnat : (50010939806824787307 : ℕ)^2048*100000000000000^8401 ≤ 100005333382001^8401*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010939806824787307 50000000000000000000 100005333382001 100000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100005333382001/100000000000000 : ℝ)) (X := (50010939806824787307/50000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049680492088608911/100000000000000000000 : ℝ) ≤ (5000605443047027/5000000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (100049680492088608911/100000000000000000000 : ℝ)^2048 ≤ (5000605443047027/5000000000000000 : ℝ)^8401 := by
      have hnat : (100049680492088608911 : ℕ)^2048*5000000000000000^8401 ≤ 5000605443047027^8401*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049680492088608911 100000000000000000000 5000605443047027 5000000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000605443047027/5000000000000000 : ℝ)) (X := (100049680492088608911/100000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509685171315955401/12500000000000000000 : ℝ) ≤ (1250236054248501/1250000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (12509685171315955401/12500000000000000000 : ℝ)^2048 ≤ (1250236054248501/1250000000000000 : ℝ)^8401 := by
      have hnat : (12509685171315955401 : ℕ)^2048*1250000000000000^8401 ≤ 1250236054248501^8401*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509685171315955401 12500000000000000000 1250236054248501 1250000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250236054248501/1250000000000000 : ℝ)) (X := (12509685171315955401/12500000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10939806824787307/100000000000000000000 : ℝ) ≤ ((2441713545554854663/2442500000000000000 : ℝ)+2*(338773946977/195400000000000 : ℝ)*(1353/12500 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (2441713545554854663/2442500000000000000 : ℝ)+2*(338773946977/195400000000000 : ℝ)*(1353/12500 : ℝ)=(100005333382001/100000000000000 : ℝ) by norm_num, show 1+2*(10939806824787307/100000000000000000000 : ℝ)=(50010939806824787307/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9685171315955401/25000000000000000000 : ℝ)+(10939806824787307/100000000000000000000 : ℝ) ≤ ((2441713545554854663/2442500000000000000 : ℝ)+(338773946977/195400000000000 : ℝ)*((3683/25000 : ℝ)+(1353/12500 : ℝ)))^(8401/2048 : ℝ) := by
    rw [show (2441713545554854663/2442500000000000000 : ℝ)+(338773946977/195400000000000 : ℝ)*((3683/25000 : ℝ)+(1353/12500 : ℝ))=(5000605443047027/5000000000000000 : ℝ) by norm_num, show 1+(9685171315955401/25000000000000000000 : ℝ)+(10939806824787307/100000000000000000000 : ℝ)=(100049680492088608911/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9685171315955401/25000000000000000000 : ℝ) ≤ ((2441713545554854663/2442500000000000000 : ℝ)+2*(338773946977/195400000000000 : ℝ)*(3683/25000 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (2441713545554854663/2442500000000000000 : ℝ)+2*(338773946977/195400000000000 : ℝ)*(3683/25000 : ℝ)=(1250236054248501/1250000000000000 : ℝ) by norm_num, show 1+2*(9685171315955401/25000000000000000000 : ℝ)=(12509685171315955401/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2441713545554854663/2442500000000000000 : ℝ)*(X 1 0+X 2 0)+(338773946977/195400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (1353/12500 : ℝ)) (hi := (3683/25000 : ℝ)) (c := (2441713545554854663/2442500000000000000 : ℝ)) (alpha := (338773946977/195400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2441713545554854663/2442500000000000000 : ℝ)*(X 0 1+X 2 1)+(338773946977/195400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (1353/12500 : ℝ)) (hi := (3683/25000 : ℝ)) (c := (2441713545554854663/2442500000000000000 : ℝ)) (alpha := (338773946977/195400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2441713545554854663/2442500000000000000 : ℝ)*(X 0 2+X 1 2)+(338773946977/195400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (1353/12500 : ℝ)) (hi := (3683/25000 : ℝ)) (c := (2441713545554854663/2442500000000000000 : ℝ)) (alpha := (338773946977/195400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2134629027/10000000000 : ℝ)*X 0 0+(1349715719/2500000000 : ℝ)*X 0 1+(5260114051/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673127213/5000000000 : ℝ)*X 1 0+(-275636719/1250000000 : ℝ)*X 1 1+(82189281/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346254131/10000000000 : ℝ)*X 2 0+(328757111/625000000 : ℝ)*X 2 1+(-2205094421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4354952819/10000000000 : ℝ)*X 0 0+(1054329471/2500000000 : ℝ)*X 0 1+(449698759/1000000000 : ℝ)*X 0 2+(4354952819/10000000000 : ℝ)*X 1 0+(1054329471/2500000000 : ℝ)*X 1 1+(449698759/1000000000 : ℝ)*X 1 2+(4354952819/10000000000 : ℝ)*X 2 0+(1054329471/2500000000 : ℝ)*X 2 1+(449698759/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-533658753/2500000000 : ℝ)*X 0 0+(2630250687/5000000000 : ℝ)*X 0 1+(5398474343/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310933321/10000000000 : ℝ)*X 1 0+(-103336727/500000000 : ℝ)*X 1 1+(1349618503/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062186771/2000000000 : ℝ)*X 2 0+(5398473747/10000000000 : ℝ)*X 2 1+(-1033367089/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1088741753/2500000000 : ℝ)*X 0 0+(4496206121/10000000000 : ℝ)*X 0 1+(1054525327/2500000000 : ℝ)*X 0 2+(1088741753/2500000000 : ℝ)*X 1 0+(4496206121/10000000000 : ℝ)*X 1 1+(1054525327/2500000000 : ℝ)*X 1 2+(1088741753/2500000000 : ℝ)*X 2 0+(4496206121/10000000000 : ℝ)*X 2 1+(1054525327/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (540013953158995137062686821/61062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (429479671/20000000000000 : ℝ)*(base19) + (2496617299/100000000000000 : ℝ)*(base23) + (210461937/50000000000000 : ℝ)*(upper2) + (66215579/20000000000000 : ℝ)*(upper3) + (5391551501247461/100000000000000 : ℝ)*(major0) + (5391551501247461/100000000000000 : ℝ)*(major1) + (5391551501247461/100000000000000 : ℝ)*(major2) + (7207345216011349/100000000000000 : ℝ)*(sp0) + (7207389214433947/100000000000000 : ℝ)*(sp1) + (7207382748453367/100000000000000 : ℝ)*(sp2) + (178783931663757/5000000000000 : ℝ)*(sp3) + (46145820953/100000000000000 : ℝ)*(sp4) + (1529190409/25000000000000 : ℝ)*(sp6) + (4089074989/12500000000000 : ℝ)*(sp7) + (893927836468763/25000000000000 : ℝ)*(f.failure) + (3603695680916151/50000000000000 : ℝ)*(f.sum) + (61791436836747/9770000000000000000000000000 : ℝ)*base65 + (409767929978723143/244250000000000000000000000000000 : ℝ)*base67 + (2117432788245723143/244250000000000000000000000000000 : ℝ)*base69 + (1027786882355276857/244250000000000000000000000000000 : ℝ)*base72 + (45565643368037/9770000000000000000000000000 : ℝ)*base73 + (1930253957473223143/244250000000000000000000000000000 : ℝ)*base75 + (1280669588395973143/244250000000000000000000000000000 : ℝ)*base77 + (1257856507722223143/244250000000000000000000000000000 : ℝ)*base79 + (85173508525027/9770000000000000000000000000 : ℝ)*base81 + (36419599/2500000000000000000000 : ℝ)*base90 + (36419599/2500000000000000000000 : ℝ)*base92 + (36419599/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (426830851214568974625591939/61062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78233619/12500000000000 : ℝ)*(base19) + (354693319/20000000000000 : ℝ)*(base23) + (92082801/100000000000000 : ℝ)*(lower2) + (48092643/100000000000000 : ℝ)*(upper3) + (118362667/50000000000000 : ℝ)*(lower4) + (58949573/20000000000000 : ℝ)*(upper5) + (2710894269031551/50000000000000 : ℝ)*(major0) + (2710894269031551/50000000000000 : ℝ)*(major1) + (2710894269031551/50000000000000 : ℝ)*(major2) + (5507166211/25000000000000 : ℝ)*(sp2) + (289912484062583/4000000000000 : ℝ)*(sp4) + (7247811475695623/100000000000000 : ℝ)*(sp5) + (7247788299433137/100000000000000 : ℝ)*(sp6) + (898941185389863/25000000000000 : ℝ)*(sp7) + (898941185389863/25000000000000 : ℝ)*(f.failure) + (289912484062583/4000000000000 : ℝ)*(f.sum) + (29163740333413/4885000000000000000000000000 : ℝ)*base66 + (456238848033690187/122125000000000000000000000000000 : ℝ)*base68 + (288732115350934813/122125000000000000000000000000000 : ℝ)*base69 + (1118988062878184813/122125000000000000000000000000000 : ℝ)*base71 + (26545330252393/4885000000000000000000000000 : ℝ)*base74 + (1188058371552440187/122125000000000000000000000000000 : ℝ)*base76 + (274100326188315187/122125000000000000000000000000000 : ℝ)*base78 + (889833796863815187/122125000000000000000000000000000 : ℝ)*base80 + (16810425235483/4885000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (12310101/2500000000000000000000 : ℝ)*base89 + (12310101/2500000000000000000000 : ℝ)*base91 + (12310101/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1209_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1353/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1209_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1209_s5_0 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1067565963/5000000000 : ℝ)*x 0 + (674151743/1250000000 : ℝ)*x 1 + (2632716351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067565963/5000000000 : ℝ)^4201 ≤ (12980371859763/100000000000000 : ℝ)^3177 := by
    have hnat : (1067565963 : ℕ)^4201*100000000000000^3177 ≤ 12980371859763^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067565963 5000000000 12980371859763 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674151743/1250000000 : ℝ)^4201 ≤ (11049883254059/25000000000000 : ℝ)^3177 := by
    have hnat : (674151743 : ℕ)^4201*25000000000000^3177 ≤ 11049883254059^3177*1250000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674151743 1250000000 11049883254059 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632716351/5000000000 : ℝ)^4201 ≤ (42820095109851/100000000000000 : ℝ)^3177 := by
    have hnat : (2632716351 : ℕ)^4201*100000000000000^3177 ≤ 42820095109851^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632716351 5000000000 42820095109851 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1067565963/5000000000 : ℝ), (674151743/1250000000 : ℝ), (2632716351/5000000000 : ℝ)] ![(12980371859763/100000000000000 : ℝ), (11049883254059/25000000000000 : ℝ), (42820095109851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1067565963/5000000000 : ℝ)|^4201 ≤ (12980371859763/100000000000000 : ℝ)^3177
        have hw : |(-1067565963/5000000000 : ℝ)|=(1067565963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674151743/1250000000 : ℝ)|^4201 ≤ (11049883254059/25000000000000 : ℝ)^3177
        have hw : |(674151743/1250000000 : ℝ)|=(674151743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632716351/5000000000 : ℝ)|^4201 ≤ (42820095109851/100000000000000 : ℝ)^3177
        have hw : |(2632716351/5000000000 : ℝ)|=(2632716351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s5_1 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344829137/10000000000 : ℝ)*x 0 + (-2199947853/10000000000 : ℝ)*x 1 + (5265432709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344829137/10000000000 : ℝ)^4201 ≤ (10918987706071/25000000000000 : ℝ)^3177 := by
    have hnat : (5344829137 : ℕ)^4201*25000000000000^3177 ≤ 10918987706071^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344829137 10000000000 10918987706071 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2199947853/10000000000 : ℝ)^4201 ≤ (6751976990317/50000000000000 : ℝ)^3177 := by
    have hnat : (2199947853 : ℕ)^4201*50000000000000^3177 ≤ 6751976990317^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199947853 10000000000 6751976990317 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265432709/10000000000 : ℝ)^4201 ≤ (342560761481/800000000000 : ℝ)^3177 := by
    have hnat : (5265432709 : ℕ)^4201*800000000000^3177 ≤ 342560761481^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265432709 10000000000 342560761481 800000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344829137/10000000000 : ℝ), (-2199947853/10000000000 : ℝ), (5265432709/10000000000 : ℝ)] ![(10918987706071/25000000000000 : ℝ), (6751976990317/50000000000000 : ℝ), (342560761481/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344829137/10000000000 : ℝ)|^4201 ≤ (10918987706071/25000000000000 : ℝ)^3177
        have hw : |(5344829137/10000000000 : ℝ)|=(5344829137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2199947853/10000000000 : ℝ)|^4201 ≤ (6751976990317/50000000000000 : ℝ)^3177
        have hw : |(-2199947853/10000000000 : ℝ)|=(2199947853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265432709/10000000000 : ℝ)|^4201 ≤ (342560761481/800000000000 : ℝ)^3177
        have hw : |(5265432709/10000000000 : ℝ)|=(5265432709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s5_2 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336207277/2500000000 : ℝ)*x 0 + (2632716383/5000000000 : ℝ)*x 1 + (-439989563/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336207277/2500000000 : ℝ)^4201 ≤ (1747038020437/4000000000000 : ℝ)^3177 := by
    have hnat : (1336207277 : ℕ)^4201*4000000000000^3177 ≤ 1747038020437^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336207277 2500000000 1747038020437 4000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632716383/5000000000 : ℝ)^4201 ≤ (42820095798073/100000000000000 : ℝ)^3177 := by
    have hnat : (2632716383 : ℕ)^4201*100000000000000^3177 ≤ 42820095798073^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632716383 5000000000 42820095798073 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (439989563/2000000000 : ℝ)^4201 ≤ (3375988418049/25000000000000 : ℝ)^3177 := by
    have hnat : (439989563 : ℕ)^4201*25000000000000^3177 ≤ 3375988418049^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439989563 2000000000 3375988418049 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336207277/2500000000 : ℝ), (2632716383/5000000000 : ℝ), (-439989563/2000000000 : ℝ)] ![(1747038020437/4000000000000 : ℝ), (42820095798073/100000000000000 : ℝ), (3375988418049/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336207277/2500000000 : ℝ)|^4201 ≤ (1747038020437/4000000000000 : ℝ)^3177
        have hw : |(1336207277/2500000000 : ℝ)|=(1336207277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632716383/5000000000 : ℝ)|^4201 ≤ (42820095798073/100000000000000 : ℝ)^3177
        have hw : |(2632716383/5000000000 : ℝ)|=(2632716383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-439989563/2000000000 : ℝ)|^4201 ≤ (3375988418049/25000000000000 : ℝ)^3177
        have hw : |(-439989563/2000000000 : ℝ)|=(439989563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s5_3 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1088812291/2500000000 : ℝ)*x 0 + (4228333289/10000000000 : ℝ)*x 1 + (4485895561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088812291/2500000000 : ℝ)^4201 ≤ (33316616296883/100000000000000 : ℝ)^3177 := by
    have hnat : (1088812291 : ℕ)^4201*100000000000000^3177 ≤ 33316616296883^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088812291 2500000000 33316616296883 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4228333289/10000000000 : ℝ)^4201 ≤ (6407775984619/20000000000000 : ℝ)^3177 := by
    have hnat : (4228333289 : ℕ)^4201*20000000000000^3177 ≤ 6407775984619^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228333289 10000000000 6407775984619 20000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4485895561/10000000000 : ℝ)^4201 ≤ (34644503758159/100000000000000 : ℝ)^3177 := by
    have hnat : (4485895561 : ℕ)^4201*100000000000000^3177 ≤ 34644503758159^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485895561 10000000000 34644503758159 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088812291/2500000000 : ℝ), (4228333289/10000000000 : ℝ), (4485895561/10000000000 : ℝ)] ![(33316616296883/100000000000000 : ℝ), (6407775984619/20000000000000 : ℝ), (34644503758159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088812291/2500000000 : ℝ)|^4201 ≤ (33316616296883/100000000000000 : ℝ)^3177
        have hw : |(1088812291/2500000000 : ℝ)|=(1088812291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4228333289/10000000000 : ℝ)|^4201 ≤ (6407775984619/20000000000000 : ℝ)^3177
        have hw : |(4228333289/10000000000 : ℝ)|=(4228333289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4485895561/10000000000 : ℝ)|^4201 ≤ (34644503758159/100000000000000 : ℝ)^3177
        have hw : |(4485895561/10000000000 : ℝ)|=(4485895561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s5_4 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2135136677/10000000000 : ℝ)*x 0 + (5265761799/10000000000 : ℝ)*x 1 + (107857677/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135136677/10000000000 : ℝ)^4201 ≤ (12980410052701/100000000000000 : ℝ)^3177 := by
    have hnat : (2135136677 : ℕ)^4201*100000000000000^3177 ≤ 12980410052701^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135136677 10000000000 12980410052701 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265761799/10000000000 : ℝ)^4201 ≤ (42823634083473/100000000000000 : ℝ)^3177 := by
    have hnat : (5265761799 : ℕ)^4201*100000000000000^3177 ≤ 42823634083473^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265761799 10000000000 42823634083473 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107857677/200000000 : ℝ)^4201 ≤ (8839191170457/20000000000000 : ℝ)^3177 := by
    have hnat : (107857677 : ℕ)^4201*20000000000000^3177 ≤ 8839191170457^3177*200000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107857677 200000000 8839191170457 20000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2135136677/10000000000 : ℝ), (5265761799/10000000000 : ℝ), (107857677/200000000 : ℝ)] ![(12980410052701/100000000000000 : ℝ), (42823634083473/100000000000000 : ℝ), (8839191170457/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2135136677/10000000000 : ℝ)|^4201 ≤ (12980410052701/100000000000000 : ℝ)^3177
        have hw : |(-2135136677/10000000000 : ℝ)|=(2135136677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265761799/10000000000 : ℝ)|^4201 ≤ (42823634083473/100000000000000 : ℝ)^3177
        have hw : |(5265761799/10000000000 : ℝ)|=(5265761799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107857677/200000000 : ℝ)|^4201 ≤ (8839191170457/20000000000000 : ℝ)^3177
        have hw : |(107857677/200000000 : ℝ)|=(107857677/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s5_5 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312299371/10000000000 : ℝ)*x 0 + (-207249669/1000000000 : ℝ)*x 1 + (2696441893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312299371/10000000000 : ℝ)^4201 ≤ (43324796374449/100000000000000 : ℝ)^3177 := by
    have hnat : (5312299371 : ℕ)^4201*100000000000000^3177 ≤ 43324796374449^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312299371 10000000000 43324796374449 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207249669/1000000000 : ℝ)^4201 ≤ (3119812111373/25000000000000 : ℝ)^3177 := by
    have hnat : (207249669 : ℕ)^4201*25000000000000^3177 ≤ 3119812111373^3177*1000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207249669 1000000000 3119812111373 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696441893/5000000000 : ℝ)^4201 ≤ (44195955158737/100000000000000 : ℝ)^3177 := by
    have hnat : (2696441893 : ℕ)^4201*100000000000000^3177 ≤ 44195955158737^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696441893 5000000000 44195955158737 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312299371/10000000000 : ℝ), (-207249669/1000000000 : ℝ), (2696441893/5000000000 : ℝ)] ![(43324796374449/100000000000000 : ℝ), (3119812111373/25000000000000 : ℝ), (44195955158737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312299371/10000000000 : ℝ)|^4201 ≤ (43324796374449/100000000000000 : ℝ)^3177
        have hw : |(5312299371/10000000000 : ℝ)|=(5312299371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-207249669/1000000000 : ℝ)|^4201 ≤ (3119812111373/25000000000000 : ℝ)^3177
        have hw : |(-207249669/1000000000 : ℝ)|=(207249669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696441893/5000000000 : ℝ)|^4201 ≤ (44195955158737/100000000000000 : ℝ)^3177
        have hw : |(2696441893/5000000000 : ℝ)|=(2696441893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s5_6 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312299247/10000000000 : ℝ)*x 0 + (1078576791/2000000000 : ℝ)*x 1 + (-2072496629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312299247/10000000000 : ℝ)^4201 ≤ (43324795037203/100000000000000 : ℝ)^3177 := by
    have hnat : (5312299247 : ℕ)^4201*100000000000000^3177 ≤ 43324795037203^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312299247 10000000000 43324795037203 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078576791/2000000000 : ℝ)^4201 ≤ (44195956990139/100000000000000 : ℝ)^3177 := by
    have hnat : (1078576791 : ℕ)^4201*100000000000000^3177 ≤ 44195956990139^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078576791 2000000000 44195956990139 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072496629/10000000000 : ℝ)^4201 ≤ (12479247959801/100000000000000 : ℝ)^3177 := by
    have hnat : (2072496629 : ℕ)^4201*100000000000000^3177 ≤ 12479247959801^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072496629 10000000000 12479247959801 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312299247/10000000000 : ℝ), (1078576791/2000000000 : ℝ), (-2072496629/10000000000 : ℝ)] ![(43324795037203/100000000000000 : ℝ), (44195956990139/100000000000000 : ℝ), (12479247959801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312299247/10000000000 : ℝ)|^4201 ≤ (43324795037203/100000000000000 : ℝ)^3177
        have hw : |(5312299247/10000000000 : ℝ)|=(5312299247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078576791/2000000000 : ℝ)|^4201 ≤ (44195956990139/100000000000000 : ℝ)^3177
        have hw : |(1078576791/2000000000 : ℝ)|=(1078576791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2072496629/10000000000 : ℝ)|^4201 ≤ (12479247959801/100000000000000 : ℝ)^3177
        have hw : |(-2072496629/10000000000 : ℝ)|=(2072496629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s5_7 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4355259411/10000000000 : ℝ)*x 0 + (897046549/2000000000 : ℝ)*x 1 + (4228998481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355259411/10000000000 : ℝ)^4201 ≤ (6663343989899/20000000000000 : ℝ)^3177 := by
    have hnat : (4355259411 : ℕ)^4201*20000000000000^3177 ≤ 6663343989899^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355259411 10000000000 6663343989899 20000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897046549/2000000000 : ℝ)^4201 ≤ (34637735088877/100000000000000 : ℝ)^3177 := by
    have hnat : (897046549 : ℕ)^4201*100000000000000^3177 ≤ 34637735088877^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897046549 2000000000 34637735088877 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228998481/10000000000 : ℝ)^4201 ≤ (6409108989079/20000000000000 : ℝ)^3177 := by
    have hnat : (4228998481 : ℕ)^4201*20000000000000^3177 ≤ 6409108989079^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228998481 10000000000 6409108989079 20000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355259411/10000000000 : ℝ), (897046549/2000000000 : ℝ), (4228998481/10000000000 : ℝ)] ![(6663343989899/20000000000000 : ℝ), (34637735088877/100000000000000 : ℝ), (6409108989079/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355259411/10000000000 : ℝ)|^4201 ≤ (6663343989899/20000000000000 : ℝ)^3177
        have hw : |(4355259411/10000000000 : ℝ)|=(4355259411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(897046549/2000000000 : ℝ)|^4201 ≤ (34637735088877/100000000000000 : ℝ)^3177
        have hw : |(897046549/2000000000 : ℝ)|=(897046549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228998481/10000000000 : ℝ)|^4201 ≤ (6409108989079/20000000000000 : ℝ)^3177
        have hw : |(4228998481/10000000000 : ℝ)|=(4228998481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1209_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (1141/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14117/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (353/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (353/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (353/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (353/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (353/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (353/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (353/3125 : ℝ) ^ (8401/2048 : ℝ) ≤ (6516568476880167/50000000000000000000 : ℝ) := by
    have hpowers : (353/3125 : ℝ)^8401 ≤ (6516568476880167/50000000000000000000 : ℝ)^2048 := by
      have hnat : (353 : ℕ)^8401*50000000000000000000^2048 ≤ 6516568476880167^2048*3125^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        353 3125 6516568476880167 50000000000000000000 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (353/3125 : ℝ)) (X := (6516568476880167/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8401/2048 : ℝ) ≤ (16826715767167171/50000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8401 ≤ (16826715767167171/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8401*50000000000000000000^2048 ≤ 16826715767167171^2048*20000^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 16826715767167171 50000000000000000000 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (16826715767167171/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006516568476880167/25000000000000000000 : ℝ) ≤ (5000317691157671/5000000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (25006516568476880167/25000000000000000000 : ℝ)^2048 ≤ (5000317691157671/5000000000000000 : ℝ)^8401 := by
      have hnat : (25006516568476880167 : ℕ)^2048*5000000000000000^8401 ≤ 5000317691157671^8401*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006516568476880167 25000000000000000000 5000317691157671 5000000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000317691157671/5000000000000000 : ℝ)) (X := (25006516568476880167/25000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011671642122023669/25000000000000000000 : ℝ) ≤ (1250142240832129/1250000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (25011671642122023669/25000000000000000000 : ℝ)^2048 ≤ (1250142240832129/1250000000000000 : ℝ)^8401 := by
      have hnat : (25011671642122023669 : ℕ)^2048*1250000000000000^8401 ≤ 1250142240832129^8401*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011671642122023669 25000000000000000000 1250142240832129 1250000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250142240832129/1250000000000000 : ℝ)) (X := (25011671642122023669/25000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016826715767167171/25000000000000000000 : ℝ) ≤ (5000820235499361/5000000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (25016826715767167171/25000000000000000000 : ℝ)^2048 ≤ (5000820235499361/5000000000000000 : ℝ)^8401 := by
      have hnat : (25016826715767167171 : ℕ)^2048*5000000000000000^8401 ≤ 5000820235499361^8401*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016826715767167171 25000000000000000000 5000820235499361 5000000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000820235499361/5000000000000000 : ℝ)) (X := (25016826715767167171/25000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6516568476880167/50000000000000000000 : ℝ) ≤ ((14690256953428664829/14695000000000000000 : ℝ)+2*(50254434169/29390000000000 : ℝ)*(353/3125 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (14690256953428664829/14695000000000000000 : ℝ)+2*(50254434169/29390000000000 : ℝ)*(353/3125 : ℝ)=(5000317691157671/5000000000000000 : ℝ) by norm_num, show 1+2*(6516568476880167/50000000000000000000 : ℝ)=(25006516568476880167/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16826715767167171/50000000000000000000 : ℝ)+(6516568476880167/50000000000000000000 : ℝ) ≤ ((14690256953428664829/14695000000000000000 : ℝ)+(50254434169/29390000000000 : ℝ)*((2847/20000 : ℝ)+(353/3125 : ℝ)))^(8401/2048 : ℝ) := by
    rw [show (14690256953428664829/14695000000000000000 : ℝ)+(50254434169/29390000000000 : ℝ)*((2847/20000 : ℝ)+(353/3125 : ℝ))=(1250142240832129/1250000000000000 : ℝ) by norm_num, show 1+(16826715767167171/50000000000000000000 : ℝ)+(6516568476880167/50000000000000000000 : ℝ)=(25011671642122023669/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16826715767167171/50000000000000000000 : ℝ) ≤ ((14690256953428664829/14695000000000000000 : ℝ)+2*(50254434169/29390000000000 : ℝ)*(2847/20000 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (14690256953428664829/14695000000000000000 : ℝ)+2*(50254434169/29390000000000 : ℝ)*(2847/20000 : ℝ)=(5000820235499361/5000000000000000 : ℝ) by norm_num, show 1+2*(16826715767167171/50000000000000000000 : ℝ)=(25016826715767167171/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14690256953428664829/14695000000000000000 : ℝ)*(X 1 0+X 2 0)+(50254434169/29390000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (353/3125 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (14690256953428664829/14695000000000000000 : ℝ)) (alpha := (50254434169/29390000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14690256953428664829/14695000000000000000 : ℝ)*(X 0 1+X 2 1)+(50254434169/29390000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (353/3125 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (14690256953428664829/14695000000000000000 : ℝ)) (alpha := (50254434169/29390000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14690256953428664829/14695000000000000000 : ℝ)*(X 0 2+X 1 2)+(50254434169/29390000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (353/3125 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (14690256953428664829/14695000000000000000 : ℝ)) (alpha := (50254434169/29390000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1067565963/5000000000 : ℝ)*X 0 0+(674151743/1250000000 : ℝ)*X 0 1+(2632716351/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344829137/10000000000 : ℝ)*X 1 0+(-2199947853/10000000000 : ℝ)*X 1 1+(5265432709/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336207277/2500000000 : ℝ)*X 2 0+(2632716383/5000000000 : ℝ)*X 2 1+(-439989563/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088812291/2500000000 : ℝ)*X 0 0+(4228333289/10000000000 : ℝ)*X 0 1+(4485895561/10000000000 : ℝ)*X 0 2+(1088812291/2500000000 : ℝ)*X 1 0+(4228333289/10000000000 : ℝ)*X 1 1+(4485895561/10000000000 : ℝ)*X 1 2+(1088812291/2500000000 : ℝ)*X 2 0+(4228333289/10000000000 : ℝ)*X 2 1+(4485895561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2135136677/10000000000 : ℝ)*X 0 0+(5265761799/10000000000 : ℝ)*X 0 1+(107857677/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312299371/10000000000 : ℝ)*X 1 0+(-207249669/1000000000 : ℝ)*X 1 1+(2696441893/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312299247/10000000000 : ℝ)*X 2 0+(1078576791/2000000000 : ℝ)*X 2 1+(-2072496629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4355259411/10000000000 : ℝ)*X 0 0+(897046549/2000000000 : ℝ)*X 0 1+(4228998481/10000000000 : ℝ)*X 0 2+(4355259411/10000000000 : ℝ)*X 1 0+(897046549/2000000000 : ℝ)*X 1 1+(4228998481/10000000000 : ℝ)*X 1 2+(4355259411/10000000000 : ℝ)*X 2 0+(897046549/2000000000 : ℝ)*X 2 1+(4228998481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (144254484408559702364674281/36737500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (110168611/12500000000000 : ℝ)*(base19) + (103244221/12500000000000 : ℝ)*(base23) + (138251/2000000000000 : ℝ)*(lower2) + (57623669/100000000000000 : ℝ)*(upper3) + (25107643/25000000000000 : ℝ)*(upper5) + (292712728083121/5000000000000 : ℝ)*(major0) + (292712728083121/5000000000000 : ℝ)*(major1) + (292712728083121/5000000000000 : ℝ)*(major2) + (7825901376503629/100000000000000 : ℝ)*(sp0) + (7825929144174333/100000000000000 : ℝ)*(sp1) + (7825929199569453/100000000000000 : ℝ)*(sp2) + (970642013319833/25000000000000 : ℝ)*(sp3) + (3581127449/12500000000000 : ℝ)*(sp4) + (10913634689/100000000000000 : ℝ)*(sp7) + (194128948345701/5000000000000 : ℝ)*(f.failure) + (391296501276161/5000000000000 : ℝ)*(f.sum) + (24241565374311/2939000000000000000000000000 : ℝ)*base66 + (500299543857823691/73475000000000000000000000000000 : ℝ)*base68 + (731185501575273691/73475000000000000000000000000000 : ℝ)*base70 + (454354466261048691/73475000000000000000000000000000 : ℝ)*base72 + (4377568301149/734750000000000000000000000 : ℝ)*base74 + (818458617158298691/73475000000000000000000000000000 : ℝ)*base76 + (794991715598973691/73475000000000000000000000000000 : ℝ)*base78 + (402822334381473691/73475000000000000000000000000000 : ℝ)*base80 + (101921582693/1469500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (936527/500000000000000000000 : ℝ)*base89 + (936527/500000000000000000000 : ℝ)*base91 + (936527/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1062281740859046733305193221/91843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (810237403/50000000000000 : ℝ)*(base19) + (2192112743/100000000000000 : ℝ)*(base23) + (5750147/3125000000000 : ℝ)*(upper3) + (322904937/100000000000000 : ℝ)*(lower4) + (82160433/100000000000000 : ℝ)*(upper5) + (1471139793849017/25000000000000 : ℝ)*(major0) + (1471139793849017/25000000000000 : ℝ)*(major1) + (1471139793849017/25000000000000 : ℝ)*(major2) + (8037933679/20000000000000 : ℝ)*(sp1) + (32131421837/50000000000000 : ℝ)*(sp2) + (1573288157042233/20000000000000 : ℝ)*(sp4) + (7866398975067963/100000000000000 : ℝ)*(sp5) + (7866374330254749/100000000000000 : ℝ)*(sp6) + (3902677180041483/100000000000000 : ℝ)*(sp7) + (3902677180041483/100000000000000 : ℝ)*(f.failure) + (1573288157042233/20000000000000 : ℝ)*(f.sum) + (716685135909/367375000000000000000000000 : ℝ)*base65 + (4919757270669373093/367375000000000000000000000000000 : ℝ)*base67 + (767437670445251907/367375000000000000000000000000000 : ℝ)*base70 + (5644927515305748093/367375000000000000000000000000000 : ℝ)*base71 + (1806952218393/1469500000000000000000000000 : ℝ)*base74 + (7961724905692623093/367375000000000000000000000000000 : ℝ)*base75 + (3591830135784123093/367375000000000000000000000000000 : ℝ)*base77 + (2144316755842373093/367375000000000000000000000000000 : ℝ)*base79 + (3109314243401/734750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (24284159/10000000000000000000000 : ℝ)*base90 + (24284159/10000000000000000000000 : ℝ)*base92 + (24284159/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1209_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1209_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1209_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16311/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1209_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1209_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1209_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16311/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1209_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
