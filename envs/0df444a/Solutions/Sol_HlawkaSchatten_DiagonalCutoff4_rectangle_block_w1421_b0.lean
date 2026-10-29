-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1421_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:02.390291+00:00
-- url     : https://prove2.me/submissions/87797542-51e6-4a33-81da-ca5633d67b46

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
theorem support_rectangle_w1421_s0_0 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1763351939/10000000000 : ℝ)*x 0 + (1192697869/2000000000 : ℝ)*x 1 + (4829404771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1763351939/10000000000 : ℝ)^4381 ≤ (5192979174817/50000000000000 : ℝ)^3357 := by
    have hnat : (1763351939 : ℕ)^4381*50000000000000^3357 ≤ 5192979174817^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1763351939 10000000000 5192979174817 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1192697869/2000000000 : ℝ)^4381 ≤ (50935478869709/100000000000000 : ℝ)^3357 := by
    have hnat : (1192697869 : ℕ)^4381*100000000000000^3357 ≤ 50935478869709^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192697869 2000000000 50935478869709 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4829404771/10000000000 : ℝ)^4381 ≤ (38678562774357/100000000000000 : ℝ)^3357 := by
    have hnat : (4829404771 : ℕ)^4381*100000000000000^3357 ≤ 38678562774357^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4829404771 10000000000 38678562774357 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1763351939/10000000000 : ℝ), (1192697869/2000000000 : ℝ), (4829404771/10000000000 : ℝ)] ![(5192979174817/50000000000000 : ℝ), (50935478869709/100000000000000 : ℝ), (38678562774357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1763351939/10000000000 : ℝ)|^4381 ≤ (5192979174817/50000000000000 : ℝ)^3357
        have hw : |(-1763351939/10000000000 : ℝ)|=(1763351939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1192697869/2000000000 : ℝ)|^4381 ≤ (50935478869709/100000000000000 : ℝ)^3357
        have hw : |(1192697869/2000000000 : ℝ)|=(1192697869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4829404771/10000000000 : ℝ)|^4381 ≤ (38678562774357/100000000000000 : ℝ)^3357
        have hw : |(4829404771/10000000000 : ℝ)|=(4829404771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s0_1 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2746494691/5000000000 : ℝ)*x 0 + (-150271779/625000000 : ℝ)*x 1 + (4829405159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2746494691/5000000000 : ℝ)^4381 ≤ (45755311659729/100000000000000 : ℝ)^3357 := by
    have hnat : (2746494691 : ℕ)^4381*100000000000000^3357 ≤ 45755311659729^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746494691 5000000000 45755311659729 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (150271779/625000000 : ℝ)^4381 ≤ (3891530372417/25000000000000 : ℝ)^3357 := by
    have hnat : (150271779 : ℕ)^4381*25000000000000^3357 ≤ 3891530372417^3357*625000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150271779 625000000 3891530372417 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4829405159/10000000000 : ℝ)^4381 ≤ (19339283414863/50000000000000 : ℝ)^3357 := by
    have hnat : (4829405159 : ℕ)^4381*50000000000000^3357 ≤ 19339283414863^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4829405159 10000000000 19339283414863 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2746494691/5000000000 : ℝ), (-150271779/625000000 : ℝ), (4829405159/10000000000 : ℝ)] ![(45755311659729/100000000000000 : ℝ), (3891530372417/25000000000000 : ℝ), (19339283414863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2746494691/5000000000 : ℝ)|^4381 ≤ (45755311659729/100000000000000 : ℝ)^3357
        have hw : |(2746494691/5000000000 : ℝ)|=(2746494691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-150271779/625000000 : ℝ)|^4381 ≤ (3891530372417/25000000000000 : ℝ)^3357
        have hw : |(-150271779/625000000 : ℝ)|=(150271779/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4829405159/10000000000 : ℝ)|^4381 ≤ (19339283414863/50000000000000 : ℝ)^3357
        have hw : |(4829405159/10000000000 : ℝ)|=(4829405159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s0_2 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5492989729/10000000000 : ℝ)*x 0 + (4829404997/10000000000 : ℝ)*x 1 + (-1202174109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5492989729/10000000000 : ℝ)^4381 ≤ (45755315431837/100000000000000 : ℝ)^3357 := by
    have hnat : (5492989729 : ℕ)^4381*100000000000000^3357 ≤ 45755315431837^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492989729 10000000000 45755315431837 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4829404997/10000000000 : ℝ)^4381 ≤ (7735713027301/20000000000000 : ℝ)^3357 := by
    have hnat : (4829404997 : ℕ)^4381*20000000000000^3357 ≤ 7735713027301^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4829404997 10000000000 7735713027301 20000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1202174109/5000000000 : ℝ)^4381 ≤ (972882463201/6250000000000 : ℝ)^3357 := by
    have hnat : (1202174109 : ℕ)^4381*6250000000000^3357 ≤ 972882463201^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202174109 5000000000 972882463201 6250000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5492989729/10000000000 : ℝ), (4829404997/10000000000 : ℝ), (-1202174109/5000000000 : ℝ)] ![(45755315431837/100000000000000 : ℝ), (7735713027301/20000000000000 : ℝ), (972882463201/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5492989729/10000000000 : ℝ)|^4381 ≤ (45755315431837/100000000000000 : ℝ)^3357
        have hw : |(5492989729/10000000000 : ℝ)|=(5492989729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4829404997/10000000000 : ℝ)|^4381 ≤ (7735713027301/20000000000000 : ℝ)^3357
        have hw : |(4829404997/10000000000 : ℝ)|=(4829404997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1202174109/5000000000 : ℝ)|^4381 ≤ (972882463201/6250000000000 : ℝ)^3357
        have hw : |(-1202174109/5000000000 : ℝ)|=(1202174109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s0_3 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2083575181/5000000000 : ℝ)*x 0 + (1551781427/5000000000 : ℝ)*x 1 + (2774889103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083575181/5000000000 : ℝ)^4381 ≤ (31906347831143/100000000000000 : ℝ)^3357 := by
    have hnat : (2083575181 : ℕ)^4381*100000000000000^3357 ≤ 31906347831143^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083575181 5000000000 31906347831143 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1551781427/5000000000 : ℝ)^4381 ≤ (21720039179143/100000000000000 : ℝ)^3357 := by
    have hnat : (1551781427 : ℕ)^4381*100000000000000^3357 ≤ 21720039179143^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1551781427 5000000000 21720039179143 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2774889103/5000000000 : ℝ)^4381 ≤ (46373612967869/100000000000000 : ℝ)^3357 := by
    have hnat : (2774889103 : ℕ)^4381*100000000000000^3357 ≤ 46373612967869^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2774889103 5000000000 46373612967869 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2083575181/5000000000 : ℝ), (1551781427/5000000000 : ℝ), (2774889103/5000000000 : ℝ)] ![(31906347831143/100000000000000 : ℝ), (21720039179143/100000000000000 : ℝ), (46373612967869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2083575181/5000000000 : ℝ)|^4381 ≤ (31906347831143/100000000000000 : ℝ)^3357
        have hw : |(2083575181/5000000000 : ℝ)|=(2083575181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1551781427/5000000000 : ℝ)|^4381 ≤ (21720039179143/100000000000000 : ℝ)^3357
        have hw : |(1551781427/5000000000 : ℝ)|=(1551781427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2774889103/5000000000 : ℝ)|^4381 ≤ (46373612967869/100000000000000 : ℝ)^3357
        have hw : |(2774889103/5000000000 : ℝ)|=(2774889103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s0_4 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-88370397/500000000 : ℝ)*x 0 + (1214609757/2500000000 : ℝ)*x 1 + (5933418349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88370397/500000000 : ℝ)^4381 ≤ (10417145794219/100000000000000 : ℝ)^3357 := by
    have hnat : (88370397 : ℕ)^4381*100000000000000^3357 ≤ 10417145794219^3357*500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88370397 500000000 10417145794219 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1214609757/2500000000 : ℝ)^4381 ≤ (38982306161797/100000000000000 : ℝ)^3357 := by
    have hnat : (1214609757 : ℕ)^4381*100000000000000^3357 ≤ 38982306161797^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1214609757 2500000000 38982306161797 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5933418349/10000000000 : ℝ)^4381 ≤ (25300274011267/50000000000000 : ℝ)^3357 := by
    have hnat : (5933418349 : ℕ)^4381*50000000000000^3357 ≤ 25300274011267^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5933418349 10000000000 25300274011267 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88370397/500000000 : ℝ), (1214609757/2500000000 : ℝ), (5933418349/10000000000 : ℝ)] ![(10417145794219/100000000000000 : ℝ), (38982306161797/100000000000000 : ℝ), (25300274011267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88370397/500000000 : ℝ)|^4381 ≤ (10417145794219/100000000000000 : ℝ)^3357
        have hw : |(-88370397/500000000 : ℝ)|=(88370397/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1214609757/2500000000 : ℝ)|^4381 ≤ (38982306161797/100000000000000 : ℝ)^3357
        have hw : |(1214609757/2500000000 : ℝ)|=(1214609757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5933418349/10000000000 : ℝ)|^4381 ≤ (25300274011267/50000000000000 : ℝ)^3357
        have hw : |(5933418349/10000000000 : ℝ)|=(5933418349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s0_5 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (518348973/1000000000 : ℝ)*x 0 + (-650167351/5000000000 : ℝ)*x 1 + (5933418433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518348973/1000000000 : ℝ)^4381 ≤ (10605038729463/25000000000000 : ℝ)^3357 := by
    have hnat : (518348973 : ℕ)^4381*25000000000000^3357 ≤ 10605038729463^3357*1000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518348973 1000000000 10605038729463 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (650167351/5000000000 : ℝ)^4381 ≤ (6979296112867/100000000000000 : ℝ)^3357 := by
    have hnat : (650167351 : ℕ)^4381*100000000000000^3357 ≤ 6979296112867^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650167351 5000000000 6979296112867 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5933418433/10000000000 : ℝ)^4381 ≤ (10120109791481/20000000000000 : ℝ)^3357 := by
    have hnat : (5933418433 : ℕ)^4381*20000000000000^3357 ≤ 10120109791481^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5933418433 10000000000 10120109791481 20000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518348973/1000000000 : ℝ), (-650167351/5000000000 : ℝ), (5933418433/10000000000 : ℝ)] ![(10605038729463/25000000000000 : ℝ), (6979296112867/100000000000000 : ℝ), (10120109791481/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518348973/1000000000 : ℝ)|^4381 ≤ (10605038729463/25000000000000 : ℝ)^3357
        have hw : |(518348973/1000000000 : ℝ)|=(518348973/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-650167351/5000000000 : ℝ)|^4381 ≤ (6979296112867/100000000000000 : ℝ)^3357
        have hw : |(-650167351/5000000000 : ℝ)|=(650167351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5933418433/10000000000 : ℝ)|^4381 ≤ (10120109791481/20000000000000 : ℝ)^3357
        have hw : |(5933418433/10000000000 : ℝ)|=(5933418433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s0_6 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1295872437/2500000000 : ℝ)*x 0 + (5933418259/10000000000 : ℝ)*x 1 + (-26006699/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1295872437/2500000000 : ℝ)^4381 ≤ (10605038777523/25000000000000 : ℝ)^3357 := by
    have hnat : (1295872437 : ℕ)^4381*25000000000000^3357 ≤ 10605038777523^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295872437 2500000000 10605038777523 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5933418259/10000000000 : ℝ)^4381 ≤ (50600547020887/100000000000000 : ℝ)^3357 := by
    have hnat : (5933418259 : ℕ)^4381*100000000000000^3357 ≤ 50600547020887^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5933418259 10000000000 50600547020887 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26006699/200000000 : ℝ)^4381 ≤ (1744824462497/25000000000000 : ℝ)^3357 := by
    have hnat : (26006699 : ℕ)^4381*25000000000000^3357 ≤ 1744824462497^3357*200000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26006699 200000000 1744824462497 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1295872437/2500000000 : ℝ), (5933418259/10000000000 : ℝ), (-26006699/200000000 : ℝ)] ![(10605038777523/25000000000000 : ℝ), (50600547020887/100000000000000 : ℝ), (1744824462497/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1295872437/2500000000 : ℝ)|^4381 ≤ (10605038777523/25000000000000 : ℝ)^3357
        have hw : |(1295872437/2500000000 : ℝ)|=(1295872437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5933418259/10000000000 : ℝ)|^4381 ≤ (50600547020887/100000000000000 : ℝ)^3357
        have hw : |(5933418259/10000000000 : ℝ)|=(5933418259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26006699/200000000 : ℝ)|^4381 ≤ (1744824462497/25000000000000 : ℝ)^3357
        have hw : |(-26006699/200000000 : ℝ)|=(26006699/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s0_7 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2087950541/5000000000 : ℝ)*x 0 + (2743575659/5000000000 : ℝ)*x 1 + (792106549/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087950541/5000000000 : ℝ)^4381 ≤ (31993814508233/100000000000000 : ℝ)^3357 := by
    have hnat : (2087950541 : ℕ)^4381*100000000000000^3357 ≤ 31993814508233^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087950541 5000000000 31993814508233 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2743575659/5000000000 : ℝ)^4381 ≤ (45691858522321/100000000000000 : ℝ)^3357 := by
    have hnat : (2743575659 : ℕ)^4381*100000000000000^3357 ≤ 45691858522321^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743575659 5000000000 45691858522321 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (792106549/2500000000 : ℝ)^4381 ≤ (5578581741369/25000000000000 : ℝ)^3357 := by
    have hnat : (792106549 : ℕ)^4381*25000000000000^3357 ≤ 5578581741369^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792106549 2500000000 5578581741369 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2087950541/5000000000 : ℝ), (2743575659/5000000000 : ℝ), (792106549/2500000000 : ℝ)] ![(31993814508233/100000000000000 : ℝ), (45691858522321/100000000000000 : ℝ), (5578581741369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2087950541/5000000000 : ℝ)|^4381 ≤ (31993814508233/100000000000000 : ℝ)^3357
        have hw : |(2087950541/5000000000 : ℝ)|=(2087950541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2743575659/5000000000 : ℝ)|^4381 ≤ (45691858522321/100000000000000 : ℝ)^3357
        have hw : |(2743575659/5000000000 : ℝ)|=(2743575659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(792106549/2500000000 : ℝ)|^4381 ≤ (5578581741369/25000000000000 : ℝ)^3357
        have hw : |(792106549/2500000000 : ℝ)|=(792106549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1421_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1991/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26313/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1095/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1095 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1095*1^256 ≤ 0^256*1^1095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1095 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1095/256 : ℝ) ≤ (1985517828349306813/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1095 ≤ (1985517828349306813/100000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1095*100000000000000000000^256 ≤ 1985517828349306813^256*5^1095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1985517828349306813 100000000000000000000 1095 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1985517828349306813/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1095 := by
      have hnat : (1 : ℕ)^256*1^1095 ≤ 1^1095*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (101985517828349306813/100000000000000000000 : ℝ) ≤ (401842815565317/400000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (101985517828349306813/100000000000000000000 : ℝ)^256 ≤ (401842815565317/400000000000000 : ℝ)^1095 := by
      have hnat : (101985517828349306813 : ℕ)^256*400000000000000^1095 ≤ 401842815565317^1095*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101985517828349306813 100000000000000000000 401842815565317 400000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (401842815565317/400000000000000 : ℝ)) (X := (101985517828349306813/100000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (51985517828349306813/50000000000000000000 : ℝ) ≤ (201842815565317/200000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (51985517828349306813/50000000000000000000 : ℝ)^256 ≤ (201842815565317/200000000000000 : ℝ)^1095 := by
      have hnat : (51985517828349306813 : ℕ)^256*200000000000000^1095 ≤ 201842815565317^1095*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51985517828349306813 50000000000000000000 201842815565317 200000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (201842815565317/200000000000000 : ℝ)) (X := (51985517828349306813/50000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1842815565317/160000000000000 : ℝ)*(0 : ℝ))^(1095/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(1842815565317/160000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1985517828349306813/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1842815565317/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1095/256 : ℝ) := by
    rw [show (1 : ℝ)+(1842815565317/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(401842815565317/400000000000000 : ℝ) by norm_num, show 1+(1985517828349306813/100000000000000000000 : ℝ)+(0 : ℝ)=(101985517828349306813/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1985517828349306813/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1842815565317/160000000000000 : ℝ)*(2/5 : ℝ))^(1095/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(1842815565317/160000000000000 : ℝ)*(2/5 : ℝ)=(201842815565317/200000000000000 : ℝ) by norm_num, show 1+2*(1985517828349306813/100000000000000000000 : ℝ)=(51985517828349306813/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1842815565317/160000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1842815565317/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1842815565317/160000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1842815565317/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1842815565317/160000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1842815565317/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1763351939/10000000000 : ℝ)*X 0 0+(1192697869/2000000000 : ℝ)*X 0 1+(4829404771/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2746494691/5000000000 : ℝ)*X 1 0+(-150271779/625000000 : ℝ)*X 1 1+(4829405159/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5492989729/10000000000 : ℝ)*X 2 0+(4829404997/10000000000 : ℝ)*X 2 1+(-1202174109/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2083575181/5000000000 : ℝ)*X 0 0+(1551781427/5000000000 : ℝ)*X 0 1+(2774889103/5000000000 : ℝ)*X 0 2+(2083575181/5000000000 : ℝ)*X 1 0+(1551781427/5000000000 : ℝ)*X 1 1+(2774889103/5000000000 : ℝ)*X 1 2+(2083575181/5000000000 : ℝ)*X 2 0+(1551781427/5000000000 : ℝ)*X 2 1+(2774889103/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-88370397/500000000 : ℝ)*X 0 0+(1214609757/2500000000 : ℝ)*X 0 1+(5933418349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((518348973/1000000000 : ℝ)*X 1 0+(-650167351/5000000000 : ℝ)*X 1 1+(5933418433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1295872437/2500000000 : ℝ)*X 2 0+(5933418259/10000000000 : ℝ)*X 2 1+(-26006699/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2087950541/5000000000 : ℝ)*X 0 0+(2743575659/5000000000 : ℝ)*X 0 1+(792106549/2500000000 : ℝ)*X 0 2+(2087950541/5000000000 : ℝ)*X 1 0+(2743575659/5000000000 : ℝ)*X 1 1+(792106549/2500000000 : ℝ)*X 1 2+(2087950541/5000000000 : ℝ)*X 2 0+(2743575659/5000000000 : ℝ)*X 2 1+(792106549/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1205738631712243024533/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (147316213/12500000000000 : ℝ)*(base19) + (1194574497/100000000000000 : ℝ)*(base23) + (66848359/50000000000000 : ℝ)*(upper3) + (2723029/12500000000000 : ℝ)*(upper4) + (180820799/100000000000000 : ℝ)*(upper5) + (80660999473067/12500000000000 : ℝ)*(major0) + (80660999473067/12500000000000 : ℝ)*(major1) + (80660999473067/12500000000000 : ℝ)*(major2) + (440886181051459/50000000000000 : ℝ)*(sp0) + (55110987628171/6250000000000 : ℝ)*(sp1) + (110221973250743/12500000000000 : ℝ)*(sp2) + (20439839597507/5000000000000 : ℝ)*(sp3) + (4618477523/100000000000000 : ℝ)*(sp4) + (2058273333/100000000000000 : ℝ)*(sp7) + (204399425111737/50000000000000 : ℝ)*(f.failure) + (22044424514511/2500000000000 : ℝ)*(f.sum) + (6723914453239/1000000000000000000000000000 : ℝ)*base65 + (10863363201239/2000000000000000000000000000 : ℝ)*base67 + (218422008761/2000000000000000000000000000 : ℝ)*base70 + (15029356541239/2000000000000000000000000000 : ℝ)*base71 + (6655087867239/1000000000000000000000000000 : ℝ)*base73 + (7734266553239/2000000000000000000000000000 : ℝ)*base75 + (3726028493239/2000000000000000000000000000 : ℝ)*base77 + (4446488426761/2000000000000000000000000000 : ℝ)*base80 + (4980448501239/1000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (4204823/2500000000000000000000 : ℝ)*base89 + (4204823/2500000000000000000000 : ℝ)*base91 + (4204823/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5762062438204733422089/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (645903309/100000000000000 : ℝ)*(base19) + (650237177/100000000000000 : ℝ)*(base23) + (115096843/100000000000000 : ℝ)*(base32) + (52838249/50000000000000 : ℝ)*(upper3) + (933123/2500000000000 : ℝ)*(upper5) + (680760673590039/100000000000000 : ℝ)*(major0) + (680760673590039/100000000000000 : ℝ)*(major1) + (680760673590039/100000000000000 : ℝ)*(major2) + (746365351/50000000000000 : ℝ)*(sp1) + (755605393/50000000000000 : ℝ)*(sp2) + (58140623125869/6250000000000 : ℝ)*(sp4) + (930247831379893/100000000000000 : ℝ)*(sp5) + (46512390428297/5000000000000 : ℝ)*(sp6) + (431271166034953/100000000000000 : ℝ)*(sp7) + (107817820282949/25000000000000 : ℝ)*(f.failure) + (58140623125869/6250000000000 : ℝ)*(f.sum) + (1091513989363/8000000000000000000000000000 : ℝ)*base65 + (79916528778637/16000000000000000000000000000 : ℝ)*base68 + (83617167466637/16000000000000000000000000000 : ℝ)*base70 + (34535102122637/16000000000000000000000000000 : ℝ)*base72 + (24614150442637/8000000000000000000000000000 : ℝ)*base74 + (58169724122637/16000000000000000000000000000 : ℝ)*base76 + (19472623082637/16000000000000000000000000000 : ℝ)*base78 + (8459741418637/16000000000000000000000000000 : ℝ)*base80 + (22838286442637/8000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (8088171/1250000000000000000000 : ℝ)*base89 + (8088171/1250000000000000000000 : ℝ)*base91 + (8088171/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1421_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1991/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26313/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1421_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1421_s1_0 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1936846851/10000000000 : ℝ)*x 0 + (1402109461/2500000000 : ℝ)*x 1 + (317077851/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1936846851/10000000000 : ℝ)^4381 ≤ (11739103211233/100000000000000 : ℝ)^3357 := by
    have hnat : (1936846851 : ℕ)^4381*100000000000000^3357 ≤ 11739103211233^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936846851 10000000000 11739103211233 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1402109461/2500000000 : ℝ)^4381 ≤ (47014312548199/100000000000000 : ℝ)^3357 := by
    have hnat : (1402109461 : ℕ)^4381*100000000000000^3357 ≤ 47014312548199^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1402109461 2500000000 47014312548199 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317077851/625000000 : ℝ)^4381 ≤ (41246584219717/100000000000000 : ℝ)^3357 := by
    have hnat : (317077851 : ℕ)^4381*100000000000000^3357 ≤ 41246584219717^3357*625000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317077851 625000000 41246584219717 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1936846851/10000000000 : ℝ), (1402109461/2500000000 : ℝ), (317077851/625000000 : ℝ)] ![(11739103211233/100000000000000 : ℝ), (47014312548199/100000000000000 : ℝ), (41246584219717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1936846851/10000000000 : ℝ)|^4381 ≤ (11739103211233/100000000000000 : ℝ)^3357
        have hw : |(-1936846851/10000000000 : ℝ)|=(1936846851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1402109461/2500000000 : ℝ)|^4381 ≤ (47014312548199/100000000000000 : ℝ)^3357
        have hw : |(1402109461/2500000000 : ℝ)|=(1402109461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317077851/625000000 : ℝ)|^4381 ≤ (41246584219717/100000000000000 : ℝ)^3357
        have hw : |(317077851/625000000 : ℝ)|=(317077851/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s1_1 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2698806317/5000000000 : ℝ)*x 0 + (-1110307467/5000000000 : ℝ)*x 1 + (5073242831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698806317/5000000000 : ℝ)^4381 ≤ (22360631614909/50000000000000 : ℝ)^3357 := by
    have hnat : (2698806317 : ℕ)^4381*50000000000000^3357 ≤ 22360631614909^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698806317 5000000000 22360631614909 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1110307467/5000000000 : ℝ)^4381 ≤ (14032182086271/100000000000000 : ℝ)^3357 := by
    have hnat : (1110307467 : ℕ)^4381*100000000000000^3357 ≤ 14032182086271^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110307467 5000000000 14032182086271 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5073242831/10000000000 : ℝ)^4381 ≤ (20623277335141/50000000000000 : ℝ)^3357 := by
    have hnat : (5073242831 : ℕ)^4381*50000000000000^3357 ≤ 20623277335141^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5073242831 10000000000 20623277335141 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698806317/5000000000 : ℝ), (-1110307467/5000000000 : ℝ), (5073242831/10000000000 : ℝ)] ![(22360631614909/50000000000000 : ℝ), (14032182086271/100000000000000 : ℝ), (20623277335141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698806317/5000000000 : ℝ)|^4381 ≤ (22360631614909/50000000000000 : ℝ)^3357
        have hw : |(2698806317/5000000000 : ℝ)|=(2698806317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1110307467/5000000000 : ℝ)|^4381 ≤ (14032182086271/100000000000000 : ℝ)^3357
        have hw : |(-1110307467/5000000000 : ℝ)|=(1110307467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5073242831/10000000000 : ℝ)|^4381 ≤ (20623277335141/50000000000000 : ℝ)^3357
        have hw : |(5073242831/10000000000 : ℝ)|=(5073242831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s1_2 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2698805471/5000000000 : ℝ)*x 0 + (2536622669/5000000000 : ℝ)*x 1 + (-2220613927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698805471/5000000000 : ℝ)^4381 ≤ (22360622467363/50000000000000 : ℝ)^3357 := by
    have hnat : (2698805471 : ℕ)^4381*50000000000000^3357 ≤ 22360622467363^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698805471 5000000000 22360622467363 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2536622669/5000000000 : ℝ)^4381 ≤ (20623290635039/50000000000000 : ℝ)^3357 := by
    have hnat : (2536622669 : ℕ)^4381*50000000000000^3357 ≤ 20623290635039^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536622669 5000000000 20623290635039 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2220613927/10000000000 : ℝ)^4381 ≤ (7016086890983/50000000000000 : ℝ)^3357 := by
    have hnat : (2220613927 : ℕ)^4381*50000000000000^3357 ≤ 7016086890983^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220613927 10000000000 7016086890983 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698805471/5000000000 : ℝ), (2536622669/5000000000 : ℝ), (-2220613927/10000000000 : ℝ)] ![(22360622467363/50000000000000 : ℝ), (20623290635039/50000000000000 : ℝ), (7016086890983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698805471/5000000000 : ℝ)|^4381 ≤ (22360622467363/50000000000000 : ℝ)^3357
        have hw : |(2698805471/5000000000 : ℝ)|=(2698805471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2536622669/5000000000 : ℝ)|^4381 ≤ (20623290635039/50000000000000 : ℝ)^3357
        have hw : |(2536622669/5000000000 : ℝ)|=(2536622669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2220613927/10000000000 : ℝ)|^4381 ≤ (7016086890983/50000000000000 : ℝ)^3357
        have hw : |(-2220613927/10000000000 : ℝ)|=(2220613927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s1_3 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (427809553/1000000000 : ℝ)*x 0 + (1867881407/5000000000 : ℝ)*x 1 + (611272261/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427809553/1000000000 : ℝ)^4381 ≤ (4127425612463/12500000000000 : ℝ)^3357 := by
    have hnat : (427809553 : ℕ)^4381*12500000000000^3357 ≤ 4127425612463^3357*1000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427809553 1000000000 4127425612463 12500000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1867881407/5000000000 : ℝ)^4381 ≤ (5533123023967/20000000000000 : ℝ)^3357 := by
    have hnat : (1867881407 : ℕ)^4381*20000000000000^3357 ≤ 5533123023967^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867881407 5000000000 5533123023967 20000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (611272261/1250000000 : ℝ)^4381 ≤ (39314979954103/100000000000000 : ℝ)^3357 := by
    have hnat : (611272261 : ℕ)^4381*100000000000000^3357 ≤ 39314979954103^3357*1250000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611272261 1250000000 39314979954103 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(427809553/1000000000 : ℝ), (1867881407/5000000000 : ℝ), (611272261/1250000000 : ℝ)] ![(4127425612463/12500000000000 : ℝ), (5533123023967/20000000000000 : ℝ), (39314979954103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(427809553/1000000000 : ℝ)|^4381 ≤ (4127425612463/12500000000000 : ℝ)^3357
        have hw : |(427809553/1000000000 : ℝ)|=(427809553/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1867881407/5000000000 : ℝ)|^4381 ≤ (5533123023967/20000000000000 : ℝ)^3357
        have hw : |(1867881407/5000000000 : ℝ)|=(1867881407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(611272261/1250000000 : ℝ)|^4381 ≤ (39314979954103/100000000000000 : ℝ)^3357
        have hw : |(611272261/1250000000 : ℝ)|=(611272261/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s1_4 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1937255201/10000000000 : ℝ)*x 0 + (2539779387/5000000000 : ℝ)*x 1 + (2801008679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1937255201/10000000000 : ℝ)^4381 ≤ (11742333252531/100000000000000 : ℝ)^3357 := by
    have hnat : (1937255201 : ℕ)^4381*100000000000000^3357 ≤ 11742333252531^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1937255201 10000000000 11742333252531 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2539779387/5000000000 : ℝ)^4381 ≤ (10328395216563/25000000000000 : ℝ)^3357 := by
    have hnat : (2539779387 : ℕ)^4381*25000000000000^3357 ≤ 10328395216563^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539779387 5000000000 10328395216563 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2801008679/5000000000 : ℝ)^4381 ≤ (46944085867837/100000000000000 : ℝ)^3357 := by
    have hnat : (2801008679 : ℕ)^4381*100000000000000^3357 ≤ 46944085867837^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2801008679 5000000000 46944085867837 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1937255201/10000000000 : ℝ), (2539779387/5000000000 : ℝ), (2801008679/5000000000 : ℝ)] ![(11742333252531/100000000000000 : ℝ), (10328395216563/25000000000000 : ℝ), (46944085867837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1937255201/10000000000 : ℝ)|^4381 ≤ (11742333252531/100000000000000 : ℝ)^3357
        have hw : |(-1937255201/10000000000 : ℝ)|=(1937255201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2539779387/5000000000 : ℝ)|^4381 ≤ (10328395216563/25000000000000 : ℝ)^3357
        have hw : |(2539779387/5000000000 : ℝ)|=(2539779387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2801008679/5000000000 : ℝ)|^4381 ≤ (46944085867837/100000000000000 : ℝ)^3357
        have hw : |(2801008679/5000000000 : ℝ)|=(2801008679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s1_5 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257863379/10000000000 : ℝ)*x 0 + (-1691840221/10000000000 : ℝ)*x 1 + (700252171/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257863379/10000000000 : ℝ)^4381 ≤ (43216199193411/100000000000000 : ℝ)^3357 := by
    have hnat : (5257863379 : ℕ)^4381*100000000000000^3357 ≤ 43216199193411^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257863379 10000000000 43216199193411 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1691840221/10000000000 : ℝ)^4381 ≤ (9839714825539/100000000000000 : ℝ)^3357 := by
    have hnat : (1691840221 : ℕ)^4381*100000000000000^3357 ≤ 9839714825539^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1691840221 10000000000 9839714825539 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (700252171/1250000000 : ℝ)^4381 ≤ (46944085977197/100000000000000 : ℝ)^3357 := by
    have hnat : (700252171 : ℕ)^4381*100000000000000^3357 ≤ 46944085977197^3357*1250000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      700252171 1250000000 46944085977197 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257863379/10000000000 : ℝ), (-1691840221/10000000000 : ℝ), (700252171/1250000000 : ℝ)] ![(43216199193411/100000000000000 : ℝ), (9839714825539/100000000000000 : ℝ), (46944085977197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257863379/10000000000 : ℝ)|^4381 ≤ (43216199193411/100000000000000 : ℝ)^3357
        have hw : |(5257863379/10000000000 : ℝ)|=(5257863379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1691840221/10000000000 : ℝ)|^4381 ≤ (9839714825539/100000000000000 : ℝ)^3357
        have hw : |(-1691840221/10000000000 : ℝ)|=(1691840221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(700252171/1250000000 : ℝ)|^4381 ≤ (46944085977197/100000000000000 : ℝ)^3357
        have hw : |(700252171/1250000000 : ℝ)|=(700252171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s1_6 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314465837/2500000000 : ℝ)*x 0 + (1400504333/2500000000 : ℝ)*x 1 + (-338368063/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314465837/2500000000 : ℝ)^4381 ≤ (5402024857611/12500000000000 : ℝ)^3357 := by
    have hnat : (1314465837 : ℕ)^4381*12500000000000^3357 ≤ 5402024857611^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314465837 2500000000 5402024857611 12500000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1400504333/2500000000 : ℝ)^4381 ≤ (46944085583501/100000000000000 : ℝ)^3357 := by
    have hnat : (1400504333 : ℕ)^4381*100000000000000^3357 ≤ 46944085583501^3357*2500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1400504333 2500000000 46944085583501 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338368063/2000000000 : ℝ)^4381 ≤ (2459928884751/25000000000000 : ℝ)^3357 := by
    have hnat : (338368063 : ℕ)^4381*25000000000000^3357 ≤ 2459928884751^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338368063 2000000000 2459928884751 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314465837/2500000000 : ℝ), (1400504333/2500000000 : ℝ), (-338368063/2000000000 : ℝ)] ![(5402024857611/12500000000000 : ℝ), (46944085583501/100000000000000 : ℝ), (2459928884751/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314465837/2500000000 : ℝ)|^4381 ≤ (5402024857611/12500000000000 : ℝ)^3357
        have hw : |(1314465837/2500000000 : ℝ)|=(1314465837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1400504333/2500000000 : ℝ)|^4381 ≤ (46944085583501/100000000000000 : ℝ)^3357
        have hw : |(1400504333/2500000000 : ℝ)|=(1400504333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-338368063/2000000000 : ℝ)|^4381 ≤ (2459928884751/25000000000000 : ℝ)^3357
        have hw : |(-338368063/2000000000 : ℝ)|=(338368063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s1_7 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4278975847/10000000000 : ℝ)*x 0 + (4876558039/10000000000 : ℝ)*x 1 + (3749617203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4278975847/10000000000 : ℝ)^4381 ≤ (6605654448073/20000000000000 : ℝ)^3357 := by
    have hnat : (4278975847 : ℕ)^4381*20000000000000^3357 ≤ 6605654448073^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278975847 10000000000 6605654448073 20000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4876558039/10000000000 : ℝ)^4381 ≤ (39172140124473/100000000000000 : ℝ)^3357 := by
    have hnat : (4876558039 : ℕ)^4381*100000000000000^3357 ≤ 39172140124473^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4876558039 10000000000 39172140124473 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3749617203/10000000000 : ℝ)^4381 ≤ (13899793814623/50000000000000 : ℝ)^3357 := by
    have hnat : (3749617203 : ℕ)^4381*50000000000000^3357 ≤ 13899793814623^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3749617203 10000000000 13899793814623 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4278975847/10000000000 : ℝ), (4876558039/10000000000 : ℝ), (3749617203/10000000000 : ℝ)] ![(6605654448073/20000000000000 : ℝ), (39172140124473/100000000000000 : ℝ), (13899793814623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4278975847/10000000000 : ℝ)|^4381 ≤ (6605654448073/20000000000000 : ℝ)^3357
        have hw : |(4278975847/10000000000 : ℝ)|=(4278975847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4876558039/10000000000 : ℝ)|^4381 ≤ (39172140124473/100000000000000 : ℝ)^3357
        have hw : |(4876558039/10000000000 : ℝ)|=(4876558039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3749617203/10000000000 : ℝ)|^4381 ≤ (13899793814623/50000000000000 : ℝ)^3357
        have hw : |(3749617203/10000000000 : ℝ)|=(3749617203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1421_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26313/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1991/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1517/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (189/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26313/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1991/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26313/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1991/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26313/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1991/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26313/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1991/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26313/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1991/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26313/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1991/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1991/100000 : ℝ) ^ (1095/256 : ℝ) ≤ (2651631009419/50000000000000000000 : ℝ) := by
    have hpowers : (1991/100000 : ℝ)^1095 ≤ (2651631009419/50000000000000000000 : ℝ)^256 := by
      have hnat : (1991 : ℕ)^1095*50000000000000000000^256 ≤ 2651631009419^256*100000^1095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1991 100000 2651631009419 50000000000000000000 1095 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1991/100000 : ℝ)) (X := (2651631009419/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hpowhi : (26313/100000 : ℝ) ^ (1095/256 : ℝ) ≤ (331031512068684519/100000000000000000000 : ℝ) := by
    have hpowers : (26313/100000 : ℝ)^1095 ≤ (331031512068684519/100000000000000000000 : ℝ)^256 := by
      have hnat : (26313 : ℕ)^1095*100000000000000000000^256 ≤ 331031512068684519^256*100000^1095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26313 100000 331031512068684519 100000000000000000000 1095 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26313/100000 : ℝ)) (X := (331031512068684519/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000002651631009419/25000000000000000000 : ℝ) ≤ (10000000247969867/10000000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (25000002651631009419/25000000000000000000 : ℝ)^256 ≤ (10000000247969867/10000000000000000 : ℝ)^1095 := by
      have hnat : (25000002651631009419 : ℕ)^256*10000000000000000^1095 ≤ 10000000247969867^1095*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000002651631009419 25000000000000000000 10000000247969867 10000000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000247969867/10000000000000000 : ℝ)) (X := (25000002651631009419/25000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100331036815330703357/100000000000000000000 : ℝ) ≤ (10007729512144291/10000000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (100331036815330703357/100000000000000000000 : ℝ)^256 ≤ (10007729512144291/10000000000000000 : ℝ)^1095 := by
      have hnat : (100331036815330703357 : ℕ)^256*10000000000000000^1095 ≤ 10007729512144291^1095*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100331036815330703357 100000000000000000000 10007729512144291 10000000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007729512144291/10000000000000000 : ℝ)) (X := (100331036815330703357/100000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50331031512068684519/50000000000000000000 : ℝ) ≤ (2003091755263743/2000000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (50331031512068684519/50000000000000000000 : ℝ)^256 ≤ (2003091755263743/2000000000000000 : ℝ)^1095 := by
      have hnat : (50331031512068684519 : ℕ)^256*2000000000000000^1095 ≤ 2003091755263743^1095*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50331031512068684519 50000000000000000000 2003091755263743 2000000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2003091755263743/2000000000000000 : ℝ)) (X := (50331031512068684519/50000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2651631009419/50000000000000000000 : ℝ) ≤ ((121594614050590274403/121610000000000000000 : ℝ)+2*(966158021803/304025000000000 : ℝ)*(1991/100000 : ℝ))^(1095/256 : ℝ) := by
    rw [show (121594614050590274403/121610000000000000000 : ℝ)+2*(966158021803/304025000000000 : ℝ)*(1991/100000 : ℝ)=(10000000247969867/10000000000000000 : ℝ) by norm_num, show 1+2*(2651631009419/50000000000000000000 : ℝ)=(25000002651631009419/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(331031512068684519/100000000000000000000 : ℝ)+(2651631009419/50000000000000000000 : ℝ) ≤ ((121594614050590274403/121610000000000000000 : ℝ)+(966158021803/304025000000000 : ℝ)*((26313/100000 : ℝ)+(1991/100000 : ℝ)))^(1095/256 : ℝ) := by
    rw [show (121594614050590274403/121610000000000000000 : ℝ)+(966158021803/304025000000000 : ℝ)*((26313/100000 : ℝ)+(1991/100000 : ℝ))=(10007729512144291/10000000000000000 : ℝ) by norm_num, show 1+(331031512068684519/100000000000000000000 : ℝ)+(2651631009419/50000000000000000000 : ℝ)=(100331036815330703357/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(331031512068684519/100000000000000000000 : ℝ) ≤ ((121594614050590274403/121610000000000000000 : ℝ)+2*(966158021803/304025000000000 : ℝ)*(26313/100000 : ℝ))^(1095/256 : ℝ) := by
    rw [show (121594614050590274403/121610000000000000000 : ℝ)+2*(966158021803/304025000000000 : ℝ)*(26313/100000 : ℝ)=(2003091755263743/2000000000000000 : ℝ) by norm_num, show 1+2*(331031512068684519/100000000000000000000 : ℝ)=(50331031512068684519/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (121594614050590274403/121610000000000000000 : ℝ)*(X 1 0+X 2 0)+(966158021803/304025000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (1991/100000 : ℝ)) (hi := (26313/100000 : ℝ)) (c := (121594614050590274403/121610000000000000000 : ℝ)) (alpha := (966158021803/304025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (121594614050590274403/121610000000000000000 : ℝ)*(X 0 1+X 2 1)+(966158021803/304025000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (1991/100000 : ℝ)) (hi := (26313/100000 : ℝ)) (c := (121594614050590274403/121610000000000000000 : ℝ)) (alpha := (966158021803/304025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (121594614050590274403/121610000000000000000 : ℝ)*(X 0 2+X 1 2)+(966158021803/304025000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (1991/100000 : ℝ)) (hi := (26313/100000 : ℝ)) (c := (121594614050590274403/121610000000000000000 : ℝ)) (alpha := (966158021803/304025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1936846851/10000000000 : ℝ)*X 0 0+(1402109461/2500000000 : ℝ)*X 0 1+(317077851/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2698806317/5000000000 : ℝ)*X 1 0+(-1110307467/5000000000 : ℝ)*X 1 1+(5073242831/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2698805471/5000000000 : ℝ)*X 2 0+(2536622669/5000000000 : ℝ)*X 2 1+(-2220613927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((427809553/1000000000 : ℝ)*X 0 0+(1867881407/5000000000 : ℝ)*X 0 1+(611272261/1250000000 : ℝ)*X 0 2+(427809553/1000000000 : ℝ)*X 1 0+(1867881407/5000000000 : ℝ)*X 1 1+(611272261/1250000000 : ℝ)*X 1 2+(427809553/1000000000 : ℝ)*X 2 0+(1867881407/5000000000 : ℝ)*X 2 1+(611272261/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1937255201/10000000000 : ℝ)*X 0 0+(2539779387/5000000000 : ℝ)*X 0 1+(2801008679/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5257863379/10000000000 : ℝ)*X 1 0+(-1691840221/10000000000 : ℝ)*X 1 1+(700252171/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1314465837/2500000000 : ℝ)*X 2 0+(1400504333/2500000000 : ℝ)*X 2 1+(-338368063/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4278975847/10000000000 : ℝ)*X 0 0+(4876558039/10000000000 : ℝ)*X 0 1+(3749617203/10000000000 : ℝ)*X 0 2+(4278975847/10000000000 : ℝ)*X 1 0+(4876558039/10000000000 : ℝ)*X 1 1+(3749617203/10000000000 : ℝ)*X 1 2+(4278975847/10000000000 : ℝ)*X 2 0+(4876558039/10000000000 : ℝ)*X 2 1+(3749617203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (561688622103270248932833/60805000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76765809/50000000000000 : ℝ)*(base1) + (228422727/10000000000000 : ℝ)*(base19) + (1698506553/100000000000000 : ℝ)*(base23) + (1646987/800000000000 : ℝ)*(upper3) + (528797029/100000000000000 : ℝ)*(upper5) + (170921686706299/12500000000000 : ℝ)*(major0) + (170921686706299/12500000000000 : ℝ)*(major1) + (170921686706299/12500000000000 : ℝ)*(major2) + (1868490779830499/100000000000000 : ℝ)*(sp0) + (934247208672039/50000000000000 : ℝ)*(sp1) + (373699000612959/20000000000000 : ℝ)*(sp2) + (866245712722589/100000000000000 : ℝ)*(sp3) + (3037636233/50000000000000 : ℝ)*(sp4) + (4111557221/100000000000000 : ℝ)*(sp7) + (866249977811427/100000000000000 : ℝ)*(f.failure) + (467124175392837/25000000000000 : ℝ)*(f.sum) + (12251765543353/30402500000000000000000000000 : ℝ)*base66 + (3890766353429239497/1520125000000000000000000000000000 : ℝ)*base67 + (6962887291138989497/1520125000000000000000000000000000 : ℝ)*base69 + (3642629452388760503/1520125000000000000000000000000000 : ℝ)*base72 + (3410209865639/60805000000000000000000000000 : ℝ)*base73 + (2746907507181760503/1520125000000000000000000000000000 : ℝ)*base76 + (1086319143671489497/1520125000000000000000000000000000 : ℝ)*base77 + (4223288268329510503/1520125000000000000000000000000000 : ℝ)*base80 + (70606031744727/30402500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (39207667/5000000000000000000000 : ℝ)*base90 + (39207667/5000000000000000000000 : ℝ)*base92 + (39207667/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28419607405098333274370920269/3040250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85651663/100000000000000 : ℝ)*(base1) + (1909941421/100000000000000 : ℝ)*(base19) + (1892660211/100000000000000 : ℝ)*(base23) + (3448833/1562500000000 : ℝ)*(upper3) + (102520427/50000000000000 : ℝ)*(upper5) + (700346365834341/50000000000000 : ℝ)*(major0) + (700346365834341/50000000000000 : ℝ)*(major1) + (700346365834341/50000000000000 : ℝ)*(major2) + (271001809/2500000000000 : ℝ)*(sp1) + (5307299101/50000000000000 : ℝ)*(sp2) + (1914027062498797/100000000000000 : ℝ)*(sp4) + (1914014226833353/100000000000000 : ℝ)*(sp5) + (1914014469588721/100000000000000 : ℝ)*(sp6) + (443679044622843/50000000000000 : ℝ)*(sp7) + (887358174897349/100000000000000 : ℝ)*(f.failure) + (957013488423567/50000000000000 : ℝ)*(f.sum) + (102048112145641/60805000000000000000000000000 : ℝ)*base66 + (3094964954916126577/6080500000000000000000000000000000 : ℝ)*base68 + (994232391947873423/6080500000000000000000000000000000 : ℝ)*base69 + (26310663200594626577/6080500000000000000000000000000000 : ℝ)*base72 + (277446315838721/60805000000000000000000000000 : ℝ)*base74 + (7462574058961126577/6080500000000000000000000000000000 : ℝ)*base76 + (51859343882122873423/6080500000000000000000000000000000 : ℝ)*base77 + (29408935356401126577/6080500000000000000000000000000000 : ℝ)*base80 + (265810390606061/60805000000000000000000000000 : ℝ)*base82 + (7245771/5000000000000000000000 : ℝ)*base89 + (7245771/5000000000000000000000 : ℝ)*base91 + (7245771/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1421_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26313/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1991/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1517/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (189/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1421_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1421_s2_0 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-394115013/2000000000 : ℝ)*x 0 + (682498271/1250000000 : ℝ)*x 1 + (519999667/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (394115013/2000000000 : ℝ)^4381 ≤ (12006589925363/100000000000000 : ℝ)^3357 := by
    have hnat : (394115013 : ℕ)^4381*100000000000000^3357 ≤ 12006589925363^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394115013 2000000000 12006589925363 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682498271/1250000000 : ℝ)^4381 ≤ (5674609398119/12500000000000 : ℝ)^3357 := by
    have hnat : (682498271 : ℕ)^4381*12500000000000^3357 ≤ 5674609398119^3357*1250000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682498271 1250000000 5674609398119 12500000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519999667/1000000000 : ℝ)^4381 ≤ (10649133717479/25000000000000 : ℝ)^3357 := by
    have hnat : (519999667 : ℕ)^4381*25000000000000^3357 ≤ 10649133717479^3357*1000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519999667 1000000000 10649133717479 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-394115013/2000000000 : ℝ), (682498271/1250000000 : ℝ), (519999667/1000000000 : ℝ)] ![(12006589925363/100000000000000 : ℝ), (5674609398119/12500000000000 : ℝ), (10649133717479/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-394115013/2000000000 : ℝ)|^4381 ≤ (12006589925363/100000000000000 : ℝ)^3357
        have hw : |(-394115013/2000000000 : ℝ)|=(394115013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(682498271/1250000000 : ℝ)|^4381 ≤ (5674609398119/12500000000000 : ℝ)^3357
        have hw : |(682498271/1250000000 : ℝ)|=(682498271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519999667/1000000000 : ℝ)|^4381 ≤ (10649133717479/25000000000000 : ℝ)^3357
        have hw : |(519999667/1000000000 : ℝ)|=(519999667/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s2_1 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5360651027/10000000000 : ℝ)*x 0 + (-263048283/1250000000 : ℝ)*x 1 + (2599998299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360651027/10000000000 : ℝ)^4381 ≤ (44322026427701/100000000000000 : ℝ)^3357 := by
    have hnat : (5360651027 : ℕ)^4381*100000000000000^3357 ≤ 44322026427701^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360651027 10000000000 44322026427701 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263048283/1250000000 : ℝ)^4381 ≤ (1635179932307/12500000000000 : ℝ)^3357 := by
    have hnat : (263048283 : ℕ)^4381*12500000000000^3357 ≤ 1635179932307^3357*1250000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263048283 1250000000 1635179932307 12500000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2599998299/5000000000 : ℝ)^4381 ≤ (42596534100209/100000000000000 : ℝ)^3357 := by
    have hnat : (2599998299 : ℕ)^4381*100000000000000^3357 ≤ 42596534100209^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599998299 5000000000 42596534100209 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360651027/10000000000 : ℝ), (-263048283/1250000000 : ℝ), (2599998299/5000000000 : ℝ)] ![(44322026427701/100000000000000 : ℝ), (1635179932307/12500000000000 : ℝ), (42596534100209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360651027/10000000000 : ℝ)|^4381 ≤ (44322026427701/100000000000000 : ℝ)^3357
        have hw : |(5360651027/10000000000 : ℝ)|=(5360651027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-263048283/1250000000 : ℝ)|^4381 ≤ (1635179932307/12500000000000 : ℝ)^3357
        have hw : |(-263048283/1250000000 : ℝ)|=(263048283/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2599998299/5000000000 : ℝ)|^4381 ≤ (42596534100209/100000000000000 : ℝ)^3357
        have hw : |(2599998299/5000000000 : ℝ)|=(2599998299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s2_2 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5360650689/10000000000 : ℝ)*x 0 + (5199996979/10000000000 : ℝ)*x 1 + (-2104386211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360650689/10000000000 : ℝ)^4381 ≤ (2216101139033/5000000000000 : ℝ)^3357 := by
    have hnat : (5360650689 : ℕ)^4381*5000000000000^3357 ≤ 2216101139033^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360650689 10000000000 2216101139033 5000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5199996979/10000000000 : ℝ)^4381 ≤ (10649134543311/25000000000000 : ℝ)^3357 := by
    have hnat : (5199996979 : ℕ)^4381*25000000000000^3357 ≤ 10649134543311^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199996979 10000000000 10649134543311 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2104386211/10000000000 : ℝ)^4381 ≤ (817589939281/6250000000000 : ℝ)^3357 := by
    have hnat : (2104386211 : ℕ)^4381*6250000000000^3357 ≤ 817589939281^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104386211 10000000000 817589939281 6250000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360650689/10000000000 : ℝ), (5199996979/10000000000 : ℝ), (-2104386211/10000000000 : ℝ)] ![(2216101139033/5000000000000 : ℝ), (10649134543311/25000000000000 : ℝ), (817589939281/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360650689/10000000000 : ℝ)|^4381 ≤ (2216101139033/5000000000000 : ℝ)^3357
        have hw : |(5360650689/10000000000 : ℝ)|=(5360650689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5199996979/10000000000 : ℝ)|^4381 ≤ (10649134543311/25000000000000 : ℝ)^3357
        have hw : |(5199996979/10000000000 : ℝ)|=(5199996979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2104386211/10000000000 : ℝ)|^4381 ≤ (817589939281/6250000000000 : ℝ)^3357
        have hw : |(-2104386211/10000000000 : ℝ)|=(2104386211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s2_3 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2150941933/5000000000 : ℝ)*x 0 + (2014858559/5000000000 : ℝ)*x 1 + (28690707/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150941933/5000000000 : ℝ)^4381 ≤ (33259217734713/100000000000000 : ℝ)^3357 := by
    have hnat : (2150941933 : ℕ)^4381*100000000000000^3357 ≤ 33259217734713^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150941933 5000000000 33259217734713 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2014858559/5000000000 : ℝ)^4381 ≤ (30540052480537/100000000000000 : ℝ)^3357 := by
    have hnat : (2014858559 : ℕ)^4381*100000000000000^3357 ≤ 30540052480537^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014858559 5000000000 30540052480537 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28690707/62500000 : ℝ)^4381 ≤ (36200729763963/100000000000000 : ℝ)^3357 := by
    have hnat : (28690707 : ℕ)^4381*100000000000000^3357 ≤ 36200729763963^3357*62500000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28690707 62500000 36200729763963 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150941933/5000000000 : ℝ), (2014858559/5000000000 : ℝ), (28690707/62500000 : ℝ)] ![(33259217734713/100000000000000 : ℝ), (30540052480537/100000000000000 : ℝ), (36200729763963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150941933/5000000000 : ℝ)|^4381 ≤ (33259217734713/100000000000000 : ℝ)^3357
        have hw : |(2150941933/5000000000 : ℝ)|=(2150941933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2014858559/5000000000 : ℝ)|^4381 ≤ (30540052480537/100000000000000 : ℝ)^3357
        have hw : |(2014858559/5000000000 : ℝ)|=(2014858559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28690707/62500000 : ℝ)|^4381 ≤ (36200729763963/100000000000000 : ℝ)^3357
        have hw : |(28690707/62500000 : ℝ)|=(28690707/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s2_4 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-98531111/500000000 : ℝ)*x 0 + (650187003/1250000000 : ℝ)*x 1 + (2729237139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98531111/500000000 : ℝ)^4381 ≤ (300174121983/2500000000000 : ℝ)^3357 := by
    have hnat : (98531111 : ℕ)^4381*2500000000000^3357 ≤ 300174121983^3357*500000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98531111 500000000 300174121983 2500000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (650187003/1250000000 : ℝ)^4381 ≤ (42612564237851/100000000000000 : ℝ)^3357 := by
    have hnat : (650187003 : ℕ)^4381*100000000000000^3357 ≤ 42612564237851^3357*1250000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650187003 1250000000 42612564237851 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729237139/5000000000 : ℝ)^4381 ≤ (45380470866897/100000000000000 : ℝ)^3357 := by
    have hnat : (2729237139 : ℕ)^4381*100000000000000^3357 ≤ 45380470866897^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729237139 5000000000 45380470866897 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98531111/500000000 : ℝ), (650187003/1250000000 : ℝ), (2729237139/5000000000 : ℝ)] ![(300174121983/2500000000000 : ℝ), (42612564237851/100000000000000 : ℝ), (45380470866897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98531111/500000000 : ℝ)|^4381 ≤ (300174121983/2500000000000 : ℝ)^3357
        have hw : |(-98531111/500000000 : ℝ)|=(98531111/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(650187003/1250000000 : ℝ)|^4381 ≤ (42612564237851/100000000000000 : ℝ)^3357
        have hw : |(650187003/1250000000 : ℝ)|=(650187003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729237139/5000000000 : ℝ)|^4381 ≤ (45380470866897/100000000000000 : ℝ)^3357
        have hw : |(2729237139/5000000000 : ℝ)|=(2729237139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s2_5 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293096397/10000000000 : ℝ)*x 0 + (-922954217/5000000000 : ℝ)*x 1 + (2729237287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293096397/10000000000 : ℝ)^4381 ≤ (43594512810351/100000000000000 : ℝ)^3357 := by
    have hnat : (5293096397 : ℕ)^4381*100000000000000^3357 ≤ 43594512810351^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293096397 10000000000 43594512810351 100000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922954217/5000000000 : ℝ)^4381 ≤ (1378126636459/12500000000000 : ℝ)^3357 := by
    have hnat : (922954217 : ℕ)^4381*12500000000000^3357 ≤ 1378126636459^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922954217 5000000000 1378126636459 12500000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729237287/5000000000 : ℝ)^4381 ≤ (22690237039211/50000000000000 : ℝ)^3357 := by
    have hnat : (2729237287 : ℕ)^4381*50000000000000^3357 ≤ 22690237039211^3357*5000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729237287 5000000000 22690237039211 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293096397/10000000000 : ℝ), (-922954217/5000000000 : ℝ), (2729237287/5000000000 : ℝ)] ![(43594512810351/100000000000000 : ℝ), (1378126636459/12500000000000 : ℝ), (22690237039211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293096397/10000000000 : ℝ)|^4381 ≤ (43594512810351/100000000000000 : ℝ)^3357
        have hw : |(5293096397/10000000000 : ℝ)|=(5293096397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-922954217/5000000000 : ℝ)|^4381 ≤ (1378126636459/12500000000000 : ℝ)^3357
        have hw : |(-922954217/5000000000 : ℝ)|=(922954217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729237287/5000000000 : ℝ)|^4381 ≤ (22690237039211/50000000000000 : ℝ)^3357
        have hw : |(2729237287/5000000000 : ℝ)|=(2729237287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s2_6 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058619271/2000000000 : ℝ)*x 0 + (5458474557/10000000000 : ℝ)*x 1 + (-369181703/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058619271/2000000000 : ℝ)^4381 ≤ (21797256179459/50000000000000 : ℝ)^3357 := by
    have hnat : (1058619271 : ℕ)^4381*50000000000000^3357 ≤ 21797256179459^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058619271 2000000000 21797256179459 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5458474557/10000000000 : ℝ)^4381 ≤ (5672559236747/12500000000000 : ℝ)^3357 := by
    have hnat : (5458474557 : ℕ)^4381*12500000000000^3357 ≤ 5672559236747^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458474557 10000000000 5672559236747 12500000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (369181703/2000000000 : ℝ)^4381 ≤ (1102501372303/10000000000000 : ℝ)^3357 := by
    have hnat : (369181703 : ℕ)^4381*10000000000000^3357 ≤ 1102501372303^3357*2000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369181703 2000000000 1102501372303 10000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058619271/2000000000 : ℝ), (5458474557/10000000000 : ℝ), (-369181703/2000000000 : ℝ)] ![(21797256179459/50000000000000 : ℝ), (5672559236747/12500000000000 : ℝ), (1102501372303/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058619271/2000000000 : ℝ)|^4381 ≤ (21797256179459/50000000000000 : ℝ)^3357
        have hw : |(1058619271/2000000000 : ℝ)|=(1058619271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5458474557/10000000000 : ℝ)|^4381 ≤ (5672559236747/12500000000000 : ℝ)^3357
        have hw : |(5458474557/10000000000 : ℝ)|=(5458474557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-369181703/2000000000 : ℝ)|^4381 ≤ (1102501372303/10000000000000 : ℝ)^3357
        have hw : |(-369181703/2000000000 : ℝ)|=(369181703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1421_s2_7 (p : ℝ) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4301985319/10000000000 : ℝ)*x 0 + (183491167/400000000 : ℝ)*x 1 + (4032977923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301985319/10000000000 : ℝ)^4381 ≤ (16630120680837/50000000000000 : ℝ)^3357 := by
    have hnat : (4301985319 : ℕ)^4381*50000000000000^3357 ≤ 16630120680837^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301985319 10000000000 16630120680837 50000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183491167/400000000 : ℝ)^4381 ≤ (9041862811813/25000000000000 : ℝ)^3357 := by
    have hnat : (183491167 : ℕ)^4381*25000000000000^3357 ≤ 9041862811813^3357*400000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183491167 400000000 9041862811813 25000000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4032977923/10000000000 : ℝ)^4381 ≤ (3821538421123/12500000000000 : ℝ)^3357 := by
    have hnat : (4032977923 : ℕ)^4381*12500000000000^3357 ≤ 3821538421123^3357*10000000000^4381 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032977923 10000000000 3821538421123 12500000000000 4381 3357 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4381/1024 : ℝ)) 4381 3357 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301985319/10000000000 : ℝ), (183491167/400000000 : ℝ), (4032977923/10000000000 : ℝ)] ![(16630120680837/50000000000000 : ℝ), (9041862811813/25000000000000 : ℝ), (3821538421123/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301985319/10000000000 : ℝ)|^4381 ≤ (16630120680837/50000000000000 : ℝ)^3357
        have hw : |(4301985319/10000000000 : ℝ)|=(4301985319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(183491167/400000000 : ℝ)|^4381 ≤ (9041862811813/25000000000000 : ℝ)^3357
        have hw : |(183491167/400000000 : ℝ)|=(183491167/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4032977923/10000000000 : ℝ)|^4381 ≤ (3821538421123/12500000000000 : ℝ)^3357
        have hw : |(4032977923/10000000000 : ℝ)|=(4032977923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1421_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (189/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1517/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2581/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (633/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (189/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1517/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (189/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1517/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (189/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1517/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (189/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1517/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (189/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1517/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (189/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1517/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1517/20000 : ℝ) ^ (1095/256 : ℝ) ≤ (809384767244669/50000000000000000000 : ℝ) := by
    have hpowers : (1517/20000 : ℝ)^1095 ≤ (809384767244669/50000000000000000000 : ℝ)^256 := by
      have hnat : (1517 : ℕ)^1095*50000000000000000000^256 ≤ 809384767244669^256*20000^1095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1517 20000 809384767244669 50000000000000000000 1095 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1517/20000 : ℝ)) (X := (809384767244669/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hpowhi : (189/1000 : ℝ) ^ (1095/256 : ℝ) ≤ (10048203759703633/12500000000000000000 : ℝ) := by
    have hpowers : (189/1000 : ℝ)^1095 ≤ (10048203759703633/12500000000000000000 : ℝ)^256 := by
      have hnat : (189 : ℕ)^1095*12500000000000000000^256 ≤ 10048203759703633^256*1000^1095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        189 1000 10048203759703633 12500000000000000000 1095 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (189/1000 : ℝ)) (X := (10048203759703633/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000809384767244669/25000000000000000000 : ℝ) ≤ (10000075689472327/10000000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (25000809384767244669/25000000000000000000 : ℝ)^256 ≤ (10000075689472327/10000000000000000 : ℝ)^1095 := by
      have hnat : (25000809384767244669 : ℕ)^256*10000000000000000^1095 ≤ 10000075689472327^1095*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000809384767244669 25000000000000000000 10000075689472327 10000000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000075689472327/10000000000000000 : ℝ)) (X := (25000809384767244669/25000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50041002199806059201/50000000000000000000 : ℝ) ≤ (39069986634639/39062500000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (50041002199806059201/50000000000000000000 : ℝ)^256 ≤ (39069986634639/39062500000000 : ℝ)^1095 := by
      have hnat : (50041002199806059201 : ℕ)^256*39062500000000^1095 ≤ 39069986634639^1095*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50041002199806059201 50000000000000000000 39069986634639 39062500000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39069986634639/39062500000000 : ℝ)) (X := (50041002199806059201/50000000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (6260048203759703633/6250000000000000000 : ℝ) ≤ (10003757467462841/10000000000000000 : ℝ) ^ (1095/256 : ℝ) := by
    have hpowers : (6260048203759703633/6250000000000000000 : ℝ)^256 ≤ (10003757467462841/10000000000000000 : ℝ)^1095 := by
      have hnat : (6260048203759703633 : ℕ)^256*10000000000000000^1095 ≤ 10003757467462841^1095*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6260048203759703633 6250000000000000000 10003757467462841 10000000000000000 256 1095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003757467462841/10000000000000000 : ℝ)) (X := (6260048203759703633/6250000000000000000 : ℝ)) (by norm_num) 1095 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(809384767244669/50000000000000000000 : ℝ) ≤ ((22624586028064266263/22630000000000000000 : ℝ)+2*(1840888995257/1131500000000000 : ℝ)*(1517/20000 : ℝ))^(1095/256 : ℝ) := by
    rw [show (22624586028064266263/22630000000000000000 : ℝ)+2*(1840888995257/1131500000000000 : ℝ)*(1517/20000 : ℝ)=(10000075689472327/10000000000000000 : ℝ) by norm_num, show 1+2*(809384767244669/50000000000000000000 : ℝ)=(25000809384767244669/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10048203759703633/12500000000000000000 : ℝ)+(809384767244669/50000000000000000000 : ℝ) ≤ ((22624586028064266263/22630000000000000000 : ℝ)+(1840888995257/1131500000000000 : ℝ)*((189/1000 : ℝ)+(1517/20000 : ℝ)))^(1095/256 : ℝ) := by
    rw [show (22624586028064266263/22630000000000000000 : ℝ)+(1840888995257/1131500000000000 : ℝ)*((189/1000 : ℝ)+(1517/20000 : ℝ))=(39069986634639/39062500000000 : ℝ) by norm_num, show 1+(10048203759703633/12500000000000000000 : ℝ)+(809384767244669/50000000000000000000 : ℝ)=(50041002199806059201/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10048203759703633/12500000000000000000 : ℝ) ≤ ((22624586028064266263/22630000000000000000 : ℝ)+2*(1840888995257/1131500000000000 : ℝ)*(189/1000 : ℝ))^(1095/256 : ℝ) := by
    rw [show (22624586028064266263/22630000000000000000 : ℝ)+2*(1840888995257/1131500000000000 : ℝ)*(189/1000 : ℝ)=(10003757467462841/10000000000000000 : ℝ) by norm_num, show 1+2*(10048203759703633/12500000000000000000 : ℝ)=(6260048203759703633/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22624586028064266263/22630000000000000000 : ℝ)*(X 1 0+X 2 0)+(1840888995257/1131500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (1517/20000 : ℝ)) (hi := (189/1000 : ℝ)) (c := (22624586028064266263/22630000000000000000 : ℝ)) (alpha := (1840888995257/1131500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22624586028064266263/22630000000000000000 : ℝ)*(X 0 1+X 2 1)+(1840888995257/1131500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (1517/20000 : ℝ)) (hi := (189/1000 : ℝ)) (c := (22624586028064266263/22630000000000000000 : ℝ)) (alpha := (1840888995257/1131500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22624586028064266263/22630000000000000000 : ℝ)*(X 0 2+X 1 2)+(1840888995257/1131500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1095/256 : ℝ)) (lo := (1517/20000 : ℝ)) (hi := (189/1000 : ℝ)) (c := (22624586028064266263/22630000000000000000 : ℝ)) (alpha := (1840888995257/1131500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-394115013/2000000000 : ℝ)*X 0 0+(682498271/1250000000 : ℝ)*X 0 1+(519999667/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5360651027/10000000000 : ℝ)*X 1 0+(-263048283/1250000000 : ℝ)*X 1 1+(2599998299/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5360650689/10000000000 : ℝ)*X 2 0+(5199996979/10000000000 : ℝ)*X 2 1+(-2104386211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2150941933/5000000000 : ℝ)*X 0 0+(2014858559/5000000000 : ℝ)*X 0 1+(28690707/62500000 : ℝ)*X 0 2+(2150941933/5000000000 : ℝ)*X 1 0+(2014858559/5000000000 : ℝ)*X 1 1+(28690707/62500000 : ℝ)*X 1 2+(2150941933/5000000000 : ℝ)*X 2 0+(2014858559/5000000000 : ℝ)*X 2 1+(28690707/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-98531111/500000000 : ℝ)*X 0 0+(650187003/1250000000 : ℝ)*X 0 1+(2729237139/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293096397/10000000000 : ℝ)*X 1 0+(-922954217/5000000000 : ℝ)*X 1 1+(2729237287/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058619271/2000000000 : ℝ)*X 2 0+(5458474557/10000000000 : ℝ)*X 2 1+(-369181703/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4301985319/10000000000 : ℝ)*X 0 0+(183491167/400000000 : ℝ)*X 0 1+(4032977923/10000000000 : ℝ)*X 0 2+(4301985319/10000000000 : ℝ)*X 1 0+(183491167/400000000 : ℝ)*X 1 1+(4032977923/10000000000 : ℝ)*X 1 2+(4301985319/10000000000 : ℝ)*X 2 0+(183491167/400000000 : ℝ)*X 2 1+(4032977923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1421_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5531583079179061104611674881/565750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (734817491/50000000000000 : ℝ)*(base19) + (976486437/100000000000000 : ℝ)*(base23) + (134353351/100000000000000 : ℝ)*(lower2) + (288352153/100000000000000 : ℝ)*(upper3) + (86913179/100000000000000 : ℝ)*(upper5) + (1407384782639971/50000000000000 : ℝ)*(major0) + (1407384782639971/50000000000000 : ℝ)*(major1) + (1407384782639971/50000000000000 : ℝ)*(major2) + (961582094307707/25000000000000 : ℝ)*(sp0) + (153853678877447/4000000000000 : ℝ)*(sp1) + (48079280813559/1250000000000 : ℝ)*(sp2) + (3566372771001/200000000000 : ℝ)*(sp3) + (1506434033/10000000000000 : ℝ)*(sp4) + (14027459/156250000000 : ℝ)*(sp7) + (89159768153713/5000000000000 : ℝ)*(f.failure) + (1923171720785579/50000000000000 : ℝ)*(f.sum) + (95483760326797/28287500000000000000000000000 : ℝ)*base65 + (1681860621594461627/1131500000000000000000000000000000 : ℝ)*base68 + (277339598691538373/1131500000000000000000000000000000 : ℝ)*base69 + (2447863025864038373/1131500000000000000000000000000000 : ℝ)*base71 + (172737466512547/28287500000000000000000000000 : ℝ)*base73 + (5132879751966538373/1131500000000000000000000000000000 : ℝ)*base75 + (12609671769181538373/1131500000000000000000000000000000 : ℝ)*base77 + (864946877658461627/1131500000000000000000000000000000 : ℝ)*base80 + (101493763876547/28287500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3074273/250000000000000000000 : ℝ)*base90 + (3074273/250000000000000000000 : ℝ)*base92 + (3074273/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7198881350624288901388510989/565750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1741862951/100000000000000 : ℝ)*(base19) + (951169/48828125000 : ℝ)*(base23) + (152441843/50000000000000 : ℝ)*(upper3) + (26897247/25000000000000 : ℝ)*(lower4) + (241600073/100000000000000 : ℝ)*(upper5) + (2847725126839801/100000000000000 : ℝ)*(major0) + (2847725126839801/100000000000000 : ℝ)*(major1) + (2847725126839801/100000000000000 : ℝ)*(major2) + (2326591073/10000000000000 : ℝ)*(sp1) + (25910105953/100000000000000 : ℝ)*(sp2) + (1945688331712393/50000000000000 : ℝ)*(sp4) + (778270331130221/20000000000000 : ℝ)*(sp5) + (1945674402662361/50000000000000 : ℝ)*(sp6) + (451018291526269/25000000000000 : ℝ)*(sp7) + (451018291526269/25000000000000 : ℝ)*(f.failure) + (1945688331712393/50000000000000 : ℝ)*(f.sum) + (275912070943557/56575000000000000000000000000 : ℝ)*base65 + (3913926100644926337/2263000000000000000000000000000000 : ℝ)*base68 + (16460560438040926337/2263000000000000000000000000000000 : ℝ)*base70 + (1213750212430073663/2263000000000000000000000000000000 : ℝ)*base71 + (158211987758107/56575000000000000000000000000 : ℝ)*base73 + (11166376719466926337/2263000000000000000000000000000000 : ℝ)*base76 + (3748220204485926337/2263000000000000000000000000000000 : ℝ)*base78 + (7824306996495926337/2263000000000000000000000000000000 : ℝ)*base80 + (42915747274067/14143750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (6353549/1250000000000000000000 : ℝ)*base90 + (6353549/1250000000000000000000 : ℝ)*base92 + (6353549/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1421_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (189/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1517/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2581/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (633/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1421_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1421_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2581/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (633/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1421_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1421_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1421_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1095/256 : ℝ) ≤ p) (hpb : p ≤ (4381/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78924879/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2581/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (633/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1421_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
