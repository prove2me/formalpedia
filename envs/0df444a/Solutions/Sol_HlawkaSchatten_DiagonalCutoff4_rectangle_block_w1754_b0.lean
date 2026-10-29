-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1754_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:23:18.550713+00:00
-- url     : https://prove2.me/submissions/d46eadcd-f42e-4ffe-81e5-a8d556f6b556

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
theorem support_rectangle_w1754_s0_0 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-72391861/625000000 : ℝ)*x 0 + (5618234087/10000000000 : ℝ)*x 1 + (4983812603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (72391861/625000000 : ℝ)^5839 ≤ (7323375693661/100000000000000 : ℝ)^4815 := by
    have hnat : (72391861 : ℕ)^5839*100000000000000^4815 ≤ 7323375693661^4815*625000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72391861 625000000 7323375693661 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5618234087/10000000000 : ℝ)^5839 ≤ (49698987480781/100000000000000 : ℝ)^4815 := by
    have hnat : (5618234087 : ℕ)^5839*100000000000000^4815 ≤ 49698987480781^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5618234087 10000000000 49698987480781 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4983812603/10000000000 : ℝ)^5839 ≤ (42977636821477/100000000000000 : ℝ)^4815 := by
    have hnat : (4983812603 : ℕ)^5839*100000000000000^4815 ≤ 42977636821477^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4983812603 10000000000 42977636821477 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-72391861/625000000 : ℝ), (5618234087/10000000000 : ℝ), (4983812603/10000000000 : ℝ)] ![(7323375693661/100000000000000 : ℝ), (49698987480781/100000000000000 : ℝ), (42977636821477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-72391861/625000000 : ℝ)|^5839 ≤ (7323375693661/100000000000000 : ℝ)^4815
        have hw : |(-72391861/625000000 : ℝ)|=(72391861/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5618234087/10000000000 : ℝ)|^5839 ≤ (49698987480781/100000000000000 : ℝ)^4815
        have hw : |(5618234087/10000000000 : ℝ)|=(5618234087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4983812603/10000000000 : ℝ)|^5839 ≤ (42977636821477/100000000000000 : ℝ)^4815
        have hw : |(4983812603/10000000000 : ℝ)|=(4983812603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s0_1 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5367173533/10000000000 : ℝ)*x 0 + (-14979663/100000000 : ℝ)*x 1 + (2491906577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367173533/10000000000 : ℝ)^5839 ≤ (940374788517/2000000000000 : ℝ)^4815 := by
    have hnat : (5367173533 : ℕ)^5839*2000000000000^4815 ≤ 940374788517^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367173533 10000000000 940374788517 2000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14979663/100000000 : ℝ)^5839 ≤ (5001808991087/50000000000000 : ℝ)^4815 := by
    have hnat : (14979663 : ℕ)^5839*50000000000000^4815 ≤ 5001808991087^4815*100000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14979663 100000000 5001808991087 50000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2491906577/5000000000 : ℝ)^5839 ≤ (8595528516699/20000000000000 : ℝ)^4815 := by
    have hnat : (2491906577 : ℕ)^5839*20000000000000^4815 ≤ 8595528516699^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491906577 5000000000 8595528516699 20000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367173533/10000000000 : ℝ), (-14979663/100000000 : ℝ), (2491906577/5000000000 : ℝ)] ![(940374788517/2000000000000 : ℝ), (5001808991087/50000000000000 : ℝ), (8595528516699/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367173533/10000000000 : ℝ)|^5839 ≤ (940374788517/2000000000000 : ℝ)^4815
        have hw : |(5367173533/10000000000 : ℝ)|=(5367173533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-14979663/100000000 : ℝ)|^5839 ≤ (5001808991087/50000000000000 : ℝ)^4815
        have hw : |(-14979663/100000000 : ℝ)|=(14979663/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2491906577/5000000000 : ℝ)|^5839 ≤ (8595528516699/20000000000000 : ℝ)^4815
        have hw : |(2491906577/5000000000 : ℝ)|=(2491906577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s0_2 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073435189/2000000000 : ℝ)*x 0 + (155744119/312500000 : ℝ)*x 1 + (-748982437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073435189/2000000000 : ℝ)^5839 ≤ (47018765049727/100000000000000 : ℝ)^4815 := by
    have hnat : (1073435189 : ℕ)^5839*100000000000000^4815 ≤ 47018765049727^4815*2000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073435189 2000000000 47018765049727 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (155744119/312500000 : ℝ)^5839 ≤ (21488814253929/50000000000000 : ℝ)^4815 := by
    have hnat : (155744119 : ℕ)^5839*50000000000000^4815 ≤ 21488814253929^4815*312500000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155744119 312500000 21488814253929 50000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (748982437/5000000000 : ℝ)^5839 ≤ (1000360643391/10000000000000 : ℝ)^4815 := by
    have hnat : (748982437 : ℕ)^5839*10000000000000^4815 ≤ 1000360643391^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748982437 5000000000 1000360643391 10000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073435189/2000000000 : ℝ), (155744119/312500000 : ℝ), (-748982437/5000000000 : ℝ)] ![(47018765049727/100000000000000 : ℝ), (21488814253929/50000000000000 : ℝ), (1000360643391/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073435189/2000000000 : ℝ)|^5839 ≤ (47018765049727/100000000000000 : ℝ)^4815
        have hw : |(1073435189/2000000000 : ℝ)|=(1073435189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(155744119/312500000 : ℝ)|^5839 ≤ (21488814253929/50000000000000 : ℝ)^4815
        have hw : |(155744119/312500000 : ℝ)|=(155744119/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-748982437/5000000000 : ℝ)|^5839 ≤ (1000360643391/10000000000000 : ℝ)^4815
        have hw : |(-748982437/5000000000 : ℝ)|=(748982437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s0_3 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (794334071/2000000000 : ℝ)*x 0 + (373438207/1250000000 : ℝ)*x 1 + (5106008741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (794334071/2000000000 : ℝ)^5839 ≤ (6527055781301/20000000000000 : ℝ)^4815 := by
    have hnat : (794334071 : ℕ)^5839*20000000000000^4815 ≤ 6527055781301^4815*2000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      794334071 2000000000 6527055781301 20000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (373438207/1250000000 : ℝ)^5839 ≤ (4621184415177/20000000000000 : ℝ)^4815 := by
    have hnat : (373438207 : ℕ)^5839*20000000000000^4815 ≤ 4621184415177^4815*1250000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373438207 1250000000 4621184415177 20000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5106008741/10000000000 : ℝ)^5839 ≤ (44258799000621/100000000000000 : ℝ)^4815 := by
    have hnat : (5106008741 : ℕ)^5839*100000000000000^4815 ≤ 44258799000621^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5106008741 10000000000 44258799000621 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(794334071/2000000000 : ℝ), (373438207/1250000000 : ℝ), (5106008741/10000000000 : ℝ)] ![(6527055781301/20000000000000 : ℝ), (4621184415177/20000000000000 : ℝ), (44258799000621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(794334071/2000000000 : ℝ)|^5839 ≤ (6527055781301/20000000000000 : ℝ)^4815
        have hw : |(794334071/2000000000 : ℝ)|=(794334071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(373438207/1250000000 : ℝ)|^5839 ≤ (4621184415177/20000000000000 : ℝ)^4815
        have hw : |(373438207/1250000000 : ℝ)|=(373438207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5106008741/10000000000 : ℝ)|^5839 ≤ (44258799000621/100000000000000 : ℝ)^4815
        have hw : |(5106008741/10000000000 : ℝ)|=(5106008741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s0_4 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-231910533/2000000000 : ℝ)*x 0 + (4999872219/10000000000 : ℝ)*x 1 + (5601650917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (231910533/2000000000 : ℝ)^5839 ≤ (7333213176473/100000000000000 : ℝ)^4815 := by
    have hnat : (231910533 : ℕ)^5839*100000000000000^4815 ≤ 7333213176473^4815*2000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231910533 2000000000 7333213176473 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4999872219/10000000000 : ℝ)^5839 ≤ (21572817935903/50000000000000 : ℝ)^4815 := by
    have hnat : (4999872219 : ℕ)^5839*50000000000000^4815 ≤ 21572817935903^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999872219 10000000000 21572817935903 50000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5601650917/10000000000 : ℝ)^5839 ≤ (12380287734113/25000000000000 : ℝ)^4815 := by
    have hnat : (5601650917 : ℕ)^5839*25000000000000^4815 ≤ 12380287734113^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5601650917 10000000000 12380287734113 25000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-231910533/2000000000 : ℝ), (4999872219/10000000000 : ℝ), (5601650917/10000000000 : ℝ)] ![(7333213176473/100000000000000 : ℝ), (21572817935903/50000000000000 : ℝ), (12380287734113/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-231910533/2000000000 : ℝ)|^5839 ≤ (7333213176473/100000000000000 : ℝ)^4815
        have hw : |(-231910533/2000000000 : ℝ)|=(231910533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4999872219/10000000000 : ℝ)|^5839 ≤ (21572817935903/50000000000000 : ℝ)^4815
        have hw : |(4999872219/10000000000 : ℝ)|=(4999872219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5601650917/10000000000 : ℝ)|^5839 ≤ (12380287734113/25000000000000 : ℝ)^4815
        have hw : |(5601650917/10000000000 : ℝ)|=(5601650917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s0_5 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5198205819/10000000000 : ℝ)*x 0 + (-176025357/2000000000 : ℝ)*x 1 + (5601650981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5198205819/10000000000 : ℝ)^5839 ≤ (45229770675147/100000000000000 : ℝ)^4815 := by
    have hnat : (5198205819 : ℕ)^5839*100000000000000^4815 ≤ 45229770675147^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198205819 10000000000 45229770675147 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176025357/2000000000 : ℝ)^5839 ≤ (1049815536579/20000000000000 : ℝ)^4815 := by
    have hnat : (176025357 : ℕ)^5839*20000000000000^4815 ≤ 1049815536579^4815*2000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176025357 2000000000 1049815536579 20000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5601650981/10000000000 : ℝ)^5839 ≤ (49521151622567/100000000000000 : ℝ)^4815 := by
    have hnat : (5601650981 : ℕ)^5839*100000000000000^4815 ≤ 49521151622567^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5601650981 10000000000 49521151622567 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5198205819/10000000000 : ℝ), (-176025357/2000000000 : ℝ), (5601650981/10000000000 : ℝ)] ![(45229770675147/100000000000000 : ℝ), (1049815536579/20000000000000 : ℝ), (49521151622567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5198205819/10000000000 : ℝ)|^5839 ≤ (45229770675147/100000000000000 : ℝ)^4815
        have hw : |(5198205819/10000000000 : ℝ)|=(5198205819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-176025357/2000000000 : ℝ)|^5839 ≤ (1049815536579/20000000000000 : ℝ)^4815
        have hw : |(-176025357/2000000000 : ℝ)|=(176025357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5601650981/10000000000 : ℝ)|^5839 ≤ (49521151622567/100000000000000 : ℝ)^4815
        have hw : |(5601650981/10000000000 : ℝ)|=(5601650981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s0_6 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039641059/2000000000 : ℝ)*x 0 + (2800825531/5000000000 : ℝ)*x 1 + (-880127431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039641059/2000000000 : ℝ)^5839 ≤ (706715080409/1562500000000 : ℝ)^4815 := by
    have hnat : (1039641059 : ℕ)^5839*1562500000000^4815 ≤ 706715080409^4815*2000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039641059 2000000000 706715080409 1562500000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2800825531/5000000000 : ℝ)^5839 ≤ (49521152490931/100000000000000 : ℝ)^4815 := by
    have hnat : (2800825531 : ℕ)^5839*100000000000000^4815 ≤ 49521152490931^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2800825531 5000000000 49521152490931 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880127431/10000000000 : ℝ)^5839 ≤ (5249082354999/100000000000000 : ℝ)^4815 := by
    have hnat : (880127431 : ℕ)^5839*100000000000000^4815 ≤ 5249082354999^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880127431 10000000000 5249082354999 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039641059/2000000000 : ℝ), (2800825531/5000000000 : ℝ), (-880127431/10000000000 : ℝ)] ![(706715080409/1562500000000 : ℝ), (49521152490931/100000000000000 : ℝ), (5249082354999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039641059/2000000000 : ℝ)|^5839 ≤ (706715080409/1562500000000 : ℝ)^4815
        have hw : |(1039641059/2000000000 : ℝ)|=(1039641059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2800825531/5000000000 : ℝ)|^5839 ≤ (49521152490931/100000000000000 : ℝ)^4815
        have hw : |(2800825531/5000000000 : ℝ)|=(2800825531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-880127431/10000000000 : ℝ)|^5839 ≤ (5249082354999/100000000000000 : ℝ)^4815
        have hw : |(-880127431/10000000000 : ℝ)|=(880127431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s0_7 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1987977659/5000000000 : ℝ)*x 0 + (5052379341/10000000000 : ℝ)*x 1 + (3042881161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1987977659/5000000000 : ℝ)^5839 ≤ (65355962793/200000000000 : ℝ)^4815 := by
    have hnat : (1987977659 : ℕ)^5839*200000000000^4815 ≤ 65355962793^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987977659 5000000000 65355962793 200000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5052379341/10000000000 : ℝ)^5839 ≤ (21847855329989/50000000000000 : ℝ)^4815 := by
    have hnat : (5052379341 : ℕ)^5839*50000000000000^4815 ≤ 21847855329989^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5052379341 10000000000 21847855329989 50000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3042881161/10000000000 : ℝ)^5839 ≤ (2953288490007/12500000000000 : ℝ)^4815 := by
    have hnat : (3042881161 : ℕ)^5839*12500000000000^4815 ≤ 2953288490007^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3042881161 10000000000 2953288490007 12500000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1987977659/5000000000 : ℝ), (5052379341/10000000000 : ℝ), (3042881161/10000000000 : ℝ)] ![(65355962793/200000000000 : ℝ), (21847855329989/50000000000000 : ℝ), (2953288490007/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1987977659/5000000000 : ℝ)|^5839 ≤ (65355962793/200000000000 : ℝ)^4815
        have hw : |(1987977659/5000000000 : ℝ)|=(1987977659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5052379341/10000000000 : ℝ)|^5839 ≤ (21847855329989/50000000000000 : ℝ)^4815
        have hw : |(5052379341/10000000000 : ℝ)|=(5052379341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3042881161/10000000000 : ℝ)|^5839 ≤ (2953288490007/12500000000000 : ℝ)^4815
        have hw : |(3042881161/10000000000 : ℝ)|=(3042881161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1754_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216963139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3441/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2061/10000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5823/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5823 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5823*1^1024 ≤ 0^1024*1^5823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5823/1024 : ℝ) ≤ (545889591869433931/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5823 ≤ (545889591869433931/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5823*100000000000000000000^1024 ≤ 545889591869433931^1024*5^5823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 545889591869433931 100000000000000000000 5823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (545889591869433931/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5823/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5823 := by
      have hnat : (1 : ℕ)^1024*1^5823 ≤ 1^5823*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100545889591869433931/100000000000000000000 : ℝ) ≤ (400383127371173/400000000000000 : ℝ) ^ (5823/1024 : ℝ) := by
    have hpowers : (100545889591869433931/100000000000000000000 : ℝ)^1024 ≤ (400383127371173/400000000000000 : ℝ)^5823 := by
      have hnat : (100545889591869433931 : ℕ)^1024*400000000000000^5823 ≤ 400383127371173^5823*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100545889591869433931 100000000000000000000 400383127371173 400000000000000 1024 5823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400383127371173/400000000000000 : ℝ)) (X := (100545889591869433931/100000000000000000000 : ℝ)) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50545889591869433931/50000000000000000000 : ℝ) ≤ (200383127371173/200000000000000 : ℝ) ^ (5823/1024 : ℝ) := by
    have hpowers : (50545889591869433931/50000000000000000000 : ℝ)^1024 ≤ (200383127371173/200000000000000 : ℝ)^5823 := by
      have hnat : (50545889591869433931 : ℕ)^1024*200000000000000^5823 ≤ 200383127371173^5823*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50545889591869433931 50000000000000000000 200383127371173 200000000000000 1024 5823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200383127371173/200000000000000 : ℝ)) (X := (50545889591869433931/50000000000000000000 : ℝ)) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(383127371173/160000000000000 : ℝ)*(0 : ℝ))^(5823/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(383127371173/160000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(545889591869433931/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(383127371173/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5823/1024 : ℝ) := by
    rw [show (1 : ℝ)+(383127371173/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(400383127371173/400000000000000 : ℝ) by norm_num, show 1+(545889591869433931/100000000000000000000 : ℝ)+(0 : ℝ)=(100545889591869433931/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(545889591869433931/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(383127371173/160000000000000 : ℝ)*(2/5 : ℝ))^(5823/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(383127371173/160000000000000 : ℝ)*(2/5 : ℝ)=(200383127371173/200000000000000 : ℝ) by norm_num, show 1+2*(545889591869433931/100000000000000000000 : ℝ)=(50545889591869433931/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(383127371173/160000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5823/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (383127371173/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(383127371173/160000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5823/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (383127371173/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(383127371173/160000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5823/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (383127371173/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-72391861/625000000 : ℝ)*X 0 0+(5618234087/10000000000 : ℝ)*X 0 1+(4983812603/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5367173533/10000000000 : ℝ)*X 1 0+(-14979663/100000000 : ℝ)*X 1 1+(2491906577/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1073435189/2000000000 : ℝ)*X 2 0+(155744119/312500000 : ℝ)*X 2 1+(-748982437/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((794334071/2000000000 : ℝ)*X 0 0+(373438207/1250000000 : ℝ)*X 0 1+(5106008741/10000000000 : ℝ)*X 0 2+(794334071/2000000000 : ℝ)*X 1 0+(373438207/1250000000 : ℝ)*X 1 1+(5106008741/10000000000 : ℝ)*X 1 2+(794334071/2000000000 : ℝ)*X 2 0+(373438207/1250000000 : ℝ)*X 2 1+(5106008741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-231910533/2000000000 : ℝ)*X 0 0+(4999872219/10000000000 : ℝ)*X 0 1+(5601650917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5198205819/10000000000 : ℝ)*X 1 0+(-176025357/2000000000 : ℝ)*X 1 1+(5601650981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1039641059/2000000000 : ℝ)*X 2 0+(2800825531/5000000000 : ℝ)*X 2 1+(-880127431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1987977659/5000000000 : ℝ)*X 0 0+(5052379341/10000000000 : ℝ)*X 0 1+(3042881161/10000000000 : ℝ)*X 0 2+(1987977659/5000000000 : ℝ)*X 1 0+(5052379341/10000000000 : ℝ)*X 1 1+(3042881161/10000000000 : ℝ)*X 1 2+(1987977659/5000000000 : ℝ)*X 2 0+(5052379341/10000000000 : ℝ)*X 2 1+(3042881161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6554677184617203873/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20997393/2000000000000 : ℝ)*(base19) + (2936137/195312500000 : ℝ)*(base23) + (86383339/100000000000000 : ℝ)*(base24) + (90463101/100000000000000 : ℝ)*(upper4) + (189727389/50000000000000 : ℝ)*(upper5) + (1024144176582791/100000000000000 : ℝ)*(major0) + (1024144176582791/100000000000000 : ℝ)*(major1) + (1024144176582791/100000000000000 : ℝ)*(major2) + (788121090170371/50000000000000 : ℝ)*(sp0) + (1576251060022403/100000000000000 : ℝ)*(sp1) + (157625052020657/10000000000000 : ℝ)*(sp2) + (94406808992121/20000000000000 : ℝ)*(sp3) + (992955131/10000000000000 : ℝ)*(sp4) + (989911837/50000000000000 : ℝ)*(sp7) + (472036024784279/100000000000000 : ℝ)*(f.failure) + (1576252109892053/100000000000000 : ℝ)*(f.sum) + (24651444036157/8000000000000000000000000000 : ℝ)*base66 + (60488938755843/16000000000000000000000000000 : ℝ)*base67 + (145884997043843/16000000000000000000000000000 : ℝ)*base69 + (68699745212157/16000000000000000000000000000 : ℝ)*base72 + (3665633228157/8000000000000000000000000000 : ℝ)*base74 + (54171935187843/16000000000000000000000000000 : ℝ)*base75 + (40639473171843/16000000000000000000000000000 : ℝ)*base77 + (38420647100157/16000000000000000000000000000 : ℝ)*base80 + (7317968171843/8000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (130308219/10000000000000000000000 : ℝ)*base90 + (130308219/10000000000000000000000 : ℝ)*base92 + (130308219/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8962775035250606394429/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2044044891/100000000000000 : ℝ)*(base19) + (950016977/50000000000000 : ℝ)*(base23) + (4279041/12500000000000 : ℝ)*(upper2) + (349105429/100000000000000 : ℝ)*(upper3) + (155747487/50000000000000 : ℝ)*(upper5) + (134961017286703/12500000000000 : ℝ)*(major0) + (134961017286703/12500000000000 : ℝ)*(major1) + (134961017286703/12500000000000 : ℝ)*(major2) + (4536562523/50000000000000 : ℝ)*(sp1) + (1553990393/20000000000000 : ℝ)*(sp2) + (1661739308636251/100000000000000 : ℝ)*(sp4) + (830864095733157/50000000000000 : ℝ)*(sp5) + (415432409662583/25000000000000 : ℝ)*(sp6) + (248818334595911/50000000000000 : ℝ)*(sp7) + (248818334595911/50000000000000 : ℝ)*(f.failure) + (1661739308636251/100000000000000 : ℝ)*(f.sum) + (750712068381/1000000000000000000000000000 : ℝ)*base66 + (2749317870619/2000000000000000000000000000 : ℝ)*base67 + (8944323394619/2000000000000000000000000000 : ℝ)*base69 + (9307842252619/2000000000000000000000000000 : ℝ)*base71 + (1661259400619/1000000000000000000000000000 : ℝ)*base73 + (235089492619/2000000000000000000000000000 : ℝ)*base75 + (175160109381/2000000000000000000000000000 : ℝ)*base78 + (543229200619/2000000000000000000000000000 : ℝ)*base79 + (5318307572619/1000000000000000000000000000 : ℝ)*base81 + (52875371/5000000000000000000000 : ℝ)*base90 + (52875371/5000000000000000000000 : ℝ)*base92 + (52875371/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1754_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216963139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3441/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2061/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1754_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1754_s1_0 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-599674827/5000000000 : ℝ)*x 0 + (5494467741/10000000000 : ℝ)*x 1 + (5080045411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (599674827/5000000000 : ℝ)^5839 ≤ (7639525375261/100000000000000 : ℝ)^4815 := by
    have hnat : (599674827 : ℕ)^5839*100000000000000^4815 ≤ 7639525375261^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599674827 5000000000 7639525375261 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5494467741/10000000000 : ℝ)^5839 ≤ (48374438604231/100000000000000 : ℝ)^4815 := by
    have hnat : (5494467741 : ℕ)^5839*100000000000000^4815 ≤ 48374438604231^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494467741 10000000000 48374438604231 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5080045411/10000000000 : ℝ)^5839 ≤ (43986036006327/100000000000000 : ℝ)^4815 := by
    have hnat : (5080045411 : ℕ)^5839*100000000000000^4815 ≤ 43986036006327^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080045411 10000000000 43986036006327 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-599674827/5000000000 : ℝ), (5494467741/10000000000 : ℝ), (5080045411/10000000000 : ℝ)] ![(7639525375261/100000000000000 : ℝ), (48374438604231/100000000000000 : ℝ), (43986036006327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-599674827/5000000000 : ℝ)|^5839 ≤ (7639525375261/100000000000000 : ℝ)^4815
        have hw : |(-599674827/5000000000 : ℝ)|=(599674827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5494467741/10000000000 : ℝ)|^5839 ≤ (48374438604231/100000000000000 : ℝ)^4815
        have hw : |(5494467741/10000000000 : ℝ)|=(5494467741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5080045411/10000000000 : ℝ)|^5839 ≤ (43986036006327/100000000000000 : ℝ)^4815
        have hw : |(5080045411/10000000000 : ℝ)|=(5080045411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s1_1 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1066853609/2000000000 : ℝ)*x 0 + (-88506457/625000000 : ℝ)*x 1 + (2540022549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066853609/2000000000 : ℝ)^5839 ≤ (46669396311247/100000000000000 : ℝ)^4815 := by
    have hnat : (1066853609 : ℕ)^5839*100000000000000^4815 ≤ 46669396311247^4815*2000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066853609 2000000000 46669396311247 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88506457/625000000 : ℝ)^5839 ≤ (9344570948197/100000000000000 : ℝ)^4815 := by
    have hnat : (88506457 : ℕ)^5839*100000000000000^4815 ≤ 9344570948197^4815*625000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88506457 625000000 9344570948197 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2540022549/5000000000 : ℝ)^5839 ≤ (21993016359913/50000000000000 : ℝ)^4815 := by
    have hnat : (2540022549 : ℕ)^5839*50000000000000^4815 ≤ 21993016359913^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540022549 5000000000 21993016359913 50000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1066853609/2000000000 : ℝ), (-88506457/625000000 : ℝ), (2540022549/5000000000 : ℝ)] ![(46669396311247/100000000000000 : ℝ), (9344570948197/100000000000000 : ℝ), (21993016359913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1066853609/2000000000 : ℝ)|^5839 ≤ (46669396311247/100000000000000 : ℝ)^4815
        have hw : |(1066853609/2000000000 : ℝ)|=(1066853609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-88506457/625000000 : ℝ)|^5839 ≤ (9344570948197/100000000000000 : ℝ)^4815
        have hw : |(-88506457/625000000 : ℝ)|=(88506457/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2540022549/5000000000 : ℝ)|^5839 ≤ (21993016359913/50000000000000 : ℝ)^4815
        have hw : |(2540022549/5000000000 : ℝ)|=(2540022549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s1_2 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5334267213/10000000000 : ℝ)*x 0 + (5080045617/10000000000 : ℝ)*x 1 + (-283220747/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5334267213/10000000000 : ℝ)^5839 ≤ (46669387484049/100000000000000 : ℝ)^4815 := by
    have hnat : (5334267213 : ℕ)^5839*100000000000000^4815 ≤ 46669387484049^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5334267213 10000000000 46669387484049 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5080045617/10000000000 : ℝ)^5839 ≤ (43986038169327/100000000000000 : ℝ)^4815 := by
    have hnat : (5080045617 : ℕ)^5839*100000000000000^4815 ≤ 43986038169327^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080045617 10000000000 43986038169327 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283220747/2000000000 : ℝ)^5839 ≤ (4672287166553/50000000000000 : ℝ)^4815 := by
    have hnat : (283220747 : ℕ)^5839*50000000000000^4815 ≤ 4672287166553^4815*2000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283220747 2000000000 4672287166553 50000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5334267213/10000000000 : ℝ), (5080045617/10000000000 : ℝ), (-283220747/2000000000 : ℝ)] ![(46669387484049/100000000000000 : ℝ), (43986038169327/100000000000000 : ℝ), (4672287166553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5334267213/10000000000 : ℝ)|^5839 ≤ (46669387484049/100000000000000 : ℝ)^4815
        have hw : |(5334267213/10000000000 : ℝ)|=(5334267213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5080045617/10000000000 : ℝ)|^5839 ≤ (43986038169327/100000000000000 : ℝ)^4815
        have hw : |(5080045617/10000000000 : ℝ)|=(5080045617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-283220747/2000000000 : ℝ)|^5839 ≤ (4672287166553/50000000000000 : ℝ)^4815
        have hw : |(-283220747/2000000000 : ℝ)|=(283220747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s1_3 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2005959803/5000000000 : ℝ)*x 0 + (3351851983/10000000000 : ℝ)*x 1 + (4735717559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2005959803/5000000000 : ℝ)^5839 ≤ (33036774355483/100000000000000 : ℝ)^4815 := by
    have hnat : (2005959803 : ℕ)^5839*100000000000000^4815 ≤ 33036774355483^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005959803 5000000000 33036774355483 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3351851983/10000000000 : ℝ)^5839 ≤ (26566096981943/100000000000000 : ℝ)^4815 := by
    have hnat : (3351851983 : ℕ)^5839*100000000000000^4815 ≤ 26566096981943^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3351851983 10000000000 26566096981943 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4735717559/10000000000 : ℝ)^5839 ≤ (1615885145873/4000000000000 : ℝ)^4815 := by
    have hnat : (4735717559 : ℕ)^5839*4000000000000^4815 ≤ 1615885145873^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4735717559 10000000000 1615885145873 4000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2005959803/5000000000 : ℝ), (3351851983/10000000000 : ℝ), (4735717559/10000000000 : ℝ)] ![(33036774355483/100000000000000 : ℝ), (26566096981943/100000000000000 : ℝ), (1615885145873/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2005959803/5000000000 : ℝ)|^5839 ≤ (33036774355483/100000000000000 : ℝ)^4815
        have hw : |(2005959803/5000000000 : ℝ)|=(2005959803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3351851983/10000000000 : ℝ)|^5839 ≤ (26566096981943/100000000000000 : ℝ)^4815
        have hw : |(3351851983/10000000000 : ℝ)|=(3351851983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4735717559/10000000000 : ℝ)|^5839 ≤ (1615885145873/4000000000000 : ℝ)^4815
        have hw : |(4735717559/10000000000 : ℝ)|=(4735717559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s1_4 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-149963229/1250000000 : ℝ)*x 0 + (2543455791/5000000000 : ℝ)*x 1 + (5487455513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (149963229/1250000000 : ℝ)^5839 ≤ (7642276710759/100000000000000 : ℝ)^4815 := by
    have hnat : (149963229 : ℕ)^5839*100000000000000^4815 ≤ 7642276710759^4815*1250000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149963229 1250000000 7642276710759 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2543455791/5000000000 : ℝ)^5839 ≤ (2753633823681/6250000000000 : ℝ)^4815 := by
    have hnat : (2543455791 : ℕ)^5839*6250000000000^4815 ≤ 2753633823681^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2543455791 5000000000 2753633823681 6250000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5487455513/10000000000 : ℝ)^5839 ≤ (24149791048297/50000000000000 : ℝ)^4815 := by
    have hnat : (5487455513 : ℕ)^5839*50000000000000^4815 ≤ 24149791048297^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487455513 10000000000 24149791048297 50000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-149963229/1250000000 : ℝ), (2543455791/5000000000 : ℝ), (5487455513/10000000000 : ℝ)] ![(7642276710759/100000000000000 : ℝ), (2753633823681/6250000000000 : ℝ), (24149791048297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-149963229/1250000000 : ℝ)|^5839 ≤ (7642276710759/100000000000000 : ℝ)^4815
        have hw : |(-149963229/1250000000 : ℝ)|=(149963229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2543455791/5000000000 : ℝ)|^5839 ≤ (2753633823681/6250000000000 : ℝ)^4815
        have hw : |(2543455791/5000000000 : ℝ)|=(2543455791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5487455513/10000000000 : ℝ)|^5839 ≤ (24149791048297/50000000000000 : ℝ)^4815
        have hw : |(5487455513/10000000000 : ℝ)|=(5487455513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s1_5 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224520373/10000000000 : ℝ)*x 0 + (-504346723/5000000000 : ℝ)*x 1 + (5487455493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224520373/10000000000 : ℝ)^5839 ≤ (4550757724737/10000000000000 : ℝ)^4815 := by
    have hnat : (5224520373 : ℕ)^5839*10000000000000^4815 ≤ 4550757724737^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224520373 10000000000 4550757724737 10000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (504346723/5000000000 : ℝ)^5839 ≤ (3096420427961/50000000000000 : ℝ)^4815 := by
    have hnat : (504346723 : ℕ)^5839*50000000000000^4815 ≤ 3096420427961^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504346723 5000000000 3096420427961 50000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5487455493/10000000000 : ℝ)^5839 ≤ (603744773539/1250000000000 : ℝ)^4815 := by
    have hnat : (5487455493 : ℕ)^5839*1250000000000^4815 ≤ 603744773539^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487455493 10000000000 603744773539 1250000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224520373/10000000000 : ℝ), (-504346723/5000000000 : ℝ), (5487455493/10000000000 : ℝ)] ![(4550757724737/10000000000000 : ℝ), (3096420427961/50000000000000 : ℝ), (603744773539/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224520373/10000000000 : ℝ)|^5839 ≤ (4550757724737/10000000000000 : ℝ)^4815
        have hw : |(5224520373/10000000000 : ℝ)|=(5224520373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-504346723/5000000000 : ℝ)|^5839 ≤ (3096420427961/50000000000000 : ℝ)^4815
        have hw : |(-504346723/5000000000 : ℝ)|=(504346723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5487455493/10000000000 : ℝ)|^5839 ≤ (603744773539/1250000000000 : ℝ)^4815
        have hw : |(5487455493/10000000000 : ℝ)|=(5487455493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s1_6 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612260123/5000000000 : ℝ)*x 0 + (5487455453/10000000000 : ℝ)*x 1 + (-504346841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612260123/5000000000 : ℝ)^5839 ≤ (45507575905893/100000000000000 : ℝ)^4815 := by
    have hnat : (2612260123 : ℕ)^5839*100000000000000^4815 ≤ 45507575905893^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612260123 5000000000 45507575905893 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5487455453/10000000000 : ℝ)^5839 ≤ (48299581456173/100000000000000 : ℝ)^4815 := by
    have hnat : (5487455453 : ℕ)^5839*100000000000000^4815 ≤ 48299581456173^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487455453 10000000000 48299581456173 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (504346841/5000000000 : ℝ)^5839 ≤ (247713704519/4000000000000 : ℝ)^4815 := by
    have hnat : (504346841 : ℕ)^5839*4000000000000^4815 ≤ 247713704519^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504346841 5000000000 247713704519 4000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612260123/5000000000 : ℝ), (5487455453/10000000000 : ℝ), (-504346841/5000000000 : ℝ)] ![(45507575905893/100000000000000 : ℝ), (48299581456173/100000000000000 : ℝ), (247713704519/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612260123/5000000000 : ℝ)|^5839 ≤ (45507575905893/100000000000000 : ℝ)^4815
        have hw : |(2612260123/5000000000 : ℝ)|=(2612260123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5487455453/10000000000 : ℝ)|^5839 ≤ (48299581456173/100000000000000 : ℝ)^4815
        have hw : |(5487455453/10000000000 : ℝ)|=(5487455453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-504346841/5000000000 : ℝ)|^5839 ≤ (247713704519/4000000000000 : ℝ)^4815
        have hw : |(-504346841/5000000000 : ℝ)|=(504346841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s1_7 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4013106757/10000000000 : ℝ)*x 0 + (4712786937/10000000000 : ℝ)*x 1 + (3375268017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4013106757/10000000000 : ℝ)^5839 ≤ (16524314755093/50000000000000 : ℝ)^4815 := by
    have hnat : (4013106757 : ℕ)^5839*50000000000000^4815 ≤ 16524314755093^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4013106757 10000000000 16524314755093 50000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4712786937/10000000000 : ℝ)^5839 ≤ (40160046542887/100000000000000 : ℝ)^4815 := by
    have hnat : (4712786937 : ℕ)^5839*100000000000000^4815 ≤ 40160046542887^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4712786937 10000000000 40160046542887 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3375268017/10000000000 : ℝ)^5839 ≤ (6697830982631/25000000000000 : ℝ)^4815 := by
    have hnat : (3375268017 : ℕ)^5839*25000000000000^4815 ≤ 6697830982631^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3375268017 10000000000 6697830982631 25000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4013106757/10000000000 : ℝ), (4712786937/10000000000 : ℝ), (3375268017/10000000000 : ℝ)] ![(16524314755093/50000000000000 : ℝ), (40160046542887/100000000000000 : ℝ), (6697830982631/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4013106757/10000000000 : ℝ)|^5839 ≤ (16524314755093/50000000000000 : ℝ)^4815
        have hw : |(4013106757/10000000000 : ℝ)|=(4013106757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4712786937/10000000000 : ℝ)|^5839 ≤ (40160046542887/100000000000000 : ℝ)^4815
        have hw : |(4712786937/10000000000 : ℝ)|=(4712786937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3375268017/10000000000 : ℝ)|^5839 ≤ (6697830982631/25000000000000 : ℝ)^4815
        have hw : |(3375268017/10000000000 : ℝ)|=(3375268017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1754_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216963139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2061/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3441/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (113/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17957/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2061/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3441/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2061/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3441/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2061/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3441/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2061/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3441/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2061/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3441/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2061/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3441/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3441/50000 : ℝ) ^ (5823/1024 : ℝ) ≤ (12291566198737/50000000000000000000 : ℝ) := by
    have hpowers : (3441/50000 : ℝ)^5823 ≤ (12291566198737/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3441 : ℕ)^5823*50000000000000000000^1024 ≤ 12291566198737^1024*50000^5823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3441 50000 12291566198737 50000000000000000000 5823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3441/50000 : ℝ)) (X := (12291566198737/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2061/10000 : ℝ) ^ (5823/1024 : ℝ) ≤ (502977334794203/4000000000000000000 : ℝ) := by
    have hpowers : (2061/10000 : ℝ)^5823 ≤ (502977334794203/4000000000000000000 : ℝ)^1024 := by
      have hnat : (2061 : ℕ)^5823*4000000000000000000^1024 ≤ 502977334794203^1024*10000^5823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2061 10000 502977334794203 4000000000000000000 5823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2061/10000 : ℝ)) (X := (502977334794203/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000012291566198737/25000000000000000000 : ℝ) ≤ (62500005403813/62500000000000 : ℝ) ^ (5823/1024 : ℝ) := by
    have hpowers : (25000012291566198737/25000000000000000000 : ℝ)^1024 ≤ (62500005403813/62500000000000 : ℝ)^5823 := by
      have hnat : (25000012291566198737 : ℕ)^1024*62500000000000^5823 ≤ 62500005403813^5823*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000012291566198737 25000000000000000000 62500005403813 62500000000000 1024 5823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62500005403813/62500000000000 : ℝ)) (X := (25000012291566198737/25000000000000000000 : ℝ)) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100012599016502252549/100000000000000000000 : ℝ) ≤ (5000110773854941/5000000000000000 : ℝ) ^ (5823/1024 : ℝ) := by
    have hpowers : (100012599016502252549/100000000000000000000 : ℝ)^1024 ≤ (5000110773854941/5000000000000000 : ℝ)^5823 := by
      have hnat : (100012599016502252549 : ℕ)^1024*5000000000000000^5823 ≤ 5000110773854941^5823*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100012599016502252549 100000000000000000000 5000110773854941 5000000000000000 1024 5823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000110773854941/5000000000000000 : ℝ)) (X := (100012599016502252549/100000000000000000000 : ℝ)) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2000502977334794203/2000000000000000000 : ℝ) ≤ (2500110557702421/2500000000000000 : ℝ) ^ (5823/1024 : ℝ) := by
    have hpowers : (2000502977334794203/2000000000000000000 : ℝ)^1024 ≤ (2500110557702421/2500000000000000 : ℝ)^5823 := by
      have hnat : (2000502977334794203 : ℕ)^1024*2500000000000000^5823 ≤ 2500110557702421^5823*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000502977334794203 2000000000000000000 2500110557702421 2500000000000000 1024 5823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500110557702421/2500000000000000 : ℝ)) (X := (2000502977334794203/2000000000000000000 : ℝ)) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12291566198737/50000000000000000000 : ℝ) ≤ ((519988539345384483/520000000000000000 : ℝ)+2*(10031049991/62400000000000 : ℝ)*(3441/50000 : ℝ))^(5823/1024 : ℝ) := by
    rw [show (519988539345384483/520000000000000000 : ℝ)+2*(10031049991/62400000000000 : ℝ)*(3441/50000 : ℝ)=(62500005403813/62500000000000 : ℝ) by norm_num, show 1+2*(12291566198737/50000000000000000000 : ℝ)=(25000012291566198737/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(502977334794203/4000000000000000000 : ℝ)+(12291566198737/50000000000000000000 : ℝ) ≤ ((519988539345384483/520000000000000000 : ℝ)+(10031049991/62400000000000 : ℝ)*((2061/10000 : ℝ)+(3441/50000 : ℝ)))^(5823/1024 : ℝ) := by
    rw [show (519988539345384483/520000000000000000 : ℝ)+(10031049991/62400000000000 : ℝ)*((2061/10000 : ℝ)+(3441/50000 : ℝ))=(5000110773854941/5000000000000000 : ℝ) by norm_num, show 1+(502977334794203/4000000000000000000 : ℝ)+(12291566198737/50000000000000000000 : ℝ)=(100012599016502252549/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(502977334794203/4000000000000000000 : ℝ) ≤ ((519988539345384483/520000000000000000 : ℝ)+2*(10031049991/62400000000000 : ℝ)*(2061/10000 : ℝ))^(5823/1024 : ℝ) := by
    rw [show (519988539345384483/520000000000000000 : ℝ)+2*(10031049991/62400000000000 : ℝ)*(2061/10000 : ℝ)=(2500110557702421/2500000000000000 : ℝ) by norm_num, show 1+2*(502977334794203/4000000000000000000 : ℝ)=(2000502977334794203/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (519988539345384483/520000000000000000 : ℝ)*(X 1 0+X 2 0)+(10031049991/62400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5823/1024 : ℝ)) (lo := (3441/50000 : ℝ)) (hi := (2061/10000 : ℝ)) (c := (519988539345384483/520000000000000000 : ℝ)) (alpha := (10031049991/62400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (519988539345384483/520000000000000000 : ℝ)*(X 0 1+X 2 1)+(10031049991/62400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5823/1024 : ℝ)) (lo := (3441/50000 : ℝ)) (hi := (2061/10000 : ℝ)) (c := (519988539345384483/520000000000000000 : ℝ)) (alpha := (10031049991/62400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (519988539345384483/520000000000000000 : ℝ)*(X 0 2+X 1 2)+(10031049991/62400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5823/1024 : ℝ)) (lo := (3441/50000 : ℝ)) (hi := (2061/10000 : ℝ)) (c := (519988539345384483/520000000000000000 : ℝ)) (alpha := (10031049991/62400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-599674827/5000000000 : ℝ)*X 0 0+(5494467741/10000000000 : ℝ)*X 0 1+(5080045411/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1066853609/2000000000 : ℝ)*X 1 0+(-88506457/625000000 : ℝ)*X 1 1+(2540022549/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5334267213/10000000000 : ℝ)*X 2 0+(5080045617/10000000000 : ℝ)*X 2 1+(-283220747/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2005959803/5000000000 : ℝ)*X 0 0+(3351851983/10000000000 : ℝ)*X 0 1+(4735717559/10000000000 : ℝ)*X 0 2+(2005959803/5000000000 : ℝ)*X 1 0+(3351851983/10000000000 : ℝ)*X 1 1+(4735717559/10000000000 : ℝ)*X 1 2+(2005959803/5000000000 : ℝ)*X 2 0+(3351851983/10000000000 : ℝ)*X 2 1+(4735717559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-149963229/1250000000 : ℝ)*X 0 0+(2543455791/5000000000 : ℝ)*X 0 1+(5487455513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5224520373/10000000000 : ℝ)*X 1 0+(-504346723/5000000000 : ℝ)*X 1 1+(5487455493/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2612260123/5000000000 : ℝ)*X 2 0+(5487455453/10000000000 : ℝ)*X 2 1+(-504346841/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4013106757/10000000000 : ℝ)*X 0 0+(4712786937/10000000000 : ℝ)*X 0 1+(3375268017/10000000000 : ℝ)*X 0 2+(4013106757/10000000000 : ℝ)*X 1 0+(4712786937/10000000000 : ℝ)*X 1 1+(3375268017/10000000000 : ℝ)*X 1 2+(4013106757/10000000000 : ℝ)*X 2 0+(4712786937/10000000000 : ℝ)*X 2 1+(3375268017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (188458367900213604438004207/13000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1044470167/50000000000000 : ℝ)*(base19) + (774151453/50000000000000 : ℝ)*(base23) + (2190671/2500000000000 : ℝ)*(lower2) + (120299171/25000000000000 : ℝ)*(upper3) + (17298537/20000000000000 : ℝ)*(upper5) + (1567824665026643/100000000000000 : ℝ)*(major0) + (1567824665026643/100000000000000 : ℝ)*(major1) + (1567824665026643/100000000000000 : ℝ)*(major2) + (603253672620267/25000000000000 : ℝ)*(sp0) + (1206512081491257/50000000000000 : ℝ)*(sp1) + (1206512351809971/50000000000000 : ℝ)*(sp2) + (90327149418879/12500000000000 : ℝ)*(sp3) + (11561441781/100000000000000 : ℝ)*(sp4) + (337472051/6250000000000 : ℝ)*(sp7) + (90327824362981/12500000000000 : ℝ)*(f.failure) + (75407070372589/3125000000000 : ℝ)*(f.sum) + (10741587129413/3120000000000000000000000000 : ℝ)*base65 + (1443017017991333293/156000000000000000000000000000000 : ℝ)*base68 + (834699445739333293/156000000000000000000000000000000 : ℝ)*base70 + (335448462072666707/156000000000000000000000000000000 : ℝ)*base71 + (4844625091387/3120000000000000000000000000 : ℝ)*base74 + (686912654015333293/156000000000000000000000000000000 : ℝ)*base76 + (85688594423333293/156000000000000000000000000000000 : ℝ)*base78 + (211562266295333293/156000000000000000000000000000000 : ℝ)*base80 + (3053970933413/3120000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4342641/1250000000000000000000 : ℝ)*base90 + (4342641/1250000000000000000000 : ℝ)*base92 + (4342641/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46787783747039199050591777/6500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1118298049/100000000000000 : ℝ)*(base19) + (9750549/800000000000 : ℝ)*(base23) + (53400923/50000000000000 : ℝ)*(upper2) + (40973481/25000000000000 : ℝ)*(upper3) + (165211297/50000000000000 : ℝ)*(upper5) + (811064615447573/50000000000000 : ℝ)*(major0) + (811064615447573/50000000000000 : ℝ)*(major1) + (811064615447573/50000000000000 : ℝ)*(major2) + (4120535933/50000000000000 : ℝ)*(sp1) + (1236773357/20000000000000 : ℝ)*(sp2) + (2496606229734977/100000000000000 : ℝ)*(sp4) + (1248298435182531/50000000000000 : ℝ)*(sp5) + (78018713345299/3125000000000 : ℝ)*(sp6) + (373825996058977/50000000000000 : ℝ)*(sp7) + (373825996058977/50000000000000 : ℝ)*(f.failure) + (2496606229734977/100000000000000 : ℝ)*(f.sum) + (6576880892003/1560000000000000000000000000 : ℝ)*base65 + (10255831947295723/78000000000000000000000000000000 : ℝ)*base68 + (132867545306704277/78000000000000000000000000000000 : ℝ)*base69 + (303611863383295723/78000000000000000000000000000000 : ℝ)*base72 + (8421060257603/1560000000000000000000000000 : ℝ)*base73 + (604904832867295723/78000000000000000000000000000000 : ℝ)*base76 + (578799282669295723/78000000000000000000000000000000 : ℝ)*base78 + (1241269150677295723/78000000000000000000000000000000 : ℝ)*base80 + (11120885469323/1560000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (20951197/5000000000000000000000 : ℝ)*base90 + (20951197/5000000000000000000000 : ℝ)*base92 + (20951197/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1754_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216963139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2061/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3441/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (113/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17957/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1754_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1754_s2_0 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1200207281/10000000000 : ℝ)*x 0 + (8786739/16000000 : ℝ)*x 1 + (1270554103/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1200207281/10000000000 : ℝ)^5839 ≤ (7646150502257/100000000000000 : ℝ)^4815 := by
    have hnat : (1200207281 : ℕ)^5839*100000000000000^4815 ≤ 7646150502257^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200207281 10000000000 7646150502257 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8786739/16000000 : ℝ)^5839 ≤ (12086254231793/25000000000000 : ℝ)^4815 := by
    have hnat : (8786739 : ℕ)^5839*25000000000000^4815 ≤ 12086254231793^4815*16000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8786739 16000000 12086254231793 25000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1270554103/2500000000 : ℝ)^5839 ≤ (22004416279337/50000000000000 : ℝ)^4815 := by
    have hnat : (1270554103 : ℕ)^5839*50000000000000^4815 ≤ 22004416279337^4815*2500000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270554103 2500000000 22004416279337 50000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1200207281/10000000000 : ℝ), (8786739/16000000 : ℝ), (1270554103/2500000000 : ℝ)] ![(7646150502257/100000000000000 : ℝ), (12086254231793/25000000000000 : ℝ), (22004416279337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1200207281/10000000000 : ℝ)|^5839 ≤ (7646150502257/100000000000000 : ℝ)^4815
        have hw : |(-1200207281/10000000000 : ℝ)|=(1200207281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8786739/16000000 : ℝ)|^5839 ≤ (12086254231793/25000000000000 : ℝ)^4815
        have hw : |(8786739/16000000 : ℝ)|=(8786739/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1270554103/2500000000 : ℝ)|^5839 ≤ (22004416279337/50000000000000 : ℝ)^4815
        have hw : |(1270554103/2500000000 : ℝ)|=(1270554103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s2_1 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (666687599/1250000000 : ℝ)*x 0 + (-282854229/2000000000 : ℝ)*x 1 + (508221637/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (666687599/1250000000 : ℝ)^5839 ≤ (46661256178553/100000000000000 : ℝ)^4815 := by
    have hnat : (666687599 : ℕ)^5839*100000000000000^4815 ≤ 46661256178553^4815*1250000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      666687599 1250000000 46661256178553 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282854229/2000000000 : ℝ)^5839 ≤ (1865982338673/20000000000000 : ℝ)^4815 := by
    have hnat : (282854229 : ℕ)^5839*20000000000000^4815 ≤ 1865982338673^4815*2000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282854229 2000000000 1865982338673 20000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508221637/1000000000 : ℝ)^5839 ≤ (44008832117633/100000000000000 : ℝ)^4815 := by
    have hnat : (508221637 : ℕ)^5839*100000000000000^4815 ≤ 44008832117633^4815*1000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508221637 1000000000 44008832117633 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(666687599/1250000000 : ℝ), (-282854229/2000000000 : ℝ), (508221637/1000000000 : ℝ)] ![(46661256178553/100000000000000 : ℝ), (1865982338673/20000000000000 : ℝ), (44008832117633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(666687599/1250000000 : ℝ)|^5839 ≤ (46661256178553/100000000000000 : ℝ)^4815
        have hw : |(666687599/1250000000 : ℝ)|=(666687599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-282854229/2000000000 : ℝ)|^5839 ≤ (1865982338673/20000000000000 : ℝ)^4815
        have hw : |(-282854229/2000000000 : ℝ)|=(282854229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(508221637/1000000000 : ℝ)|^5839 ≤ (44008832117633/100000000000000 : ℝ)^4815
        have hw : |(508221637/1000000000 : ℝ)|=(508221637/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s2_2 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1333375197/2500000000 : ℝ)*x 0 + (2541108189/5000000000 : ℝ)*x 1 + (-1414271139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1333375197/2500000000 : ℝ)^5839 ≤ (11665314034029/25000000000000 : ℝ)^4815 := by
    have hnat : (1333375197 : ℕ)^5839*25000000000000^4815 ≤ 11665314034029^4815*2500000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1333375197 2500000000 11665314034029 25000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2541108189/5000000000 : ℝ)^5839 ≤ (44008832201641/100000000000000 : ℝ)^4815 := by
    have hnat : (2541108189 : ℕ)^5839*100000000000000^4815 ≤ 44008832201641^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541108189 5000000000 44008832201641 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1414271139/10000000000 : ℝ)^5839 ≤ (4664955822683/50000000000000 : ℝ)^4815 := by
    have hnat : (1414271139 : ℕ)^5839*50000000000000^4815 ≤ 4664955822683^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414271139 10000000000 4664955822683 50000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1333375197/2500000000 : ℝ), (2541108189/5000000000 : ℝ), (-1414271139/10000000000 : ℝ)] ![(11665314034029/25000000000000 : ℝ), (44008832201641/100000000000000 : ℝ), (4664955822683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1333375197/2500000000 : ℝ)|^5839 ≤ (11665314034029/25000000000000 : ℝ)^4815
        have hw : |(1333375197/2500000000 : ℝ)|=(1333375197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2541108189/5000000000 : ℝ)|^5839 ≤ (44008832201641/100000000000000 : ℝ)^4815
        have hw : |(2541108189/5000000000 : ℝ)|=(2541108189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1414271139/10000000000 : ℝ)|^5839 ≤ (4664955822683/50000000000000 : ℝ)^4815
        have hw : |(-1414271139/10000000000 : ℝ)|=(1414271139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s2_3 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4012623521/10000000000 : ℝ)*x 0 + (3360026827/10000000000 : ℝ)*x 1 + (2363719499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4012623521/10000000000 : ℝ)^5839 ≤ (8260950929419/25000000000000 : ℝ)^4815 := by
    have hnat : (4012623521 : ℕ)^5839*25000000000000^4815 ≤ 8260950929419^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4012623521 10000000000 8260950929419 25000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3360026827/10000000000 : ℝ)^5839 ≤ (26644688761443/100000000000000 : ℝ)^4815 := by
    have hnat : (3360026827 : ℕ)^5839*100000000000000^4815 ≤ 26644688761443^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3360026827 10000000000 26644688761443 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2363719499/5000000000 : ℝ)^5839 ≤ (20155753757119/50000000000000 : ℝ)^4815 := by
    have hnat : (2363719499 : ℕ)^5839*50000000000000^4815 ≤ 20155753757119^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2363719499 5000000000 20155753757119 50000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4012623521/10000000000 : ℝ), (3360026827/10000000000 : ℝ), (2363719499/5000000000 : ℝ)] ![(8260950929419/25000000000000 : ℝ), (26644688761443/100000000000000 : ℝ), (20155753757119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4012623521/10000000000 : ℝ)|^5839 ≤ (8260950929419/25000000000000 : ℝ)^4815
        have hw : |(4012623521/10000000000 : ℝ)|=(4012623521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3360026827/10000000000 : ℝ)|^5839 ≤ (26644688761443/100000000000000 : ℝ)^4815
        have hw : |(3360026827/10000000000 : ℝ)|=(3360026827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2363719499/5000000000 : ℝ)|^5839 ≤ (20155753757119/50000000000000 : ℝ)^4815
        have hw : |(2363719499/5000000000 : ℝ)|=(2363719499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s2_4 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-600275113/5000000000 : ℝ)*x 0 + (2544460583/5000000000 : ℝ)*x 1 + (548486669/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (600275113/5000000000 : ℝ)^5839 ≤ (7648800017599/100000000000000 : ℝ)^4815 := by
    have hnat : (600275113 : ℕ)^5839*100000000000000^4815 ≤ 7648800017599^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600275113 5000000000 7648800017599 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2544460583/5000000000 : ℝ)^5839 ≤ (881584975301/2000000000000 : ℝ)^4815 := by
    have hnat : (2544460583 : ℕ)^5839*2000000000000^4815 ≤ 881584975301^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2544460583 5000000000 881584975301 2000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548486669/1000000000 : ℝ)^5839 ≤ (48271951191381/100000000000000 : ℝ)^4815 := by
    have hnat : (548486669 : ℕ)^5839*100000000000000^4815 ≤ 48271951191381^4815*1000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548486669 1000000000 48271951191381 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-600275113/5000000000 : ℝ), (2544460583/5000000000 : ℝ), (548486669/1000000000 : ℝ)] ![(7648800017599/100000000000000 : ℝ), (881584975301/2000000000000 : ℝ), (48271951191381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-600275113/5000000000 : ℝ)|^5839 ≤ (7648800017599/100000000000000 : ℝ)^4815
        have hw : |(-600275113/5000000000 : ℝ)|=(600275113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2544460583/5000000000 : ℝ)|^5839 ≤ (881584975301/2000000000000 : ℝ)^4815
        have hw : |(2544460583/5000000000 : ℝ)|=(2544460583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(548486669/1000000000 : ℝ)|^5839 ≤ (48271951191381/100000000000000 : ℝ)^4815
        have hw : |(548486669/1000000000 : ℝ)|=(548486669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s2_5 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225072113/10000000000 : ℝ)*x 0 + (-1011620989/10000000000 : ℝ)*x 1 + (548486669/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225072113/10000000000 : ℝ)^5839 ≤ (45513405237653/100000000000000 : ℝ)^4815 := by
    have hnat : (5225072113 : ℕ)^5839*100000000000000^4815 ≤ 45513405237653^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225072113 10000000000 45513405237653 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1011620989/10000000000 : ℝ)^5839 ≤ (6214643546661/100000000000000 : ℝ)^4815 := by
    have hnat : (1011620989 : ℕ)^5839*100000000000000^4815 ≤ 6214643546661^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011620989 10000000000 6214643546661 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548486669/1000000000 : ℝ)^5839 ≤ (48271951191381/100000000000000 : ℝ)^4815 := by
    have hnat : (548486669 : ℕ)^5839*100000000000000^4815 ≤ 48271951191381^4815*1000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548486669 1000000000 48271951191381 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225072113/10000000000 : ℝ), (-1011620989/10000000000 : ℝ), (548486669/1000000000 : ℝ)] ![(45513405237653/100000000000000 : ℝ), (6214643546661/100000000000000 : ℝ), (48271951191381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225072113/10000000000 : ℝ)|^5839 ≤ (45513405237653/100000000000000 : ℝ)^4815
        have hw : |(5225072113/10000000000 : ℝ)|=(5225072113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1011620989/10000000000 : ℝ)|^5839 ≤ (6214643546661/100000000000000 : ℝ)^4815
        have hw : |(-1011620989/10000000000 : ℝ)|=(1011620989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(548486669/1000000000 : ℝ)|^5839 ≤ (48271951191381/100000000000000 : ℝ)^4815
        have hw : |(548486669/1000000000 : ℝ)|=(548486669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s2_6 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225072113/10000000000 : ℝ)*x 0 + (548486669/1000000000 : ℝ)*x 1 + (-1011620989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225072113/10000000000 : ℝ)^5839 ≤ (45513405237653/100000000000000 : ℝ)^4815 := by
    have hnat : (5225072113 : ℕ)^5839*100000000000000^4815 ≤ 45513405237653^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225072113 10000000000 45513405237653 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548486669/1000000000 : ℝ)^5839 ≤ (48271951191381/100000000000000 : ℝ)^4815 := by
    have hnat : (548486669 : ℕ)^5839*100000000000000^4815 ≤ 48271951191381^4815*1000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548486669 1000000000 48271951191381 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1011620989/10000000000 : ℝ)^5839 ≤ (6214643546661/100000000000000 : ℝ)^4815 := by
    have hnat : (1011620989 : ℕ)^5839*100000000000000^4815 ≤ 6214643546661^4815*10000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011620989 10000000000 6214643546661 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225072113/10000000000 : ℝ), (548486669/1000000000 : ℝ), (-1011620989/10000000000 : ℝ)] ![(45513405237653/100000000000000 : ℝ), (48271951191381/100000000000000 : ℝ), (6214643546661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225072113/10000000000 : ℝ)|^5839 ≤ (45513405237653/100000000000000 : ℝ)^4815
        have hw : |(5225072113/10000000000 : ℝ)|=(5225072113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548486669/1000000000 : ℝ)|^5839 ≤ (48271951191381/100000000000000 : ℝ)^4815
        have hw : |(548486669/1000000000 : ℝ)|=(548486669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1011620989/10000000000 : ℝ)|^5839 ≤ (6214643546661/100000000000000 : ℝ)^4815
        have hw : |(-1011620989/10000000000 : ℝ)|=(1011620989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1754_s2_7 (p : ℝ) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2006884231/5000000000 : ℝ)*x 0 + (941010049/2000000000 : ℝ)*x 1 + (1691442047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2006884231/5000000000 : ℝ)^5839 ≤ (33055237767657/100000000000000 : ℝ)^4815 := by
    have hnat : (2006884231 : ℕ)^5839*100000000000000^4815 ≤ 33055237767657^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006884231 5000000000 33055237767657 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (941010049/2000000000 : ℝ)^5839 ≤ (8016022269449/20000000000000 : ℝ)^4815 := by
    have hnat : (941010049 : ℕ)^5839*20000000000000^4815 ≤ 8016022269449^4815*2000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941010049 2000000000 8016022269449 20000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1691442047/5000000000 : ℝ)^5839 ≤ (26864650868567/100000000000000 : ℝ)^4815 := by
    have hnat : (1691442047 : ℕ)^5839*100000000000000^4815 ≤ 26864650868567^4815*5000000000^5839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1691442047 5000000000 26864650868567 100000000000000 5839 4815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5839/1024 : ℝ)) 5839 4815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2006884231/5000000000 : ℝ), (941010049/2000000000 : ℝ), (1691442047/5000000000 : ℝ)] ![(33055237767657/100000000000000 : ℝ), (8016022269449/20000000000000 : ℝ), (26864650868567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2006884231/5000000000 : ℝ)|^5839 ≤ (33055237767657/100000000000000 : ℝ)^4815
        have hw : |(2006884231/5000000000 : ℝ)|=(2006884231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(941010049/2000000000 : ℝ)|^5839 ≤ (8016022269449/20000000000000 : ℝ)^4815
        have hw : |(941010049/2000000000 : ℝ)|=(941010049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1691442047/5000000000 : ℝ)|^5839 ≤ (26864650868567/100000000000000 : ℝ)^4815
        have hw : |(1691442047/5000000000 : ℝ)|=(1691442047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1754_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216963139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17957/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/1250 : ℝ)*pair X i i ≤ pair X i h) :
    (9089/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8949/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17957/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (113/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17957/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (113/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17957/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (113/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17957/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (113/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17957/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (113/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17957/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (113/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (113/1250 : ℝ) ^ (5823/1024 : ℝ) ≤ (23187680665851/20000000000000000000 : ℝ) := by
    have hpowers : (113/1250 : ℝ)^5823 ≤ (23187680665851/20000000000000000000 : ℝ)^1024 := by
      have hnat : (113 : ℕ)^5823*20000000000000000000^1024 ≤ 23187680665851^1024*1250^5823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113 1250 23187680665851 20000000000000000000 5823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (113/1250 : ℝ)) (X := (23187680665851/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17957/100000 : ℝ) ^ (5823/1024 : ℝ) ≤ (5743583327257827/100000000000000000000 : ℝ) := by
    have hpowers : (17957/100000 : ℝ)^5823 ≤ (5743583327257827/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17957 : ℕ)^5823*100000000000000000000^1024 ≤ 5743583327257827^1024*100000^5823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17957 100000 5743583327257827 100000000000000000000 5823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17957/100000 : ℝ)) (X := (5743583327257827/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000023187680665851/10000000000000000000 : ℝ) ≤ (10000004077651093/10000000000000000 : ℝ) ^ (5823/1024 : ℝ) := by
    have hpowers : (10000023187680665851/10000000000000000000 : ℝ)^1024 ≤ (10000004077651093/10000000000000000 : ℝ)^5823 := by
      have hnat : (10000023187680665851 : ℕ)^1024*10000000000000000^5823 ≤ 10000004077651093^5823*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000023187680665851 10000000000000000000 10000004077651093 10000000000000000 1024 5823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000004077651093/10000000000000000 : ℝ)) (X := (10000023187680665851/10000000000000000000 : ℝ)) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50002929760865293541/50000000000000000000 : ℝ) ≤ (10000103039762677/10000000000000000 : ℝ) ^ (5823/1024 : ℝ) := by
    have hpowers : (50002929760865293541/50000000000000000000 : ℝ)^1024 ≤ (10000103039762677/10000000000000000 : ℝ)^5823 := by
      have hnat : (50002929760865293541 : ℕ)^1024*10000000000000000^5823 ≤ 10000103039762677^5823*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002929760865293541 50000000000000000000 10000103039762677 10000000000000000 1024 5823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000103039762677/10000000000000000 : ℝ)) (X := (50002929760865293541/50000000000000000000 : ℝ)) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50005743583327257827/50000000000000000000 : ℝ) ≤ (10000202001874261/10000000000000000 : ℝ) ^ (5823/1024 : ℝ) := by
    have hpowers : (50005743583327257827/50000000000000000000 : ℝ)^1024 ≤ (10000202001874261/10000000000000000 : ℝ)^5823 := by
      have hnat : (50005743583327257827 : ℕ)^1024*10000000000000000^5823 ≤ 10000202001874261^5823*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005743583327257827 50000000000000000000 10000202001874261 10000000000000000 1024 5823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000202001874261/10000000000000000 : ℝ)) (X := (50005743583327257827/50000000000000000000 : ℝ)) (by norm_num) 5823 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(23187680665851/20000000000000000000 : ℝ) ≤ ((89168247125437357561/89170000000000000000 : ℝ)+2*(3092565987/27865625000000 : ℝ)*(113/1250 : ℝ))^(5823/1024 : ℝ) := by
    rw [show (89168247125437357561/89170000000000000000 : ℝ)+2*(3092565987/27865625000000 : ℝ)*(113/1250 : ℝ)=(10000004077651093/10000000000000000 : ℝ) by norm_num, show 1+2*(23187680665851/20000000000000000000 : ℝ)=(10000023187680665851/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5743583327257827/100000000000000000000 : ℝ)+(23187680665851/20000000000000000000 : ℝ) ≤ ((89168247125437357561/89170000000000000000 : ℝ)+(3092565987/27865625000000 : ℝ)*((17957/100000 : ℝ)+(113/1250 : ℝ)))^(5823/1024 : ℝ) := by
    rw [show (89168247125437357561/89170000000000000000 : ℝ)+(3092565987/27865625000000 : ℝ)*((17957/100000 : ℝ)+(113/1250 : ℝ))=(10000103039762677/10000000000000000 : ℝ) by norm_num, show 1+(5743583327257827/100000000000000000000 : ℝ)+(23187680665851/20000000000000000000 : ℝ)=(50002929760865293541/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5743583327257827/100000000000000000000 : ℝ) ≤ ((89168247125437357561/89170000000000000000 : ℝ)+2*(3092565987/27865625000000 : ℝ)*(17957/100000 : ℝ))^(5823/1024 : ℝ) := by
    rw [show (89168247125437357561/89170000000000000000 : ℝ)+2*(3092565987/27865625000000 : ℝ)*(17957/100000 : ℝ)=(10000202001874261/10000000000000000 : ℝ) by norm_num, show 1+2*(5743583327257827/100000000000000000000 : ℝ)=(50005743583327257827/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (89168247125437357561/89170000000000000000 : ℝ)*(X 1 0+X 2 0)+(3092565987/27865625000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5823/1024 : ℝ)) (lo := (113/1250 : ℝ)) (hi := (17957/100000 : ℝ)) (c := (89168247125437357561/89170000000000000000 : ℝ)) (alpha := (3092565987/27865625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (89168247125437357561/89170000000000000000 : ℝ)*(X 0 1+X 2 1)+(3092565987/27865625000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5823/1024 : ℝ)) (lo := (113/1250 : ℝ)) (hi := (17957/100000 : ℝ)) (c := (89168247125437357561/89170000000000000000 : ℝ)) (alpha := (3092565987/27865625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (89168247125437357561/89170000000000000000 : ℝ)*(X 0 2+X 1 2)+(3092565987/27865625000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5823/1024 : ℝ)) (lo := (113/1250 : ℝ)) (hi := (17957/100000 : ℝ)) (c := (89168247125437357561/89170000000000000000 : ℝ)) (alpha := (3092565987/27865625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1200207281/10000000000 : ℝ)*X 0 0+(8786739/16000000 : ℝ)*X 0 1+(1270554103/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((666687599/1250000000 : ℝ)*X 1 0+(-282854229/2000000000 : ℝ)*X 1 1+(508221637/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1333375197/2500000000 : ℝ)*X 2 0+(2541108189/5000000000 : ℝ)*X 2 1+(-1414271139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4012623521/10000000000 : ℝ)*X 0 0+(3360026827/10000000000 : ℝ)*X 0 1+(2363719499/5000000000 : ℝ)*X 0 2+(4012623521/10000000000 : ℝ)*X 1 0+(3360026827/10000000000 : ℝ)*X 1 1+(2363719499/5000000000 : ℝ)*X 1 2+(4012623521/10000000000 : ℝ)*X 2 0+(3360026827/10000000000 : ℝ)*X 2 1+(2363719499/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-600275113/5000000000 : ℝ)*X 0 0+(2544460583/5000000000 : ℝ)*X 0 1+(548486669/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5225072113/10000000000 : ℝ)*X 1 0+(-1011620989/10000000000 : ℝ)*X 1 1+(548486669/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5225072113/10000000000 : ℝ)*X 2 0+(548486669/1000000000 : ℝ)*X 2 1+(-1011620989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2006884231/5000000000 : ℝ)*X 0 0+(941010049/2000000000 : ℝ)*X 0 1+(1691442047/5000000000 : ℝ)*X 0 2+(2006884231/5000000000 : ℝ)*X 1 0+(941010049/2000000000 : ℝ)*X 1 1+(1691442047/5000000000 : ℝ)*X 1 2+(2006884231/5000000000 : ℝ)*X 2 0+(941010049/2000000000 : ℝ)*X 2 1+(1691442047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1754_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58267674124010848036629717/15062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (296589293/50000000000000 : ℝ)*(base19) + (264382663/50000000000000 : ℝ)*(base23) + (16689001/50000000000000 : ℝ)*(lower2) + (41831029/50000000000000 : ℝ)*(upper3) + (41793033/100000000000000 : ℝ)*(upper5) + (396668822573937/25000000000000 : ℝ)*(major0) + (396668822573937/25000000000000 : ℝ)*(major1) + (396668822573937/25000000000000 : ℝ)*(major2) + (2442034544490283/100000000000000 : ℝ)*(sp0) + (610509715902149/25000000000000 : ℝ)*(sp1) + (76313716500683/3125000000000 : ℝ)*(sp2) + (36565477289167/5000000000000 : ℝ)*(sp3) + (49122969/1000000000000 : ℝ)*(sp4) + (1449074523/100000000000000 : ℝ)*(sp7) + (731310994857863/100000000000000 : ℝ)*(f.failure) + (2442039456787183/100000000000000 : ℝ)*(f.sum) + (39596583895323/44585000000000000000000000000 : ℝ)*base66 + (6150796434004287657/2229250000000000000000000000000000 : ℝ)*base67 + (12174641144432212343/2229250000000000000000000000000000 : ℝ)*base70 + (8843339294257787657/2229250000000000000000000000000000 : ℝ)*base71 + (142263535753743/44585000000000000000000000000 : ℝ)*base74 + (20759114793240787657/2229250000000000000000000000000000 : ℝ)*base75 + (14387005879049787657/2229250000000000000000000000000000 : ℝ)*base77 + (9169732514271537657/2229250000000000000000000000000000 : ℝ)*base79 + (179310774409249/22292500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (15311957/10000000000000000000000 : ℝ)*base89 + (15311957/10000000000000000000000 : ℝ)*base91 + (15311957/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3527650071399110709133870083/1114625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81676183/20000000000000 : ℝ)*(base19) + (218660451/50000000000000 : ℝ)*(base23) + (5777693/5000000000000 : ℝ)*(lower1) + (2151111/3125000000000 : ℝ)*(upper3) + (3210777/25000000000000 : ℝ)*(lower4) + (16572881/25000000000000 : ℝ)*(upper5) + (820482666427199/50000000000000 : ℝ)*(major0) + (820482666427199/50000000000000 : ℝ)*(major1) + (820482666427199/50000000000000 : ℝ)*(major2) + (210115551/100000000000000 : ℝ)*(sp2) + (1262798431023757/50000000000000 : ℝ)*(sp4) + (2525596453666599/100000000000000 : ℝ)*(sp5) + (2525596214611061/100000000000000 : ℝ)*(sp6) + (378166849082691/50000000000000 : ℝ)*(sp7) + (378166849082691/50000000000000 : ℝ)*(f.failure) + (1262798431023757/50000000000000 : ℝ)*(f.sum) + (1032309213113/696640625000000000000000000 : ℝ)*base65 + (7486252942091301639/4458500000000000000000000000000000 : ℝ)*base67 + (5369166969232301639/4458500000000000000000000000000000 : ℝ)*base69 + (506790385340256801639/4458500000000000000000000000000000 : ℝ)*base71 + (170082363454283/44585000000000000000000000000 : ℝ)*base74 + (674484218641792698361/4458500000000000000000000000000000 : ℝ)*base76 + (8474797576607801639/4458500000000000000000000000000000 : ℝ)*base77 + (15257993392417301639/4458500000000000000000000000000000 : ℝ)*base79 + (113190363113859/22292500000000000000000000000 : ℝ)*base82 + (9927049/5000000000000000000000 : ℝ)*base89 + (9927049/5000000000000000000000 : ℝ)*base91 + (9927049/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1754_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216963139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17957/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9089/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8949/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1754_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1754_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216963139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9089/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8949/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1754_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1754_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1754_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5823/1024 : ℝ) ≤ p) (hpb : p ≤ (5839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216963139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9089/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8949/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1754_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
