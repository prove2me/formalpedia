-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1169_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:43:54.710696+00:00
-- url     : https://prove2.me/submissions/80889f82-3af0-4527-9e7c-e92f3f84e857

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
theorem support_rectangle_w1169_s0_0 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1883294659/10000000000 : ℝ)*x 0 + (3024055419/5000000000 : ℝ)*x 1 + (149496171/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1883294659/10000000000 : ℝ)^4181 ≤ (5479006413649/50000000000000 : ℝ)^3157 := by
    have hnat : (1883294659 : ℕ)^4181*50000000000000^3157 ≤ 5479006413649^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1883294659 10000000000 5479006413649 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3024055419/5000000000 : ℝ)^4181 ≤ (51379069353271/100000000000000 : ℝ)^3157 := by
    have hnat : (3024055419 : ℕ)^4181*100000000000000^3157 ≤ 51379069353271^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3024055419 5000000000 51379069353271 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149496171/312500000 : ℝ)^4181 ≤ (7532583560113/20000000000000 : ℝ)^3157 := by
    have hnat : (149496171 : ℕ)^4181*20000000000000^3157 ≤ 7532583560113^3157*312500000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149496171 312500000 7532583560113 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1883294659/10000000000 : ℝ), (3024055419/5000000000 : ℝ), (149496171/312500000 : ℝ)] ![(5479006413649/50000000000000 : ℝ), (51379069353271/100000000000000 : ℝ), (7532583560113/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1883294659/10000000000 : ℝ)|^4181 ≤ (5479006413649/50000000000000 : ℝ)^3157
        have hw : |(-1883294659/10000000000 : ℝ)|=(1883294659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3024055419/5000000000 : ℝ)|^4181 ≤ (51379069353271/100000000000000 : ℝ)^3157
        have hw : |(3024055419/5000000000 : ℝ)|=(3024055419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(149496171/312500000 : ℝ)|^4181 ≤ (7532583560113/20000000000000 : ℝ)^3157
        have hw : |(149496171/312500000 : ℝ)|=(149496171/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s0_1 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2757636279/5000000000 : ℝ)*x 0 + (-5216109/20000000 : ℝ)*x 1 + (4783877451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757636279/5000000000 : ℝ)^4181 ≤ (9094357257621/20000000000000 : ℝ)^3157 := by
    have hnat : (2757636279 : ℕ)^4181*20000000000000^3157 ≤ 9094357257621^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757636279 5000000000 9094357257621 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216109/20000000 : ℝ)^4181 ≤ (16865296117899/100000000000000 : ℝ)^3157 := by
    have hnat : (5216109 : ℕ)^4181*100000000000000^3157 ≤ 16865296117899^3157*20000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216109 20000000 16865296117899 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4783877451/10000000000 : ℝ)^4181 ≤ (4707864697701/12500000000000 : ℝ)^3157 := by
    have hnat : (4783877451 : ℕ)^4181*12500000000000^3157 ≤ 4707864697701^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4783877451 10000000000 4707864697701 12500000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757636279/5000000000 : ℝ), (-5216109/20000000 : ℝ), (4783877451/10000000000 : ℝ)] ![(9094357257621/20000000000000 : ℝ), (16865296117899/100000000000000 : ℝ), (4707864697701/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757636279/5000000000 : ℝ)|^4181 ≤ (9094357257621/20000000000000 : ℝ)^3157
        have hw : |(2757636279/5000000000 : ℝ)|=(2757636279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5216109/20000000 : ℝ)|^4181 ≤ (16865296117899/100000000000000 : ℝ)^3157
        have hw : |(-5216109/20000000 : ℝ)|=(5216109/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4783877451/10000000000 : ℝ)|^4181 ≤ (4707864697701/12500000000000 : ℝ)^3157
        have hw : |(4783877451/10000000000 : ℝ)|=(4783877451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s0_2 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (344704533/625000000 : ℝ)*x 0 + (149496171/312500000 : ℝ)*x 1 + (-163003407/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344704533/625000000 : ℝ)^4181 ≤ (45471785960537/100000000000000 : ℝ)^3157 := by
    have hnat : (344704533 : ℕ)^4181*100000000000000^3157 ≤ 45471785960537^3157*625000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344704533 625000000 45471785960537 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149496171/312500000 : ℝ)^4181 ≤ (7532583560113/20000000000000 : ℝ)^3157 := by
    have hnat : (149496171 : ℕ)^4181*20000000000000^3157 ≤ 7532583560113^3157*312500000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149496171 312500000 7532583560113 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163003407/625000000 : ℝ)^4181 ≤ (16865296220669/100000000000000 : ℝ)^3157 := by
    have hnat : (163003407 : ℕ)^4181*100000000000000^3157 ≤ 16865296220669^3157*625000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163003407 625000000 16865296220669 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(344704533/625000000 : ℝ), (149496171/312500000 : ℝ), (-163003407/625000000 : ℝ)] ![(45471785960537/100000000000000 : ℝ), (7532583560113/20000000000000 : ℝ), (16865296220669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(344704533/625000000 : ℝ)|^4181 ≤ (45471785960537/100000000000000 : ℝ)^3157
        have hw : |(344704533/625000000 : ℝ)|=(344704533/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(149496171/312500000 : ℝ)|^4181 ≤ (7532583560113/20000000000000 : ℝ)^3157
        have hw : |(149496171/312500000 : ℝ)|=(149496171/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-163003407/625000000 : ℝ)|^4181 ≤ (16865296220669/100000000000000 : ℝ)^3157
        have hw : |(-163003407/625000000 : ℝ)|=(163003407/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s0_3 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1049703973/2500000000 : ℝ)*x 0 + (779965119/2500000000 : ℝ)*x 1 + (176510843/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049703973/2500000000 : ℝ)^4181 ≤ (31687267577501/100000000000000 : ℝ)^3157 := by
    have hnat : (1049703973 : ℕ)^4181*100000000000000^3157 ≤ 31687267577501^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049703973 2500000000 31687267577501 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (779965119/2500000000 : ℝ)^4181 ≤ (21382258765069/100000000000000 : ℝ)^3157 := by
    have hnat : (779965119 : ℕ)^4181*100000000000000^3157 ≤ 21382258765069^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779965119 2500000000 21382258765069 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (176510843/312500000 : ℝ)^4181 ≤ (23465236822493/50000000000000 : ℝ)^3157 := by
    have hnat : (176510843 : ℕ)^4181*50000000000000^3157 ≤ 23465236822493^3157*312500000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176510843 312500000 23465236822493 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049703973/2500000000 : ℝ), (779965119/2500000000 : ℝ), (176510843/312500000 : ℝ)] ![(31687267577501/100000000000000 : ℝ), (21382258765069/100000000000000 : ℝ), (23465236822493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049703973/2500000000 : ℝ)|^4181 ≤ (31687267577501/100000000000000 : ℝ)^3157
        have hw : |(1049703973/2500000000 : ℝ)|=(1049703973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(779965119/2500000000 : ℝ)|^4181 ≤ (21382258765069/100000000000000 : ℝ)^3157
        have hw : |(779965119/2500000000 : ℝ)|=(779965119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(176510843/312500000 : ℝ)|^4181 ≤ (23465236822493/50000000000000 : ℝ)^3157
        have hw : |(176510843/312500000 : ℝ)|=(176510843/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s0_4 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1888361259/10000000000 : ℝ)*x 0 + (4816477129/10000000000 : ℝ)*x 1 + (1503590767/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1888361259/10000000000 : ℝ)^4181 ≤ (10997072182051/100000000000000 : ℝ)^3157 := by
    have hnat : (1888361259 : ℕ)^4181*100000000000000^3157 ≤ 10997072182051^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888361259 10000000000 10997072182051 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4816477129/10000000000 : ℝ)^4181 ≤ (3800319394297/10000000000000 : ℝ)^3157 := by
    have hnat : (4816477129 : ℕ)^4181*10000000000000^3157 ≤ 3800319394297^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4816477129 10000000000 3800319394297 10000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1503590767/2500000000 : ℝ)^4181 ≤ (50999733865817/100000000000000 : ℝ)^3157 := by
    have hnat : (1503590767 : ℕ)^4181*100000000000000^3157 ≤ 50999733865817^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503590767 2500000000 50999733865817 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1888361259/10000000000 : ℝ), (4816477129/10000000000 : ℝ), (1503590767/2500000000 : ℝ)] ![(10997072182051/100000000000000 : ℝ), (3800319394297/10000000000000 : ℝ), (50999733865817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1888361259/10000000000 : ℝ)|^4181 ≤ (10997072182051/100000000000000 : ℝ)^3157
        have hw : |(-1888361259/10000000000 : ℝ)|=(1888361259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4816477129/10000000000 : ℝ)|^4181 ≤ (3800319394297/10000000000000 : ℝ)^3157
        have hw : |(4816477129/10000000000 : ℝ)|=(4816477129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1503590767/2500000000 : ℝ)|^4181 ≤ (50999733865817/100000000000000 : ℝ)^3157
        have hw : |(1503590767/2500000000 : ℝ)|=(1503590767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s0_5 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (80806599/156250000 : ℝ)*x 0 + (-1377569103/10000000000 : ℝ)*x 1 + (3007181419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (80806599/156250000 : ℝ)^4181 ≤ (41757953097213/100000000000000 : ℝ)^3157 := by
    have hnat : (80806599 : ℕ)^4181*100000000000000^3157 ≤ 41757953097213^3157*156250000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80806599 156250000 41757953097213 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1377569103/10000000000 : ℝ)^4181 ≤ (7242315604203/100000000000000 : ℝ)^3157 := by
    have hnat : (1377569103 : ℕ)^4181*100000000000000^3157 ≤ 7242315604203^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377569103 10000000000 7242315604203 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3007181419/5000000000 : ℝ)^4181 ≤ (50999731282893/100000000000000 : ℝ)^3157 := by
    have hnat : (3007181419 : ℕ)^4181*100000000000000^3157 ≤ 50999731282893^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3007181419 5000000000 50999731282893 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(80806599/156250000 : ℝ), (-1377569103/10000000000 : ℝ), (3007181419/5000000000 : ℝ)] ![(41757953097213/100000000000000 : ℝ), (7242315604203/100000000000000 : ℝ), (50999731282893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(80806599/156250000 : ℝ)|^4181 ≤ (41757953097213/100000000000000 : ℝ)^3157
        have hw : |(80806599/156250000 : ℝ)|=(80806599/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1377569103/10000000000 : ℝ)|^4181 ≤ (7242315604203/100000000000000 : ℝ)^3157
        have hw : |(-1377569103/10000000000 : ℝ)|=(1377569103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3007181419/5000000000 : ℝ)|^4181 ≤ (50999731282893/100000000000000 : ℝ)^3157
        have hw : |(3007181419/5000000000 : ℝ)|=(3007181419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s0_6 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5171622299/10000000000 : ℝ)*x 0 + (6014362939/10000000000 : ℝ)*x 1 + (-1377568997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171622299/10000000000 : ℝ)^4181 ≤ (8351590540311/20000000000000 : ℝ)^3157 := by
    have hnat : (5171622299 : ℕ)^4181*20000000000000^3157 ≤ 8351590540311^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171622299 10000000000 8351590540311 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6014362939/10000000000 : ℝ)^4181 ≤ (25499866208567/50000000000000 : ℝ)^3157 := by
    have hnat : (6014362939 : ℕ)^4181*50000000000000^3157 ≤ 25499866208567^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6014362939 10000000000 25499866208567 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1377568997/10000000000 : ℝ)^4181 ≤ (7242314866171/100000000000000 : ℝ)^3157 := by
    have hnat : (1377568997 : ℕ)^4181*100000000000000^3157 ≤ 7242314866171^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377568997 10000000000 7242314866171 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171622299/10000000000 : ℝ), (6014362939/10000000000 : ℝ), (-1377568997/10000000000 : ℝ)] ![(8351590540311/20000000000000 : ℝ), (25499866208567/50000000000000 : ℝ), (7242314866171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171622299/10000000000 : ℝ)|^4181 ≤ (8351590540311/20000000000000 : ℝ)^3157
        have hw : |(5171622299/10000000000 : ℝ)|=(5171622299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6014362939/10000000000 : ℝ)|^4181 ≤ (25499866208567/50000000000000 : ℝ)^3157
        have hw : |(6014362939/10000000000 : ℝ)|=(6014362939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1377568997/10000000000 : ℝ)|^4181 ≤ (7242314866171/100000000000000 : ℝ)^3157
        have hw : |(-1377568997/10000000000 : ℝ)|=(1377568997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s0_7 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4208949353/10000000000 : ℝ)*x 0 + (5583146867/10000000000 : ℝ)*x 1 + (1593678401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4208949353/10000000000 : ℝ)^4181 ≤ (31788586649759/100000000000000 : ℝ)^3157 := by
    have hnat : (4208949353 : ℕ)^4181*100000000000000^3157 ≤ 31788586649759^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4208949353 10000000000 31788586649759 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5583146867/10000000000 : ℝ)^4181 ≤ (46214377134649/100000000000000 : ℝ)^3157 := by
    have hnat : (5583146867 : ℕ)^4181*100000000000000^3157 ≤ 46214377134649^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5583146867 10000000000 46214377134649 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1593678401/5000000000 : ℝ)^4181 ≤ (5499259049513/25000000000000 : ℝ)^3157 := by
    have hnat : (1593678401 : ℕ)^4181*25000000000000^3157 ≤ 5499259049513^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1593678401 5000000000 5499259049513 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4208949353/10000000000 : ℝ), (5583146867/10000000000 : ℝ), (1593678401/5000000000 : ℝ)] ![(31788586649759/100000000000000 : ℝ), (46214377134649/100000000000000 : ℝ), (5499259049513/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4208949353/10000000000 : ℝ)|^4181 ≤ (31788586649759/100000000000000 : ℝ)^3157
        have hw : |(4208949353/10000000000 : ℝ)|=(4208949353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5583146867/10000000000 : ℝ)|^4181 ≤ (46214377134649/100000000000000 : ℝ)^3157
        have hw : |(5583146867/10000000000 : ℝ)|=(5583146867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1593678401/5000000000 : ℝ)|^4181 ≤ (5499259049513/25000000000000 : ℝ)^3157
        have hw : |(1593678401/5000000000 : ℝ)|=(1593678401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1169_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (131/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (866/3125 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8361/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8361 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8361*1^2048 ≤ 0^2048*1^8361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8361 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8361/2048 : ℝ) ≤ (237357053624463111/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8361 ≤ (237357053624463111/10000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8361*10000000000000000000^2048 ≤ 237357053624463111^2048*5^8361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 237357053624463111 10000000000000000000 8361 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (237357053624463111/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8361 := by
      have hnat : (1 : ℕ)^2048*1^8361 ≤ 1^8361*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10237357053624463111/10000000000000000000 : ℝ) ≤ (5028812990123523/5000000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (10237357053624463111/10000000000000000000 : ℝ)^2048 ≤ (5028812990123523/5000000000000000 : ℝ)^8361 := by
      have hnat : (10237357053624463111 : ℕ)^2048*5000000000000000^8361 ≤ 5028812990123523^8361*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10237357053624463111 10000000000000000000 5028812990123523 5000000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028812990123523/5000000000000000 : ℝ)) (X := (10237357053624463111/10000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5237357053624463111/5000000000000000000 : ℝ) ≤ (2528812990123523/2500000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (5237357053624463111/5000000000000000000 : ℝ)^2048 ≤ (2528812990123523/2500000000000000 : ℝ)^8361 := by
      have hnat : (5237357053624463111 : ℕ)^2048*2500000000000000^8361 ≤ 2528812990123523^8361*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5237357053624463111 5000000000000000000 2528812990123523 2500000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2528812990123523/2500000000000000 : ℝ)) (X := (5237357053624463111/5000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(28812990123523/2000000000000000 : ℝ)*(0 : ℝ))^(8361/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(28812990123523/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(237357053624463111/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(28812990123523/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8361/2048 : ℝ) := by
    rw [show (1 : ℝ)+(28812990123523/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5028812990123523/5000000000000000 : ℝ) by norm_num, show 1+(237357053624463111/10000000000000000000 : ℝ)+(0 : ℝ)=(10237357053624463111/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(237357053624463111/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(28812990123523/2000000000000000 : ℝ)*(2/5 : ℝ))^(8361/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(28812990123523/2000000000000000 : ℝ)*(2/5 : ℝ)=(2528812990123523/2500000000000000 : ℝ) by norm_num, show 1+2*(237357053624463111/10000000000000000000 : ℝ)=(5237357053624463111/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(28812990123523/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28812990123523/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(28812990123523/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28812990123523/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(28812990123523/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28812990123523/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1883294659/10000000000 : ℝ)*X 0 0+(3024055419/5000000000 : ℝ)*X 0 1+(149496171/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2757636279/5000000000 : ℝ)*X 1 0+(-5216109/20000000 : ℝ)*X 1 1+(4783877451/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((344704533/625000000 : ℝ)*X 2 0+(149496171/312500000 : ℝ)*X 2 1+(-163003407/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1049703973/2500000000 : ℝ)*X 0 0+(779965119/2500000000 : ℝ)*X 0 1+(176510843/312500000 : ℝ)*X 0 2+(1049703973/2500000000 : ℝ)*X 1 0+(779965119/2500000000 : ℝ)*X 1 1+(176510843/312500000 : ℝ)*X 1 2+(1049703973/2500000000 : ℝ)*X 2 0+(779965119/2500000000 : ℝ)*X 2 1+(176510843/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1888361259/10000000000 : ℝ)*X 0 0+(4816477129/10000000000 : ℝ)*X 0 1+(1503590767/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((80806599/156250000 : ℝ)*X 1 0+(-1377569103/10000000000 : ℝ)*X 1 1+(3007181419/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5171622299/10000000000 : ℝ)*X 2 0+(6014362939/10000000000 : ℝ)*X 2 1+(-1377568997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4208949353/10000000000 : ℝ)*X 0 0+(5583146867/10000000000 : ℝ)*X 0 1+(1593678401/5000000000 : ℝ)*X 0 2+(4208949353/10000000000 : ℝ)*X 1 0+(5583146867/10000000000 : ℝ)*X 1 1+(1593678401/5000000000 : ℝ)*X 1 2+(4208949353/10000000000 : ℝ)*X 2 0+(5583146867/10000000000 : ℝ)*X 2 1+(1593678401/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (106148283133633327799661/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (108993/200000000000 : ℝ)*(base1) + (1318941031/100000000000000 : ℝ)*(base19) + (1225733131/100000000000000 : ℝ)*(base23) + (44452653/50000000000000 : ℝ)*(base24) + (300775231/100000000000000 : ℝ)*(upper3) + (593248966481669/100000000000000 : ℝ)*(major0) + (593248966481669/100000000000000 : ℝ)*(major1) + (593248966481669/100000000000000 : ℝ)*(major2) + (79099764269489/10000000000000 : ℝ)*(sp0) + (395499595308173/50000000000000 : ℝ)*(sp1) + (39549959745947/5000000000000 : ℝ)*(sp2) + (197747437580481/50000000000000 : ℝ)*(sp3) + (2921358987/100000000000000 : ℝ)*(sp4) + (2316834691/100000000000000 : ℝ)*(sp7) + (395497246492153/100000000000000 : ℝ)*(f.failure) + (791000509557377/100000000000000 : ℝ)*(f.sum) + (4846563200113/100000000000000000000000000000 : ℝ)*base66 + (266998405200113/200000000000000000000000000000 : ℝ)*base68 + (1067348832800113/200000000000000000000000000000 : ℝ)*base70 + (316957806199887/200000000000000000000000000000 : ℝ)*base71 + (137497375700113/100000000000000000000000000000 : ℝ)*base74 + (866989602800113/200000000000000000000000000000 : ℝ)*base76 + (236811644200113/200000000000000000000000000000 : ℝ)*base78 + (609357112600113/200000000000000000000000000000 : ℝ)*base80 + (419144156200113/100000000000000000000000000000 : ℝ)*base82 + (53355799/10000000000000000000000 : ℝ)*base89 + (53355799/10000000000000000000000 : ℝ)*base91 + (53355799/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (303530683201067292607653/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9163079/12500000000000 : ℝ)*(base1) + (756522337/50000000000000 : ℝ)*(base19) + (754001033/50000000000000 : ℝ)*(base23) + (161956849/100000000000000 : ℝ)*(upper3) + (180510003/100000000000000 : ℝ)*(upper5) + (626101566048563/100000000000000 : ℝ)*(major0) + (626101566048563/100000000000000 : ℝ)*(major1) + (626101566048563/100000000000000 : ℝ)*(major2) + (3070327387/100000000000000 : ℝ)*(sp1) + (616864377/20000000000000 : ℝ)*(sp2) + (417402068918833/50000000000000 : ℝ)*(sp4) + (417399740580487/50000000000000 : ℝ)*(sp5) + (208699868052271/25000000000000 : ℝ)*(sp6) + (417398791905667/100000000000000 : ℝ)*(sp7) + (417398865210299/100000000000000 : ℝ)*(f.failure) + (417402032266517/50000000000000 : ℝ)*(f.sum) + (103846190947449/100000000000000000000000000000 : ℝ)*base65 + (434109146047449/200000000000000000000000000000 : ℝ)*base67 + (75926857752551/200000000000000000000000000000 : ℝ)*base70 + (588267454447449/200000000000000000000000000000 : ℝ)*base71 + (210954639947449/100000000000000000000000000000 : ℝ)*base73 + (1517689949952551/200000000000000000000000000000 : ℝ)*base76 + (113248182752551/200000000000000000000000000000 : ℝ)*base78 + (668505190352551/200000000000000000000000000000 : ℝ)*base80 + (88973080047449/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (9664117/10000000000000000000000 : ℝ)*base89 + (9664117/10000000000000000000000 : ℝ)*base91 + (9664117/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1169_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (131/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (866/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1169_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1169_s1_0 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2086003511/10000000000 : ℝ)*x 0 + (1423589023/2500000000 : ℝ)*x 1 + (5007867109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086003511/10000000000 : ℝ)^4181 ≤ (1568335768607/12500000000000 : ℝ)^3157 := by
    have hnat : (2086003511 : ℕ)^4181*12500000000000^3157 ≤ 1568335768607^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086003511 10000000000 1568335768607 12500000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1423589023/2500000000 : ℝ)^4181 ≤ (4743741222191/10000000000000 : ℝ)^3157 := by
    have hnat : (1423589023 : ℕ)^4181*10000000000000^3157 ≤ 4743741222191^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1423589023 2500000000 4743741222191 10000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5007867109/10000000000 : ℝ)^4181 ≤ (40015901610539/100000000000000 : ℝ)^3157 := by
    have hnat : (5007867109 : ℕ)^4181*100000000000000^3157 ≤ 40015901610539^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5007867109 10000000000 40015901610539 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2086003511/10000000000 : ℝ), (1423589023/2500000000 : ℝ), (5007867109/10000000000 : ℝ)] ![(1568335768607/12500000000000 : ℝ), (4743741222191/10000000000000 : ℝ), (40015901610539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2086003511/10000000000 : ℝ)|^4181 ≤ (1568335768607/12500000000000 : ℝ)^3157
        have hw : |(-2086003511/10000000000 : ℝ)|=(2086003511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1423589023/2500000000 : ℝ)|^4181 ≤ (4743741222191/10000000000000 : ℝ)^3157
        have hw : |(1423589023/2500000000 : ℝ)|=(1423589023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5007867109/10000000000 : ℝ)|^4181 ≤ (40015901610539/100000000000000 : ℝ)^3157
        have hw : |(5007867109/10000000000 : ℝ)|=(5007867109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s1_1 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5417642081/10000000000 : ℝ)*x 0 + (-2455965457/10000000000 : ℝ)*x 1 + (5007866149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417642081/10000000000 : ℝ)^4181 ≤ (44408837323809/100000000000000 : ℝ)^3157 := by
    have hnat : (5417642081 : ℕ)^4181*100000000000000^3157 ≤ 44408837323809^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417642081 10000000000 44408837323809 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2455965457/10000000000 : ℝ)^4181 ≤ (1946908900769/12500000000000 : ℝ)^3157 := by
    have hnat : (2455965457 : ℕ)^4181*12500000000000^3157 ≤ 1946908900769^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2455965457 10000000000 1946908900769 12500000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5007866149/10000000000 : ℝ)^4181 ≤ (40015891451407/100000000000000 : ℝ)^3157 := by
    have hnat : (5007866149 : ℕ)^4181*100000000000000^3157 ≤ 40015891451407^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5007866149 10000000000 40015891451407 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417642081/10000000000 : ℝ), (-2455965457/10000000000 : ℝ), (5007866149/10000000000 : ℝ)] ![(44408837323809/100000000000000 : ℝ), (1946908900769/12500000000000 : ℝ), (40015891451407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417642081/10000000000 : ℝ)|^4181 ≤ (44408837323809/100000000000000 : ℝ)^3157
        have hw : |(5417642081/10000000000 : ℝ)|=(5417642081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2455965457/10000000000 : ℝ)|^4181 ≤ (1946908900769/12500000000000 : ℝ)^3157
        have hw : |(-2455965457/10000000000 : ℝ)|=(2455965457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5007866149/10000000000 : ℝ)|^4181 ≤ (40015891451407/100000000000000 : ℝ)^3157
        have hw : |(5007866149/10000000000 : ℝ)|=(5007866149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s1_2 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5417644199/10000000000 : ℝ)*x 0 + (5007864187/10000000000 : ℝ)*x 1 + (-2455965193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417644199/10000000000 : ℝ)^4181 ≤ (8881772063309/20000000000000 : ℝ)^3157 := by
    have hnat : (5417644199 : ℕ)^4181*20000000000000^3157 ≤ 8881772063309^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417644199 10000000000 8881772063309 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5007864187/10000000000 : ℝ)^4181 ≤ (20007935344341/50000000000000 : ℝ)^3157 := by
    have hnat : (5007864187 : ℕ)^4181*50000000000000^3157 ≤ 20007935344341^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5007864187 10000000000 20007935344341 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2455965193/10000000000 : ℝ)^4181 ≤ (778763449443/5000000000000 : ℝ)^3157 := by
    have hnat : (2455965193 : ℕ)^4181*5000000000000^3157 ≤ 778763449443^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2455965193 10000000000 778763449443 5000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417644199/10000000000 : ℝ), (5007864187/10000000000 : ℝ), (-2455965193/10000000000 : ℝ)] ![(8881772063309/20000000000000 : ℝ), (20007935344341/50000000000000 : ℝ), (778763449443/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417644199/10000000000 : ℝ)|^4181 ≤ (8881772063309/20000000000000 : ℝ)^3157
        have hw : |(5417644199/10000000000 : ℝ)|=(5417644199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5007864187/10000000000 : ℝ)|^4181 ≤ (20007935344341/50000000000000 : ℝ)^3157
        have hw : |(5007864187/10000000000 : ℝ)|=(5007864187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2455965193/10000000000 : ℝ)|^4181 ≤ (778763449443/5000000000000 : ℝ)^3157
        have hw : |(-2455965193/10000000000 : ℝ)|=(2455965193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s1_3 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4315143611/10000000000 : ℝ)*x 0 + (736415651/2000000000 : ℝ)*x 1 + (1011012373/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315143611/10000000000 : ℝ)^4181 ≤ (16427551652661/50000000000000 : ℝ)^3157 := by
    have hnat : (4315143611 : ℕ)^4181*50000000000000^3157 ≤ 16427551652661^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315143611 10000000000 16427551652661 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (736415651/2000000000 : ℝ)^4181 ≤ (13314399074917/50000000000000 : ℝ)^3157 := by
    have hnat : (736415651 : ℕ)^4181*50000000000000^3157 ≤ 13314399074917^3157*2000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736415651 2000000000 13314399074917 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1011012373/2000000000 : ℝ)^4181 ≤ (40516098524921/100000000000000 : ℝ)^3157 := by
    have hnat : (1011012373 : ℕ)^4181*100000000000000^3157 ≤ 40516098524921^3157*2000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011012373 2000000000 40516098524921 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315143611/10000000000 : ℝ), (736415651/2000000000 : ℝ), (1011012373/2000000000 : ℝ)] ![(16427551652661/50000000000000 : ℝ), (13314399074917/50000000000000 : ℝ), (40516098524921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315143611/10000000000 : ℝ)|^4181 ≤ (16427551652661/50000000000000 : ℝ)^3157
        have hw : |(4315143611/10000000000 : ℝ)|=(4315143611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(736415651/2000000000 : ℝ)|^4181 ≤ (13314399074917/50000000000000 : ℝ)^3157
        have hw : |(736415651/2000000000 : ℝ)|=(736415651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1011012373/2000000000 : ℝ)|^4181 ≤ (40516098524921/100000000000000 : ℝ)^3157
        have hw : |(1011012373/2000000000 : ℝ)|=(1011012373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s1_4 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-260847099/1250000000 : ℝ)*x 0 + (627143039/1250000000 : ℝ)*x 1 + (113697879/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260847099/1250000000 : ℝ)^4181 ≤ (12552846181749/100000000000000 : ℝ)^3157 := by
    have hnat : (260847099 : ℕ)^4181*100000000000000^3157 ≤ 12552846181749^3157*1250000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260847099 1250000000 12552846181749 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (627143039/1250000000 : ℝ)^4181 ≤ (40114106443727/100000000000000 : ℝ)^3157 := by
    have hnat : (627143039 : ℕ)^4181*100000000000000^3157 ≤ 40114106443727^3157*1250000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627143039 1250000000 40114106443727 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113697879/200000000 : ℝ)^4181 ≤ (47333047356427/100000000000000 : ℝ)^3157 := by
    have hnat : (113697879 : ℕ)^4181*100000000000000^3157 ≤ 47333047356427^3157*200000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113697879 200000000 47333047356427 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-260847099/1250000000 : ℝ), (627143039/1250000000 : ℝ), (113697879/200000000 : ℝ)] ![(12552846181749/100000000000000 : ℝ), (40114106443727/100000000000000 : ℝ), (47333047356427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-260847099/1250000000 : ℝ)|^4181 ≤ (12552846181749/100000000000000 : ℝ)^3157
        have hw : |(-260847099/1250000000 : ℝ)|=(260847099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(627143039/1250000000 : ℝ)|^4181 ≤ (40114106443727/100000000000000 : ℝ)^3157
        have hw : |(627143039/1250000000 : ℝ)|=(627143039/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(113697879/200000000 : ℝ)|^4181 ≤ (47333047356427/100000000000000 : ℝ)^3157
        have hw : |(113697879/200000000 : ℝ)|=(113697879/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s1_5 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5241402189/10000000000 : ℝ)*x 0 + (-1778934569/10000000000 : ℝ)*x 1 + (2842448437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5241402189/10000000000 : ℝ)^4181 ≤ (10626442156997/25000000000000 : ℝ)^3157 := by
    have hnat : (5241402189 : ℕ)^4181*25000000000000^3157 ≤ 10626442156997^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241402189 10000000000 10626442156997 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1778934569/10000000000 : ℝ)^4181 ≤ (10161151755001/100000000000000 : ℝ)^3157 := by
    have hnat : (1778934569 : ℕ)^4181*100000000000000^3157 ≤ 10161151755001^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1778934569 10000000000 10161151755001 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2842448437/5000000000 : ℝ)^4181 ≤ (23666539799329/50000000000000 : ℝ)^3157 := by
    have hnat : (2842448437 : ℕ)^4181*50000000000000^3157 ≤ 23666539799329^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2842448437 5000000000 23666539799329 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5241402189/10000000000 : ℝ), (-1778934569/10000000000 : ℝ), (2842448437/5000000000 : ℝ)] ![(10626442156997/25000000000000 : ℝ), (10161151755001/100000000000000 : ℝ), (23666539799329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5241402189/10000000000 : ℝ)|^4181 ≤ (10626442156997/25000000000000 : ℝ)^3157
        have hw : |(5241402189/10000000000 : ℝ)|=(5241402189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1778934569/10000000000 : ℝ)|^4181 ≤ (10161151755001/100000000000000 : ℝ)^3157
        have hw : |(-1778934569/10000000000 : ℝ)|=(1778934569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2842448437/5000000000 : ℝ)|^4181 ≤ (23666539799329/50000000000000 : ℝ)^3157
        have hw : |(2842448437/5000000000 : ℝ)|=(2842448437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s1_6 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5241401453/10000000000 : ℝ)*x 0 + (1421224537/2500000000 : ℝ)*x 1 + (-889466879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5241401453/10000000000 : ℝ)^4181 ≤ (42505760723317/100000000000000 : ℝ)^3157 := by
    have hnat : (5241401453 : ℕ)^4181*100000000000000^3157 ≤ 42505760723317^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241401453 10000000000 42505760723317 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1421224537/2500000000 : ℝ)^4181 ≤ (23666546823373/50000000000000 : ℝ)^3157 := by
    have hnat : (1421224537 : ℕ)^4181*50000000000000^3157 ≤ 23666546823373^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1421224537 2500000000 23666546823373 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (889466879/5000000000 : ℝ)^4181 ≤ (406445824803/4000000000000 : ℝ)^3157 := by
    have hnat : (889466879 : ℕ)^4181*4000000000000^3157 ≤ 406445824803^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889466879 5000000000 406445824803 4000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5241401453/10000000000 : ℝ), (1421224537/2500000000 : ℝ), (-889466879/5000000000 : ℝ)] ![(42505760723317/100000000000000 : ℝ), (23666546823373/50000000000000 : ℝ), (406445824803/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5241401453/10000000000 : ℝ)|^4181 ≤ (42505760723317/100000000000000 : ℝ)^3157
        have hw : |(5241401453/10000000000 : ℝ)|=(5241401453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1421224537/2500000000 : ℝ)|^4181 ≤ (23666546823373/50000000000000 : ℝ)^3157
        have hw : |(1421224537/2500000000 : ℝ)|=(1421224537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-889466879/5000000000 : ℝ)|^4181 ≤ (406445824803/4000000000000 : ℝ)^3157
        have hw : |(-889466879/5000000000 : ℝ)|=(889466879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s1_7 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (863335697/2000000000 : ℝ)*x 0 + (2518255091/5000000000 : ℝ)*x 1 + (1850497189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863335697/2000000000 : ℝ)^4181 ≤ (2054411322909/6250000000000 : ℝ)^3157 := by
    have hnat : (863335697 : ℕ)^4181*6250000000000^3157 ≤ 2054411322909^3157*2000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863335697 2000000000 2054411322909 6250000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2518255091/5000000000 : ℝ)^4181 ≤ (40319295727551/100000000000000 : ℝ)^3157 := by
    have hnat : (2518255091 : ℕ)^4181*100000000000000^3157 ≤ 40319295727551^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2518255091 5000000000 40319295727551 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1850497189/5000000000 : ℝ)^4181 ≤ (26810123088871/100000000000000 : ℝ)^3157 := by
    have hnat : (1850497189 : ℕ)^4181*100000000000000^3157 ≤ 26810123088871^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1850497189 5000000000 26810123088871 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863335697/2000000000 : ℝ), (2518255091/5000000000 : ℝ), (1850497189/5000000000 : ℝ)] ![(2054411322909/6250000000000 : ℝ), (40319295727551/100000000000000 : ℝ), (26810123088871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863335697/2000000000 : ℝ)|^4181 ≤ (2054411322909/6250000000000 : ℝ)^3157
        have hw : |(863335697/2000000000 : ℝ)|=(863335697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2518255091/5000000000 : ℝ)|^4181 ≤ (40319295727551/100000000000000 : ℝ)^3157
        have hw : |(2518255091/5000000000 : ℝ)|=(2518255091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1850497189/5000000000 : ℝ)|^4181 ≤ (26810123088871/100000000000000 : ℝ)^3157
        have hw : |(1850497189/5000000000 : ℝ)|=(1850497189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1169_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (866/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (131/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5799/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5079/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (866/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (131/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (866/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (131/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (866/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (131/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (866/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (131/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (866/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (131/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (866/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (131/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (131/25000 : ℝ) ^ (8361/2048 : ℝ) ≤ (48879351441/100000000000000000000 : ℝ) := by
    have hpowers : (131/25000 : ℝ)^8361 ≤ (48879351441/100000000000000000000 : ℝ)^2048 := by
      have hnat : (131 : ℕ)^8361*100000000000000000000^2048 ≤ 48879351441^2048*25000^8361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        131 25000 48879351441 100000000000000000000 8361 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (131/25000 : ℝ)) (X := (48879351441/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (866/3125 : ℝ) ^ (8361/2048 : ℝ) ≤ (530494267457120051/100000000000000000000 : ℝ) := by
    have hpowers : (866/3125 : ℝ)^8361 ≤ (530494267457120051/100000000000000000000 : ℝ)^2048 := by
      have hnat : (866 : ℕ)^8361*100000000000000000000^2048 ≤ 530494267457120051^2048*3125^8361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        866 3125 530494267457120051 100000000000000000000 8361 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (866/3125 : ℝ)) (X := (530494267457120051/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000048879351441/50000000000000000000 : ℝ) ≤ (1250000000299321/1250000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (50000000048879351441/50000000000000000000 : ℝ)^2048 ≤ (1250000000299321/1250000000000000 : ℝ)^8361 := by
      have hnat : (50000000048879351441 : ℕ)^2048*1250000000000000^8361 ≤ 1250000000299321^8361*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000048879351441 50000000000000000000 1250000000299321 1250000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000000299321/1250000000000000 : ℝ)) (X := (50000000048879351441/50000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25132623579084117873/25000000000000000000 : ℝ) ≤ (2002593668670857/2000000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (25132623579084117873/25000000000000000000 : ℝ)^2048 ≤ (2002593668670857/2000000000000000 : ℝ)^8361 := by
      have hnat : (25132623579084117873 : ℕ)^2048*2000000000000000^8361 ≤ 2002593668670857^8361*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25132623579084117873 25000000000000000000 2002593668670857 2000000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002593668670857/2000000000000000 : ℝ)) (X := (25132623579084117873/25000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50530494267457120051/50000000000000000000 : ℝ) ≤ (5012968342157001/5000000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (50530494267457120051/50000000000000000000 : ℝ)^2048 ≤ (5012968342157001/5000000000000000 : ℝ)^8361 := by
      have hnat : (50530494267457120051 : ℕ)^2048*5000000000000000^8361 ≤ 5012968342157001^8361*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50530494267457120051 50000000000000000000 5012968342157001 5000000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012968342157001/5000000000000000 : ℝ)) (X := (50530494267457120051/50000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(48879351441/100000000000000000000 : ℝ) ≤ ((33983301155472216421/33985000000000000000 : ℝ)+2*(12968340959717/2718800000000000 : ℝ)*(131/25000 : ℝ))^(8361/2048 : ℝ) := by
    rw [show (33983301155472216421/33985000000000000000 : ℝ)+2*(12968340959717/2718800000000000 : ℝ)*(131/25000 : ℝ)=(1250000000299321/1250000000000000 : ℝ) by norm_num, show 1+2*(48879351441/100000000000000000000 : ℝ)=(50000000048879351441/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(530494267457120051/100000000000000000000 : ℝ)+(48879351441/100000000000000000000 : ℝ) ≤ ((33983301155472216421/33985000000000000000 : ℝ)+(12968340959717/2718800000000000 : ℝ)*((866/3125 : ℝ)+(131/25000 : ℝ)))^(8361/2048 : ℝ) := by
    rw [show (33983301155472216421/33985000000000000000 : ℝ)+(12968340959717/2718800000000000 : ℝ)*((866/3125 : ℝ)+(131/25000 : ℝ))=(2002593668670857/2000000000000000 : ℝ) by norm_num, show 1+(530494267457120051/100000000000000000000 : ℝ)+(48879351441/100000000000000000000 : ℝ)=(25132623579084117873/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(530494267457120051/100000000000000000000 : ℝ) ≤ ((33983301155472216421/33985000000000000000 : ℝ)+2*(12968340959717/2718800000000000 : ℝ)*(866/3125 : ℝ))^(8361/2048 : ℝ) := by
    rw [show (33983301155472216421/33985000000000000000 : ℝ)+2*(12968340959717/2718800000000000 : ℝ)*(866/3125 : ℝ)=(5012968342157001/5000000000000000 : ℝ) by norm_num, show 1+2*(530494267457120051/100000000000000000000 : ℝ)=(50530494267457120051/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33983301155472216421/33985000000000000000 : ℝ)*(X 1 0+X 2 0)+(12968340959717/2718800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (131/25000 : ℝ)) (hi := (866/3125 : ℝ)) (c := (33983301155472216421/33985000000000000000 : ℝ)) (alpha := (12968340959717/2718800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33983301155472216421/33985000000000000000 : ℝ)*(X 0 1+X 2 1)+(12968340959717/2718800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (131/25000 : ℝ)) (hi := (866/3125 : ℝ)) (c := (33983301155472216421/33985000000000000000 : ℝ)) (alpha := (12968340959717/2718800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33983301155472216421/33985000000000000000 : ℝ)*(X 0 2+X 1 2)+(12968340959717/2718800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (131/25000 : ℝ)) (hi := (866/3125 : ℝ)) (c := (33983301155472216421/33985000000000000000 : ℝ)) (alpha := (12968340959717/2718800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2086003511/10000000000 : ℝ)*X 0 0+(1423589023/2500000000 : ℝ)*X 0 1+(5007867109/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5417642081/10000000000 : ℝ)*X 1 0+(-2455965457/10000000000 : ℝ)*X 1 1+(5007866149/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5417644199/10000000000 : ℝ)*X 2 0+(5007864187/10000000000 : ℝ)*X 2 1+(-2455965193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4315143611/10000000000 : ℝ)*X 0 0+(736415651/2000000000 : ℝ)*X 0 1+(1011012373/2000000000 : ℝ)*X 0 2+(4315143611/10000000000 : ℝ)*X 1 0+(736415651/2000000000 : ℝ)*X 1 1+(1011012373/2000000000 : ℝ)*X 1 2+(4315143611/10000000000 : ℝ)*X 2 0+(736415651/2000000000 : ℝ)*X 2 1+(1011012373/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-260847099/1250000000 : ℝ)*X 0 0+(627143039/1250000000 : ℝ)*X 0 1+(113697879/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5241402189/10000000000 : ℝ)*X 1 0+(-1778934569/10000000000 : ℝ)*X 1 1+(2842448437/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5241401453/10000000000 : ℝ)*X 2 0+(1421224537/2500000000 : ℝ)*X 2 1+(-889466879/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((863335697/2000000000 : ℝ)*X 0 0+(2518255091/5000000000 : ℝ)*X 0 1+(1850497189/5000000000 : ℝ)*X 0 2+(863335697/2000000000 : ℝ)*X 1 0+(2518255091/5000000000 : ℝ)*X 1 1+(1850497189/5000000000 : ℝ)*X 1 2+(863335697/2000000000 : ℝ)*X 2 0+(2518255091/5000000000 : ℝ)*X 2 1+(1850497189/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11358306202765507606153183593/1699250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73863459/10000000000000 : ℝ)*(base1) + (1152878461/100000000000000 : ℝ)*(base19) + (1792541273/100000000000000 : ℝ)*(base23) + (85803507/50000000000000 : ℝ)*(base37) + (43594409/50000000000000 : ℝ)*(upper3) + (1092514920953637/100000000000000 : ℝ)*(major0) + (1092514920953637/100000000000000 : ℝ)*(major1) + (1092514920953637/100000000000000 : ℝ)*(major2) + (1456689037783773/100000000000000 : ℝ)*(sp0) + (58267473209521/4000000000000 : ℝ)*(sp1) + (1456688347852133/100000000000000 : ℝ)*(sp2) + (182084642115519/25000000000000 : ℝ)*(sp3) + (1841244223/100000000000000 : ℝ)*(sp4) + (53931923/2500000000000 : ℝ)*(sp5) + (728339478703679/100000000000000 : ℝ)*(f.failure) + (728345070196703/50000000000000 : ℝ)*(f.sum) + (202445531662251/135940000000000000000000000000 : ℝ)*base66 + (1012663188830259189/485500000000000000000000000000000 : ℝ)*base68 + (125821106092759189/485500000000000000000000000000000 : ℝ)*base70 + (440716160429759189/485500000000000000000000000000000 : ℝ)*base72 + (229648574510771/135940000000000000000000000000 : ℝ)*base74 + (2555598439971759189/485500000000000000000000000000000 : ℝ)*base76 + (2481621522280759189/485500000000000000000000000000000 : ℝ)*base78 + (446403263734759189/485500000000000000000000000000000 : ℝ)*base80 + (49870316511011/135940000000000000000000000000 : ℝ)*base82 + (25019343/10000000000000000000000 : ℝ)*base90 + (25019343/10000000000000000000000 : ℝ)*base92 + (25019343/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (410698074426433748101270113/242750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1878786929/100000000000000 : ℝ)*(base19) + (635028751/25000000000000 : ℝ)*(base23) + (13989487/4000000000000 : ℝ)*(upper2) + (525928421/100000000000000 : ℝ)*(upper3) + (242923623/100000000000000 : ℝ)*(upper5) + (1123168655300657/100000000000000 : ℝ)*(major0) + (1123168655300657/100000000000000 : ℝ)*(major1) + (1123168655300657/100000000000000 : ℝ)*(major2) + (2668544549/25000000000000 : ℝ)*(sp1) + (2093940427/12500000000000 : ℝ)*(sp2) + (1497562059278853/100000000000000 : ℝ)*(sp4) + (2924901379519/195312500000 : ℝ)*(sp5) + (1497542767640433/100000000000000 : ℝ)*(sp6) + (374387597463627/50000000000000 : ℝ)*(sp7) + (374387597463627/50000000000000 : ℝ)*(f.failure) + (1497562059278853/100000000000000 : ℝ)*(f.sum) + (38280740880987/19420000000000000000000000000 : ℝ)*base65 + (3754456662028664129/485500000000000000000000000000000 : ℝ)*base68 + (1745497957557664129/485500000000000000000000000000000 : ℝ)*base70 + (88063730765664129/485500000000000000000000000000000 : ℝ)*base72 + (39362571049213/19420000000000000000000000000 : ℝ)*base74 + (1226078075730664129/485500000000000000000000000000000 : ℝ)*base76 + (877791685476835871/485500000000000000000000000000000 : ℝ)*base77 + (897076725701335871/485500000000000000000000000000000 : ℝ)*base79 + (72373077119333/19420000000000000000000000000 : ℝ)*base82 + (14019941/5000000000000000000000 : ℝ)*base89 + (14019941/5000000000000000000000 : ℝ)*base91 + (14019941/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1169_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (866/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (131/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5799/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5079/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1169_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1169_s2_0 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-534450133/2500000000 : ℝ)*x 0 + (2752875111/5000000000 : ℝ)*x 1 + (5163509837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534450133/2500000000 : ℝ)^4181 ≤ (1296093387441/10000000000000 : ℝ)^3157 := by
    have hnat : (534450133 : ℕ)^4181*10000000000000^3157 ≤ 1296093387441^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534450133 2500000000 1296093387441 10000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2752875111/5000000000 : ℝ)^4181 ≤ (5670980195461/12500000000000 : ℝ)^3157 := by
    have hnat : (2752875111 : ℕ)^4181*12500000000000^3157 ≤ 5670980195461^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752875111 5000000000 5670980195461 12500000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5163509837/10000000000 : ℝ)^4181 ≤ (41671224543849/100000000000000 : ℝ)^3157 := by
    have hnat : (5163509837 : ℕ)^4181*100000000000000^3157 ≤ 41671224543849^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5163509837 10000000000 41671224543849 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-534450133/2500000000 : ℝ), (2752875111/5000000000 : ℝ), (5163509837/10000000000 : ℝ)] ![(1296093387441/10000000000000 : ℝ), (5670980195461/12500000000000 : ℝ), (41671224543849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-534450133/2500000000 : ℝ)|^4181 ≤ (1296093387441/10000000000000 : ℝ)^3157
        have hw : |(-534450133/2500000000 : ℝ)|=(534450133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2752875111/5000000000 : ℝ)|^4181 ≤ (5670980195461/12500000000000 : ℝ)^3157
        have hw : |(2752875111/5000000000 : ℝ)|=(2752875111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5163509837/10000000000 : ℝ)|^4181 ≤ (41671224543849/100000000000000 : ℝ)^3157
        have hw : |(5163509837/10000000000 : ℝ)|=(5163509837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s2_1 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5372712877/10000000000 : ℝ)*x 0 + (-578886651/2500000000 : ℝ)*x 1 + (5163512637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372712877/10000000000 : ℝ)^4181 ≤ (21960874455079/50000000000000 : ℝ)^3157 := by
    have hnat : (5372712877 : ℕ)^4181*50000000000000^3157 ≤ 21960874455079^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372712877 10000000000 21960874455079 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (578886651/2500000000 : ℝ)^4181 ≤ (14406996600877/100000000000000 : ℝ)^3157 := by
    have hnat : (578886651 : ℕ)^4181*100000000000000^3157 ≤ 14406996600877^3157*2500000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578886651 2500000000 14406996600877 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5163512637/10000000000 : ℝ)^4181 ≤ (41671254470279/100000000000000 : ℝ)^3157 := by
    have hnat : (5163512637 : ℕ)^4181*100000000000000^3157 ≤ 41671254470279^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5163512637 10000000000 41671254470279 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372712877/10000000000 : ℝ), (-578886651/2500000000 : ℝ), (5163512637/10000000000 : ℝ)] ![(21960874455079/50000000000000 : ℝ), (14406996600877/100000000000000 : ℝ), (41671254470279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372712877/10000000000 : ℝ)|^4181 ≤ (21960874455079/50000000000000 : ℝ)^3157
        have hw : |(5372712877/10000000000 : ℝ)|=(5372712877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-578886651/2500000000 : ℝ)|^4181 ≤ (14406996600877/100000000000000 : ℝ)^3157
        have hw : |(-578886651/2500000000 : ℝ)|=(578886651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5163512637/10000000000 : ℝ)|^4181 ≤ (41671254470279/100000000000000 : ℝ)^3157
        have hw : |(5163512637/10000000000 : ℝ)|=(5163512637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s2_2 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5372713417/10000000000 : ℝ)*x 0 + (5163511727/10000000000 : ℝ)*x 1 + (-92621883/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372713417/10000000000 : ℝ)^4181 ≤ (8784350951303/20000000000000 : ℝ)^3157 := by
    have hnat : (5372713417 : ℕ)^4181*20000000000000^3157 ≤ 8784350951303^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372713417 10000000000 8784350951303 20000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5163511727/10000000000 : ℝ)^4181 ≤ (41671244744189/100000000000000 : ℝ)^3157 := by
    have hnat : (5163511727 : ℕ)^4181*100000000000000^3157 ≤ 41671244744189^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5163511727 10000000000 41671244744189 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (92621883/400000000 : ℝ)^4181 ≤ (7203500240951/50000000000000 : ℝ)^3157 := by
    have hnat : (92621883 : ℕ)^4181*50000000000000^3157 ≤ 7203500240951^3157*400000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92621883 400000000 7203500240951 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372713417/10000000000 : ℝ), (5163511727/10000000000 : ℝ), (-92621883/400000000 : ℝ)] ![(8784350951303/20000000000000 : ℝ), (41671244744189/100000000000000 : ℝ), (7203500240951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372713417/10000000000 : ℝ)|^4181 ≤ (8784350951303/20000000000000 : ℝ)^3157
        have hw : |(5372713417/10000000000 : ℝ)|=(5372713417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5163511727/10000000000 : ℝ)|^4181 ≤ (41671244744189/100000000000000 : ℝ)^3157
        have hw : |(5163511727/10000000000 : ℝ)|=(5163511727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-92621883/400000000 : ℝ)|^4181 ≤ (7203500240951/50000000000000 : ℝ)^3157
        have hw : |(-92621883/400000000 : ℝ)|=(92621883/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s2_3 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4350742583/10000000000 : ℝ)*x 0 + (2010879511/5000000000 : ℝ)*x 1 + (4706240437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350742583/10000000000 : ℝ)^4181 ≤ (33214546465741/100000000000000 : ℝ)^3157 := by
    have hnat : (4350742583 : ℕ)^4181*100000000000000^3157 ≤ 33214546465741^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350742583 10000000000 33214546465741 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010879511/5000000000 : ℝ)^4181 ≤ (7482470409891/25000000000000 : ℝ)^3157 := by
    have hnat : (2010879511 : ℕ)^4181*25000000000000^3157 ≤ 7482470409891^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010879511 5000000000 7482470409891 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4706240437/10000000000 : ℝ)^4181 ≤ (4606946484313/12500000000000 : ℝ)^3157 := by
    have hnat : (4706240437 : ℕ)^4181*12500000000000^3157 ≤ 4606946484313^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4706240437 10000000000 4606946484313 12500000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350742583/10000000000 : ℝ), (2010879511/5000000000 : ℝ), (4706240437/10000000000 : ℝ)] ![(33214546465741/100000000000000 : ℝ), (7482470409891/25000000000000 : ℝ), (4606946484313/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350742583/10000000000 : ℝ)|^4181 ≤ (33214546465741/100000000000000 : ℝ)^3157
        have hw : |(4350742583/10000000000 : ℝ)|=(4350742583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2010879511/5000000000 : ℝ)|^4181 ≤ (7482470409891/25000000000000 : ℝ)^3157
        have hw : |(2010879511/5000000000 : ℝ)|=(2010879511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4706240437/10000000000 : ℝ)|^4181 ≤ (4606946484313/12500000000000 : ℝ)^3157
        have hw : |(4706240437/10000000000 : ℝ)|=(4706240437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s2_4 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2137895257/10000000000 : ℝ)*x 0 + (2582913147/5000000000 : ℝ)*x 1 + (1100682293/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2137895257/10000000000 : ℝ)^4181 ≤ (12961694450091/100000000000000 : ℝ)^3157 := by
    have hnat : (2137895257 : ℕ)^4181*100000000000000^3157 ≤ 12961694450091^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137895257 10000000000 12961694450091 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2582913147/5000000000 : ℝ)^4181 ≤ (10423996164979/25000000000000 : ℝ)^3157 := by
    have hnat : (2582913147 : ℕ)^4181*25000000000000^3157 ≤ 10423996164979^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2582913147 5000000000 10423996164979 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100682293/2000000000 : ℝ)^4181 ≤ (5667790109479/12500000000000 : ℝ)^3157 := by
    have hnat : (1100682293 : ℕ)^4181*12500000000000^3157 ≤ 5667790109479^3157*2000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100682293 2000000000 5667790109479 12500000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2137895257/10000000000 : ℝ), (2582913147/5000000000 : ℝ), (1100682293/2000000000 : ℝ)] ![(12961694450091/100000000000000 : ℝ), (10423996164979/25000000000000 : ℝ), (5667790109479/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2137895257/10000000000 : ℝ)|^4181 ≤ (12961694450091/100000000000000 : ℝ)^3157
        have hw : |(-2137895257/10000000000 : ℝ)|=(2137895257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2582913147/5000000000 : ℝ)|^4181 ≤ (10423996164979/25000000000000 : ℝ)^3157
        have hw : |(2582913147/5000000000 : ℝ)|=(2582913147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1100682293/2000000000 : ℝ)|^4181 ≤ (5667790109479/12500000000000 : ℝ)^3157
        have hw : |(1100682293/2000000000 : ℝ)|=(1100682293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s2_5 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285722307/10000000000 : ℝ)*x 0 + (-9878233/50000000 : ℝ)*x 1 + (5503411463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285722307/10000000000 : ℝ)^4181 ≤ (21491210037399/50000000000000 : ℝ)^3157 := by
    have hnat : (5285722307 : ℕ)^4181*50000000000000^3157 ≤ 21491210037399^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285722307 10000000000 21491210037399 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9878233/50000000 : ℝ)^4181 ≤ (11675259059439/100000000000000 : ℝ)^3157 := by
    have hnat : (9878233 : ℕ)^4181*100000000000000^3157 ≤ 11675259059439^3157*50000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9878233 50000000 11675259059439 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5503411463/10000000000 : ℝ)^4181 ≤ (4534232085401/10000000000000 : ℝ)^3157 := by
    have hnat : (5503411463 : ℕ)^4181*10000000000000^3157 ≤ 4534232085401^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503411463 10000000000 4534232085401 10000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285722307/10000000000 : ℝ), (-9878233/50000000 : ℝ), (5503411463/10000000000 : ℝ)] ![(21491210037399/50000000000000 : ℝ), (11675259059439/100000000000000 : ℝ), (4534232085401/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285722307/10000000000 : ℝ)|^4181 ≤ (21491210037399/50000000000000 : ℝ)^3157
        have hw : |(5285722307/10000000000 : ℝ)|=(5285722307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9878233/50000000 : ℝ)|^4181 ≤ (11675259059439/100000000000000 : ℝ)^3157
        have hw : |(-9878233/50000000 : ℝ)|=(9878233/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5503411463/10000000000 : ℝ)|^4181 ≤ (4534232085401/10000000000000 : ℝ)^3157
        have hw : |(5503411463/10000000000 : ℝ)|=(5503411463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s2_6 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285722437/10000000000 : ℝ)*x 0 + (5503411459/10000000000 : ℝ)*x 1 + (-987823213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285722437/10000000000 : ℝ)^4181 ≤ (21491210737411/50000000000000 : ℝ)^3157 := by
    have hnat : (5285722437 : ℕ)^4181*50000000000000^3157 ≤ 21491210737411^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285722437 10000000000 21491210737411 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5503411459/10000000000 : ℝ)^4181 ≤ (11335580202591/25000000000000 : ℝ)^3157 := by
    have hnat : (5503411459 : ℕ)^4181*25000000000000^3157 ≤ 11335580202591^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503411459 10000000000 11335580202591 25000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (987823213/5000000000 : ℝ)^4181 ≤ (11675257697643/100000000000000 : ℝ)^3157 := by
    have hnat : (987823213 : ℕ)^4181*100000000000000^3157 ≤ 11675257697643^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987823213 5000000000 11675257697643 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285722437/10000000000 : ℝ), (5503411459/10000000000 : ℝ), (-987823213/5000000000 : ℝ)] ![(21491210737411/50000000000000 : ℝ), (11335580202591/25000000000000 : ℝ), (11675257697643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285722437/10000000000 : ℝ)|^4181 ≤ (21491210737411/50000000000000 : ℝ)^3157
        have hw : |(5285722437/10000000000 : ℝ)|=(5285722437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5503411459/10000000000 : ℝ)|^4181 ≤ (11335580202591/25000000000000 : ℝ)^3157
        have hw : |(5503411459/10000000000 : ℝ)|=(5503411459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-987823213/5000000000 : ℝ)|^4181 ≤ (11675257697643/100000000000000 : ℝ)^3157
        have hw : |(-987823213/5000000000 : ℝ)|=(987823213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1169_s2_7 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2175466837/5000000000 : ℝ)*x 0 + (4701609951/10000000000 : ℝ)*x 1 + (4026434001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175466837/5000000000 : ℝ)^4181 ≤ (33216478495673/100000000000000 : ℝ)^3157 := by
    have hnat : (2175466837 : ℕ)^4181*100000000000000^3157 ≤ 33216478495673^3157*5000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175466837 5000000000 33216478495673 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4701609951/10000000000 : ℝ)^4181 ≤ (36807555221567/100000000000000 : ℝ)^3157 := by
    have hnat : (4701609951 : ℕ)^4181*100000000000000^3157 ≤ 36807555221567^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4701609951 10000000000 36807555221567 100000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4026434001/10000000000 : ℝ)^4181 ≤ (14987983131811/50000000000000 : ℝ)^3157 := by
    have hnat : (4026434001 : ℕ)^4181*50000000000000^3157 ≤ 14987983131811^3157*10000000000^4181 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026434001 10000000000 14987983131811 50000000000000 4181 3157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4181/1024 : ℝ)) 4181 3157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175466837/5000000000 : ℝ), (4701609951/10000000000 : ℝ), (4026434001/10000000000 : ℝ)] ![(33216478495673/100000000000000 : ℝ), (36807555221567/100000000000000 : ℝ), (14987983131811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175466837/5000000000 : ℝ)|^4181 ≤ (33216478495673/100000000000000 : ℝ)^3157
        have hw : |(2175466837/5000000000 : ℝ)|=(2175466837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4701609951/10000000000 : ℝ)|^4181 ≤ (36807555221567/100000000000000 : ℝ)^3157
        have hw : |(4701609951/10000000000 : ℝ)|=(4701609951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4026434001/10000000000 : ℝ)|^4181 ≤ (14987983131811/50000000000000 : ℝ)^3157
        have hw : |(4026434001/10000000000 : ℝ)|=(4026434001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1169_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5079/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5799/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9191/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16423/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5079/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5799/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5079/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5799/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5079/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5799/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5079/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5799/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5079/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5799/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5079/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5799/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (5799/100000 : ℝ) ^ (8361/2048 : ℝ) ≤ (447028196736501/50000000000000000000 : ℝ) := by
    have hpowers : (5799/100000 : ℝ)^8361 ≤ (447028196736501/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5799 : ℕ)^8361*50000000000000000000^2048 ≤ 447028196736501^2048*100000^8361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5799 100000 447028196736501 50000000000000000000 8361 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5799/100000 : ℝ)) (X := (447028196736501/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5079/25000 : ℝ) ^ (8361/2048 : ℝ) ≤ (149360565651415763/100000000000000000000 : ℝ) := by
    have hpowers : (5079/25000 : ℝ)^8361 ≤ (149360565651415763/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5079 : ℕ)^8361*100000000000000000000^2048 ≤ 149360565651415763^2048*25000^8361 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5079 25000 149360565651415763 100000000000000000000 8361 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5079/25000 : ℝ)) (X := (149360565651415763/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000447028196736501/25000000000000000000 : ℝ) ≤ (5000021899475343/5000000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (25000447028196736501/25000000000000000000 : ℝ)^2048 ≤ (5000021899475343/5000000000000000 : ℝ)^8361 := by
      have hnat : (25000447028196736501 : ℕ)^2048*5000000000000000^8361 ≤ 5000021899475343^8361*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000447028196736501 25000000000000000000 5000021899475343 5000000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000021899475343/5000000000000000 : ℝ)) (X := (25000447028196736501/25000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20030050924408977753/20000000000000000000 : ℝ) ≤ (10003678352635577/10000000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (20030050924408977753/20000000000000000000 : ℝ)^2048 ≤ (10003678352635577/10000000000000000 : ℝ)^8361 := by
      have hnat : (20030050924408977753 : ℕ)^2048*10000000000000000^8361 ≤ 10003678352635577^8361*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20030050924408977753 20000000000000000000 10003678352635577 10000000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003678352635577/10000000000000000 : ℝ)) (X := (20030050924408977753/20000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50149360565651415763/50000000000000000000 : ℝ) ≤ (2501828226580117/2500000000000000 : ℝ) ^ (8361/2048 : ℝ) := by
    have hpowers : (50149360565651415763/50000000000000000000 : ℝ)^2048 ≤ (2501828226580117/2500000000000000 : ℝ)^8361 := by
      have hnat : (50149360565651415763 : ℕ)^2048*2500000000000000^8361 ≤ 2501828226580117^8361*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50149360565651415763 50000000000000000000 2501828226580117 2500000000000000 2048 8361 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501828226580117/2500000000000000 : ℝ)) (X := (50149360565651415763/50000000000000000000 : ℝ)) (by norm_num) 8361 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(447028196736501/50000000000000000000 : ℝ) ≤ ((12094040189644145237/12097500000000000000 : ℝ)+2*(3634553684891/1451700000000000 : ℝ)*(5799/100000 : ℝ))^(8361/2048 : ℝ) := by
    rw [show (12094040189644145237/12097500000000000000 : ℝ)+2*(3634553684891/1451700000000000 : ℝ)*(5799/100000 : ℝ)=(5000021899475343/5000000000000000 : ℝ) by norm_num, show 1+2*(447028196736501/50000000000000000000 : ℝ)=(25000447028196736501/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(149360565651415763/100000000000000000000 : ℝ)+(447028196736501/50000000000000000000 : ℝ) ≤ ((12094040189644145237/12097500000000000000 : ℝ)+(3634553684891/1451700000000000 : ℝ)*((5079/25000 : ℝ)+(5799/100000 : ℝ)))^(8361/2048 : ℝ) := by
    rw [show (12094040189644145237/12097500000000000000 : ℝ)+(3634553684891/1451700000000000 : ℝ)*((5079/25000 : ℝ)+(5799/100000 : ℝ))=(10003678352635577/10000000000000000 : ℝ) by norm_num, show 1+(149360565651415763/100000000000000000000 : ℝ)+(447028196736501/50000000000000000000 : ℝ)=(20030050924408977753/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(149360565651415763/100000000000000000000 : ℝ) ≤ ((12094040189644145237/12097500000000000000 : ℝ)+2*(3634553684891/1451700000000000 : ℝ)*(5079/25000 : ℝ))^(8361/2048 : ℝ) := by
    rw [show (12094040189644145237/12097500000000000000 : ℝ)+2*(3634553684891/1451700000000000 : ℝ)*(5079/25000 : ℝ)=(2501828226580117/2500000000000000 : ℝ) by norm_num, show 1+2*(149360565651415763/100000000000000000000 : ℝ)=(50149360565651415763/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12094040189644145237/12097500000000000000 : ℝ)*(X 1 0+X 2 0)+(3634553684891/1451700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (5799/100000 : ℝ)) (hi := (5079/25000 : ℝ)) (c := (12094040189644145237/12097500000000000000 : ℝ)) (alpha := (3634553684891/1451700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12094040189644145237/12097500000000000000 : ℝ)*(X 0 1+X 2 1)+(3634553684891/1451700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (5799/100000 : ℝ)) (hi := (5079/25000 : ℝ)) (c := (12094040189644145237/12097500000000000000 : ℝ)) (alpha := (3634553684891/1451700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12094040189644145237/12097500000000000000 : ℝ)*(X 0 2+X 1 2)+(3634553684891/1451700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8361/2048 : ℝ)) (lo := (5799/100000 : ℝ)) (hi := (5079/25000 : ℝ)) (c := (12094040189644145237/12097500000000000000 : ℝ)) (alpha := (3634553684891/1451700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-534450133/2500000000 : ℝ)*X 0 0+(2752875111/5000000000 : ℝ)*X 0 1+(5163509837/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5372712877/10000000000 : ℝ)*X 1 0+(-578886651/2500000000 : ℝ)*X 1 1+(5163512637/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5372713417/10000000000 : ℝ)*X 2 0+(5163511727/10000000000 : ℝ)*X 2 1+(-92621883/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350742583/10000000000 : ℝ)*X 0 0+(2010879511/5000000000 : ℝ)*X 0 1+(4706240437/10000000000 : ℝ)*X 0 2+(4350742583/10000000000 : ℝ)*X 1 0+(2010879511/5000000000 : ℝ)*X 1 1+(4706240437/10000000000 : ℝ)*X 1 2+(4350742583/10000000000 : ℝ)*X 2 0+(2010879511/5000000000 : ℝ)*X 2 1+(4706240437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2137895257/10000000000 : ℝ)*X 0 0+(2582913147/5000000000 : ℝ)*X 0 1+(1100682293/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5285722307/10000000000 : ℝ)*X 1 0+(-9878233/50000000 : ℝ)*X 1 1+(5503411463/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5285722437/10000000000 : ℝ)*X 2 0+(5503411459/10000000000 : ℝ)*X 2 1+(-987823213/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2175466837/5000000000 : ℝ)*X 0 0+(4701609951/10000000000 : ℝ)*X 0 1+(4026434001/10000000000 : ℝ)*X 0 2+(2175466837/5000000000 : ℝ)*X 1 0+(4701609951/10000000000 : ℝ)*X 1 1+(4026434001/10000000000 : ℝ)*X 1 2+(2175466837/5000000000 : ℝ)*X 2 0+(4701609951/10000000000 : ℝ)*X 2 1+(4026434001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1169_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (158559275754990078983867237/60487500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16551211/12500000000000 : ℝ)*(base15) + (97476353/100000000000000 : ℝ)*(upper2) + (99646609/50000000000000 : ℝ)*(upper3) + (84685781/50000000000000 : ℝ)*(upper4) + (438292551131333/20000000000000 : ℝ)*(major0) + (438292551131333/20000000000000 : ℝ)*(major1) + (438292551131333/20000000000000 : ℝ)*(major2) + (730485421081051/25000000000000 : ℝ)*(sp0) + (2921957747337907/100000000000000 : ℝ)*(sp1) + (2921955049482717/100000000000000 : ℝ)*(sp2) + (365240708541977/25000000000000 : ℝ)*(sp3) + (16195423391/100000000000000 : ℝ)*(sp4) + (1415132439/50000000000000 : ℝ)*(sp6) + (588752411/12500000000000 : ℝ)*(sp7) + (365241886046799/25000000000000 : ℝ)*(f.failure) + (584391575949519/20000000000000 : ℝ)*(f.sum) + (4383362174183/7258500000000000000000000000 : ℝ)*base65 + (845441105692707763/725850000000000000000000000000000 : ℝ)*base67 + (1838068170307857763/725850000000000000000000000000000 : ℝ)*base69 + (6361144908630057763/725850000000000000000000000000000 : ℝ)*base71 + (20795719956091/14517000000000000000000000000 : ℝ)*base73 + (4907878801258742237/725850000000000000000000000000000 : ℝ)*base76 + (2424095867279457763/725850000000000000000000000000000 : ℝ)*base77 + (612920125351557763/725850000000000000000000000000000 : ℝ)*base79 + (33265072892213/7258500000000000000000000000 : ℝ)*base81 + (356383/2500000000000000000000 : ℝ)*base90 + (356383/2500000000000000000000 : ℝ)*base92 + (356383/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15205196282985676932981511/9451171875000000000000000000000 : ℝ) := by norm_num
    linear_combination (133255019/25000000000000 : ℝ)*(base19) + (359306477/50000000000000 : ℝ)*(base23) + (35104187/100000000000000 : ℝ)*(upper2) + (2348299/3125000000000 : ℝ)*(upper3) + (62503/156250000000 : ℝ)*(upper5) + (69426728931227/3125000000000 : ℝ)*(major0) + (69426728931227/3125000000000 : ℝ)*(major1) + (69426728931227/3125000000000 : ℝ)*(major2) + (4823175999/100000000000000 : ℝ)*(sp1) + (3818979557/50000000000000 : ℝ)*(sp2) + (5785575739763/195312500000 : ℝ)*(sp4) + (1481104711281291/50000000000000 : ℝ)*(sp5) + (740551605546647/25000000000000 : ℝ)*(sp6) + (1481095819212667/100000000000000 : ℝ)*(sp7) + (1481095819212667/100000000000000 : ℝ)*(f.failure) + (5785575739763/195312500000 : ℝ)*(f.sum) + (66588664450943/36292500000000000000000000000 : ℝ)*base66 + (269169267123904169/226828125000000000000000000000000 : ℝ)*base67 + (1759974241672064581/226828125000000000000000000000000 : ℝ)*base70 + (1528183717937939581/226828125000000000000000000000000 : ℝ)*base72 + (247849153936439/72585000000000000000000000000 : ℝ)*base73 + (883036347390040103/113414062500000000000000000000000 : ℝ)*base76 + (359402322917008853/113414062500000000000000000000000 : ℝ)*base78 + (750965608805122919/226828125000000000000000000000000 : ℝ)*base79 + (305313430375741/72585000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (93518261/10000000000000000000000 : ℝ)*base89 + (93518261/10000000000000000000000 : ℝ)*base91 + (93518261/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1169_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5079/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5799/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9191/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16423/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1169_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1169_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9191/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16423/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1169_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1169_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1169_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150000783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9191/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16423/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1169_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
