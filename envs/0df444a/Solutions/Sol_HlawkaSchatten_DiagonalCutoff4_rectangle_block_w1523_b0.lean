-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1523_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:58:21.943301+00:00
-- url     : https://prove2.me/submissions/6ba643d1-70a8-4b79-ad8d-962e3f67eefd

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
theorem support_rectangle_w1523_s0_0 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1674229279/10000000000 : ℝ)*x 0 + (5904409327/10000000000 : ℝ)*x 1 + (2429997099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1674229279/10000000000 : ℝ)^4543 ≤ (1990588405861/20000000000000 : ℝ)^3519 := by
    have hnat : (1674229279 : ℕ)^4543*20000000000000^3519 ≤ 1990588405861^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674229279 10000000000 1990588405861 20000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5904409327/10000000000 : ℝ)^4543 ≤ (50651311219177/100000000000000 : ℝ)^3519 := by
    have hnat : (5904409327 : ℕ)^4543*100000000000000^3519 ≤ 50651311219177^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5904409327 10000000000 50651311219177 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2429997099/5000000000 : ℝ)^4543 ≤ (7879149344771/20000000000000 : ℝ)^3519 := by
    have hnat : (2429997099 : ℕ)^4543*20000000000000^3519 ≤ 7879149344771^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2429997099 5000000000 7879149344771 20000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1674229279/10000000000 : ℝ), (5904409327/10000000000 : ℝ), (2429997099/5000000000 : ℝ)] ![(1990588405861/20000000000000 : ℝ), (50651311219177/100000000000000 : ℝ), (7879149344771/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1674229279/10000000000 : ℝ)|^4543 ≤ (1990588405861/20000000000000 : ℝ)^3519
        have hw : |(-1674229279/10000000000 : ℝ)|=(1674229279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5904409327/10000000000 : ℝ)|^4543 ≤ (50651311219177/100000000000000 : ℝ)^3519
        have hw : |(5904409327/10000000000 : ℝ)|=(5904409327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2429997099/5000000000 : ℝ)|^4543 ≤ (7879149344771/20000000000000 : ℝ)^3519
        have hw : |(2429997099/5000000000 : ℝ)|=(2429997099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s0_1 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2737795179/5000000000 : ℝ)*x 0 + (-2258819909/10000000000 : ℝ)*x 1 + (242999711/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2737795179/5000000000 : ℝ)^4543 ≤ (11488319913419/25000000000000 : ℝ)^3519 := by
    have hnat : (2737795179 : ℕ)^4543*25000000000000^3519 ≤ 11488319913419^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737795179 5000000000 11488319913419 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2258819909/10000000000 : ℝ)^4543 ≤ (14650973376619/100000000000000 : ℝ)^3519 := by
    have hnat : (2258819909 : ℕ)^4543*100000000000000^3519 ≤ 14650973376619^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258819909 10000000000 14650973376619 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (242999711/500000000 : ℝ)^4543 ≤ (9848936738521/25000000000000 : ℝ)^3519 := by
    have hnat : (242999711 : ℕ)^4543*25000000000000^3519 ≤ 9848936738521^3519*500000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242999711 500000000 9848936738521 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2737795179/5000000000 : ℝ), (-2258819909/10000000000 : ℝ), (242999711/500000000 : ℝ)] ![(11488319913419/25000000000000 : ℝ), (14650973376619/100000000000000 : ℝ), (9848936738521/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2737795179/5000000000 : ℝ)|^4543 ≤ (11488319913419/25000000000000 : ℝ)^3519
        have hw : |(2737795179/5000000000 : ℝ)|=(2737795179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2258819909/10000000000 : ℝ)|^4543 ≤ (14650973376619/100000000000000 : ℝ)^3519
        have hw : |(-2258819909/10000000000 : ℝ)|=(2258819909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(242999711/500000000 : ℝ)|^4543 ≤ (9848936738521/25000000000000 : ℝ)^3519
        have hw : |(242999711/500000000 : ℝ)|=(242999711/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s0_2 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1095118069/2000000000 : ℝ)*x 0 + (4859994213/10000000000 : ℝ)*x 1 + (-451763987/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1095118069/2000000000 : ℝ)^4543 ≤ (11488319878207/25000000000000 : ℝ)^3519 := by
    have hnat : (1095118069 : ℕ)^4543*25000000000000^3519 ≤ 11488319878207^3519*2000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095118069 2000000000 11488319878207 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4859994213/10000000000 : ℝ)^4543 ≤ (39395746880829/100000000000000 : ℝ)^3519 := by
    have hnat : (4859994213 : ℕ)^4543*100000000000000^3519 ≤ 39395746880829^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4859994213 10000000000 39395746880829 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451763987/2000000000 : ℝ)^4543 ≤ (1465097359433/10000000000000 : ℝ)^3519 := by
    have hnat : (451763987 : ℕ)^4543*10000000000000^3519 ≤ 1465097359433^3519*2000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451763987 2000000000 1465097359433 10000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1095118069/2000000000 : ℝ), (4859994213/10000000000 : ℝ), (-451763987/2000000000 : ℝ)] ![(11488319878207/25000000000000 : ℝ), (39395746880829/100000000000000 : ℝ), (1465097359433/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1095118069/2000000000 : ℝ)|^4543 ≤ (11488319878207/25000000000000 : ℝ)^3519
        have hw : |(1095118069/2000000000 : ℝ)|=(1095118069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4859994213/10000000000 : ℝ)|^4543 ≤ (39395746880829/100000000000000 : ℝ)^3519
        have hw : |(4859994213/10000000000 : ℝ)|=(4859994213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-451763987/2000000000 : ℝ)|^4543 ≤ (1465097359433/10000000000000 : ℝ)^3519
        have hw : |(-451763987/2000000000 : ℝ)|=(451763987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s0_3 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2071095323/5000000000 : ℝ)*x 0 + (3091412317/10000000000 : ℝ)*x 1 + (2739040593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2071095323/5000000000 : ℝ)^4543 ≤ (16025706942441/50000000000000 : ℝ)^3519 := by
    have hnat : (2071095323 : ℕ)^4543*50000000000000^3519 ≤ 16025706942441^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071095323 5000000000 16025706942441 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091412317/10000000000 : ℝ)^4543 ≤ (2746039721581/12500000000000 : ℝ)^3519 := by
    have hnat : (3091412317 : ℕ)^4543*12500000000000^3519 ≤ 2746039721581^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091412317 10000000000 2746039721581 12500000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2739040593/5000000000 : ℝ)^4543 ≤ (45980268325419/100000000000000 : ℝ)^3519 := by
    have hnat : (2739040593 : ℕ)^4543*100000000000000^3519 ≤ 45980268325419^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739040593 5000000000 45980268325419 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2071095323/5000000000 : ℝ), (3091412317/10000000000 : ℝ), (2739040593/5000000000 : ℝ)] ![(16025706942441/50000000000000 : ℝ), (2746039721581/12500000000000 : ℝ), (45980268325419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2071095323/5000000000 : ℝ)|^4543 ≤ (16025706942441/50000000000000 : ℝ)^3519
        have hw : |(2071095323/5000000000 : ℝ)|=(2071095323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091412317/10000000000 : ℝ)|^4543 ≤ (2746039721581/12500000000000 : ℝ)^3519
        have hw : |(3091412317/10000000000 : ℝ)|=(3091412317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2739040593/5000000000 : ℝ)|^4543 ≤ (45980268325419/100000000000000 : ℝ)^3519
        have hw : |(2739040593/5000000000 : ℝ)|=(2739040593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s0_4 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-838828457/5000000000 : ℝ)*x 0 + (195463111/400000000 : ℝ)*x 1 + (5876875059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838828457/5000000000 : ℝ)^4543 ≤ (9979255847107/100000000000000 : ℝ)^3519 := by
    have hnat : (838828457 : ℕ)^4543*100000000000000^3519 ≤ 9979255847107^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838828457 5000000000 9979255847107 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195463111/400000000 : ℝ)^4543 ≤ (793483271557/2000000000000 : ℝ)^3519 := by
    have hnat : (195463111 : ℕ)^4543*2000000000000^3519 ≤ 793483271557^3519*400000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195463111 400000000 793483271557 2000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5876875059/10000000000 : ℝ)^4543 ≤ (12586645140709/25000000000000 : ℝ)^3519 := by
    have hnat : (5876875059 : ℕ)^4543*25000000000000^3519 ≤ 12586645140709^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5876875059 10000000000 12586645140709 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-838828457/5000000000 : ℝ), (195463111/400000000 : ℝ), (5876875059/10000000000 : ℝ)] ![(9979255847107/100000000000000 : ℝ), (793483271557/2000000000000 : ℝ), (12586645140709/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-838828457/5000000000 : ℝ)|^4543 ≤ (9979255847107/100000000000000 : ℝ)^3519
        have hw : |(-838828457/5000000000 : ℝ)|=(838828457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(195463111/400000000 : ℝ)|^4543 ≤ (793483271557/2000000000000 : ℝ)^3519
        have hw : |(195463111/400000000 : ℝ)|=(195463111/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5876875059/10000000000 : ℝ)|^4543 ≤ (12586645140709/25000000000000 : ℝ)^3519
        have hw : |(5876875059/10000000000 : ℝ)|=(5876875059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s0_5 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5190198231/10000000000 : ℝ)*x 0 + (-620969593/5000000000 : ℝ)*x 1 + (5876875107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5190198231/10000000000 : ℝ)^4543 ≤ (42884941360419/100000000000000 : ℝ)^3519 := by
    have hnat : (5190198231 : ℕ)^4543*100000000000000^3519 ≤ 42884941360419^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190198231 10000000000 42884941360419 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (620969593/5000000000 : ℝ)^4543 ≤ (846059692039/12500000000000 : ℝ)^3519 := by
    have hnat : (620969593 : ℕ)^4543*12500000000000^3519 ≤ 846059692039^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620969593 5000000000 846059692039 12500000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5876875107/10000000000 : ℝ)^4543 ≤ (25173290546853/50000000000000 : ℝ)^3519 := by
    have hnat : (5876875107 : ℕ)^4543*50000000000000^3519 ≤ 25173290546853^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5876875107 10000000000 25173290546853 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5190198231/10000000000 : ℝ), (-620969593/5000000000 : ℝ), (5876875107/10000000000 : ℝ)] ![(42884941360419/100000000000000 : ℝ), (846059692039/12500000000000 : ℝ), (25173290546853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5190198231/10000000000 : ℝ)|^4543 ≤ (42884941360419/100000000000000 : ℝ)^3519
        have hw : |(5190198231/10000000000 : ℝ)|=(5190198231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-620969593/5000000000 : ℝ)|^4543 ≤ (846059692039/12500000000000 : ℝ)^3519
        have hw : |(-620969593/5000000000 : ℝ)|=(620969593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5876875107/10000000000 : ℝ)|^4543 ≤ (25173290546853/50000000000000 : ℝ)^3519
        have hw : |(5876875107/10000000000 : ℝ)|=(5876875107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s0_6 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2595099093/5000000000 : ℝ)*x 0 + (2938437647/5000000000 : ℝ)*x 1 + (-1241938959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2595099093/5000000000 : ℝ)^4543 ≤ (21442470440201/50000000000000 : ℝ)^3519 := by
    have hnat : (2595099093 : ℕ)^4543*50000000000000^3519 ≤ 21442470440201^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595099093 5000000000 21442470440201 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2938437647/5000000000 : ℝ)^4543 ≤ (50346583161887/100000000000000 : ℝ)^3519 := by
    have hnat : (2938437647 : ℕ)^4543*100000000000000^3519 ≤ 50346583161887^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2938437647 5000000000 50346583161887 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1241938959/10000000000 : ℝ)^4543 ≤ (6768475939183/100000000000000 : ℝ)^3519 := by
    have hnat : (1241938959 : ℕ)^4543*100000000000000^3519 ≤ 6768475939183^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1241938959 10000000000 6768475939183 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2595099093/5000000000 : ℝ), (2938437647/5000000000 : ℝ), (-1241938959/10000000000 : ℝ)] ![(21442470440201/50000000000000 : ℝ), (50346583161887/100000000000000 : ℝ), (6768475939183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2595099093/5000000000 : ℝ)|^4543 ≤ (21442470440201/50000000000000 : ℝ)^3519
        have hw : |(2595099093/5000000000 : ℝ)|=(2595099093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2938437647/5000000000 : ℝ)|^4543 ≤ (50346583161887/100000000000000 : ℝ)^3519
        have hw : |(2938437647/5000000000 : ℝ)|=(2938437647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1241938959/10000000000 : ℝ)|^4543 ≤ (6768475939183/100000000000000 : ℝ)^3519
        have hw : |(-1241938959/10000000000 : ℝ)|=(1241938959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s0_7 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (129688211/312500000 : ℝ)*x 0 + (2708666539/5000000000 : ℝ)*x 1 + (49286447/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129688211/312500000 : ℝ)^4543 ≤ (6425934730079/20000000000000 : ℝ)^3519 := by
    have hnat : (129688211 : ℕ)^4543*20000000000000^3519 ≤ 6425934730079^3519*312500000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129688211 312500000 6425934730079 20000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708666539/5000000000 : ℝ)^4543 ≤ (566538380871/1250000000000 : ℝ)^3519 := by
    have hnat : (2708666539 : ℕ)^4543*1250000000000^3519 ≤ 566538380871^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708666539 5000000000 566538380871 1250000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49286447/156250000 : ℝ)^4543 ≤ (5636813967149/25000000000000 : ℝ)^3519 := by
    have hnat : (49286447 : ℕ)^4543*25000000000000^3519 ≤ 5636813967149^3519*156250000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49286447 156250000 5636813967149 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129688211/312500000 : ℝ), (2708666539/5000000000 : ℝ), (49286447/156250000 : ℝ)] ![(6425934730079/20000000000000 : ℝ), (566538380871/1250000000000 : ℝ), (5636813967149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129688211/312500000 : ℝ)|^4543 ≤ (6425934730079/20000000000000 : ℝ)^3519
        have hw : |(129688211/312500000 : ℝ)|=(129688211/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708666539/5000000000 : ℝ)|^4543 ≤ (566538380871/1250000000000 : ℝ)^3519
        have hw : |(2708666539/5000000000 : ℝ)|=(2708666539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(49286447/156250000 : ℝ)|^4543 ≤ (5636813967149/25000000000000 : ℝ)^3519
        have hw : |(49286447/156250000 : ℝ)|=(49286447/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1523_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41064659/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (371/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12671/50000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4541/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4541 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4541*1^1024 ≤ 0^1024*1^4541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4541 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4541/1024 : ℝ) ≤ (429780849593337889/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4541 ≤ (429780849593337889/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4541*25000000000000000000^1024 ≤ 429780849593337889^1024*5^4541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 429780849593337889 25000000000000000000 4541 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (429780849593337889/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4541/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4541 := by
      have hnat : (1 : ℕ)^1024*1^4541 ≤ 1^4541*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25429780849593337889/25000000000000000000 : ℝ) ≤ (10038510916958029/10000000000000000 : ℝ) ^ (4541/1024 : ℝ) := by
    have hpowers : (25429780849593337889/25000000000000000000 : ℝ)^1024 ≤ (10038510916958029/10000000000000000 : ℝ)^4541 := by
      have hnat : (25429780849593337889 : ℕ)^1024*10000000000000000^4541 ≤ 10038510916958029^4541*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25429780849593337889 25000000000000000000 10038510916958029 10000000000000000 1024 4541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10038510916958029/10000000000000000 : ℝ)) (X := (25429780849593337889/25000000000000000000 : ℝ)) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12929780849593337889/12500000000000000000 : ℝ) ≤ (5038510916958029/5000000000000000 : ℝ) ^ (4541/1024 : ℝ) := by
    have hpowers : (12929780849593337889/12500000000000000000 : ℝ)^1024 ≤ (5038510916958029/5000000000000000 : ℝ)^4541 := by
      have hnat : (12929780849593337889 : ℕ)^1024*5000000000000000^4541 ≤ 5038510916958029^4541*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12929780849593337889 12500000000000000000 5038510916958029 5000000000000000 1024 4541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5038510916958029/5000000000000000 : ℝ)) (X := (12929780849593337889/12500000000000000000 : ℝ)) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(38510916958029/4000000000000000 : ℝ)*(0 : ℝ))^(4541/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(38510916958029/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(429780849593337889/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(38510916958029/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4541/1024 : ℝ) := by
    rw [show (1 : ℝ)+(38510916958029/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10038510916958029/10000000000000000 : ℝ) by norm_num, show 1+(429780849593337889/25000000000000000000 : ℝ)+(0 : ℝ)=(25429780849593337889/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(429780849593337889/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(38510916958029/4000000000000000 : ℝ)*(2/5 : ℝ))^(4541/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(38510916958029/4000000000000000 : ℝ)*(2/5 : ℝ)=(5038510916958029/5000000000000000 : ℝ) by norm_num, show 1+2*(429780849593337889/25000000000000000000 : ℝ)=(12929780849593337889/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(38510916958029/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4541/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (38510916958029/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(38510916958029/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4541/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (38510916958029/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(38510916958029/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4541/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (38510916958029/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1674229279/10000000000 : ℝ)*X 0 0+(5904409327/10000000000 : ℝ)*X 0 1+(2429997099/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2737795179/5000000000 : ℝ)*X 1 0+(-2258819909/10000000000 : ℝ)*X 1 1+(242999711/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1095118069/2000000000 : ℝ)*X 2 0+(4859994213/10000000000 : ℝ)*X 2 1+(-451763987/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2071095323/5000000000 : ℝ)*X 0 0+(3091412317/10000000000 : ℝ)*X 0 1+(2739040593/5000000000 : ℝ)*X 0 2+(2071095323/5000000000 : ℝ)*X 1 0+(3091412317/10000000000 : ℝ)*X 1 1+(2739040593/5000000000 : ℝ)*X 1 2+(2071095323/5000000000 : ℝ)*X 2 0+(3091412317/10000000000 : ℝ)*X 2 1+(2739040593/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-838828457/5000000000 : ℝ)*X 0 0+(195463111/400000000 : ℝ)*X 0 1+(5876875059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5190198231/10000000000 : ℝ)*X 1 0+(-620969593/5000000000 : ℝ)*X 1 1+(5876875107/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2595099093/5000000000 : ℝ)*X 2 0+(2938437647/5000000000 : ℝ)*X 2 1+(-1241938959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((129688211/312500000 : ℝ)*X 0 0+(2708666539/5000000000 : ℝ)*X 0 1+(49286447/156250000 : ℝ)*X 0 2+(129688211/312500000 : ℝ)*X 1 0+(2708666539/5000000000 : ℝ)*X 1 1+(49286447/156250000 : ℝ)*X 1 2+(129688211/312500000 : ℝ)*X 2 0+(2708666539/5000000000 : ℝ)*X 2 1+(49286447/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (256929779964472057741713/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51924119/100000000000000 : ℝ)*(base1) + (1111021831/100000000000000 : ℝ)*(base19) + (1108748607/100000000000000 : ℝ)*(base23) + (29281593/20000000000000 : ℝ)*(upper3) + (1106709/800000000000 : ℝ)*(upper5) + (688239504913399/100000000000000 : ℝ)*(major0) + (688239504913399/100000000000000 : ℝ)*(major1) + (688239504913399/100000000000000 : ℝ)*(major2) + (957477486550689/100000000000000 : ℝ)*(sp0) + (478740136120511/50000000000000 : ℝ)*(sp1) + (478740137257123/50000000000000 : ℝ)*(sp2) + (83799131852769/20000000000000 : ℝ)*(sp3) + (1974318141/50000000000000 : ℝ)*(sp4) + (109005591/6250000000000 : ℝ)*(sp7) + (20949872763871/5000000000000 : ℝ)*(f.failure) + (239370345815713/25000000000000 : ℝ)*(f.sum) + (37152202130571/200000000000000000000000000000 : ℝ)*base65 + (673309151669429/400000000000000000000000000000 : ℝ)*base68 + (2121381628469429/400000000000000000000000000000 : ℝ)*base70 + (1516608900469429/400000000000000000000000000000 : ℝ)*base72 + (304283324269429/200000000000000000000000000000 : ℝ)*base74 + (1739661540469429/400000000000000000000000000000 : ℝ)*base76 + (1455524498069429/400000000000000000000000000000 : ℝ)*base78 + (2503848969669429/400000000000000000000000000000 : ℝ)*base80 + (484785318869429/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1384989/125000000000000000000 : ℝ)*base89 + (1384989/125000000000000000000 : ℝ)*base91 + (1384989/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (316053100510492310911497/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28816999/10000000000000 : ℝ)*(base19) + (37692123/10000000000000 : ℝ)*(base23) + (98629363/100000000000000 : ℝ)*(base39) + (34825999/100000000000000 : ℝ)*(upper3) + (89730987/100000000000000 : ℝ)*(upper5) + (362922102584897/50000000000000 : ℝ)*(major0) + (362922102584897/50000000000000 : ℝ)*(major1) + (725844106540431/100000000000000 : ℝ)*(major2) + (109202949/12500000000000 : ℝ)*(sp1) + (443236609/50000000000000 : ℝ)*(sp2) + (126224651598589/12500000000000 : ℝ)*(sp4) + (100979605099513/10000000000000 : ℝ)*(sp5) + (252449012005907/25000000000000 : ℝ)*(sp6) + (441891046245991/100000000000000 : ℝ)*(sp7) + (441891046245991/100000000000000 : ℝ)*(f.failure) + (252449327854519/25000000000000 : ℝ)*(f.sum) + (7177498018139/16000000000000000000000000000 : ℝ)*base66 + (547316820629501/400000000000000000000000000000 : ℝ)*base68 + (1292231251088013/200000000000000000000000000000 : ℝ)*base69 + (18339370499/400000000000000000000000000000 : ℝ)*base71 + (23409506434139/16000000000000000000000000000 : ℝ)*base74 + (839964622688013/200000000000000000000000000000 : ℝ)*base75 + (420028291711987/200000000000000000000000000000 : ℝ)*base78 + (779771914511987/200000000000000000000000000000 : ℝ)*base80 + (232967913688013/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (532069/2500000000000000000000 : ℝ)*base89 + (532069/2500000000000000000000 : ℝ)*base91 + (532069/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1523_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41064659/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (371/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12671/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1523_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1523_s1_0 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-228126357/1250000000 : ℝ)*x 0 + (1390824353/2500000000 : ℝ)*x 1 + (5104147571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (228126357/1250000000 : ℝ)^4543 ≤ (5562497015829/50000000000000 : ℝ)^3519 := by
    have hnat : (228126357 : ℕ)^4543*50000000000000^3519 ≤ 5562497015829^3519*1250000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228126357 1250000000 5562497015829 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1390824353/2500000000 : ℝ)^4543 ≤ (46905748362367/100000000000000 : ℝ)^3519 := by
    have hnat : (1390824353 : ℕ)^4543*100000000000000^3519 ≤ 46905748362367^3519*2500000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390824353 2500000000 46905748362367 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5104147571/10000000000 : ℝ)^4543 ≤ (5246157198587/12500000000000 : ℝ)^3519 := by
    have hnat : (5104147571 : ℕ)^4543*12500000000000^3519 ≤ 5246157198587^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5104147571 10000000000 5246157198587 12500000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-228126357/1250000000 : ℝ), (1390824353/2500000000 : ℝ), (5104147571/10000000000 : ℝ)] ![(5562497015829/50000000000000 : ℝ), (46905748362367/100000000000000 : ℝ), (5246157198587/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-228126357/1250000000 : ℝ)|^4543 ≤ (5562497015829/50000000000000 : ℝ)^3519
        have hw : |(-228126357/1250000000 : ℝ)|=(228126357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1390824353/2500000000 : ℝ)|^4543 ≤ (46905748362367/100000000000000 : ℝ)^3519
        have hw : |(1390824353/2500000000 : ℝ)|=(1390824353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5104147571/10000000000 : ℝ)|^4543 ≤ (5246157198587/12500000000000 : ℝ)^3519
        have hw : |(5104147571/10000000000 : ℝ)|=(5104147571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s1_1 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5384628353/10000000000 : ℝ)*x 0 + (-1033228243/5000000000 : ℝ)*x 1 + (2552074297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5384628353/10000000000 : ℝ)^4543 ≤ (22485071454757/50000000000000 : ℝ)^3519 := by
    have hnat : (5384628353 : ℕ)^4543*50000000000000^3519 ≤ 22485071454757^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384628353 10000000000 22485071454757 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033228243/5000000000 : ℝ)^4543 ≤ (653029431777/5000000000000 : ℝ)^3519 := by
    have hnat : (1033228243 : ℕ)^4543*5000000000000^3519 ≤ 653029431777^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033228243 5000000000 653029431777 5000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2552074297/5000000000 : ℝ)^4543 ≤ (41969268448129/100000000000000 : ℝ)^3519 := by
    have hnat : (2552074297 : ℕ)^4543*100000000000000^3519 ≤ 41969268448129^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2552074297 5000000000 41969268448129 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5384628353/10000000000 : ℝ), (-1033228243/5000000000 : ℝ), (2552074297/5000000000 : ℝ)] ![(22485071454757/50000000000000 : ℝ), (653029431777/5000000000000 : ℝ), (41969268448129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5384628353/10000000000 : ℝ)|^4543 ≤ (22485071454757/50000000000000 : ℝ)^3519
        have hw : |(5384628353/10000000000 : ℝ)|=(5384628353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1033228243/5000000000 : ℝ)|^4543 ≤ (653029431777/5000000000000 : ℝ)^3519
        have hw : |(-1033228243/5000000000 : ℝ)|=(1033228243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2552074297/5000000000 : ℝ)|^4543 ≤ (41969268448129/100000000000000 : ℝ)^3519
        have hw : |(2552074297/5000000000 : ℝ)|=(2552074297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s1_2 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692315221/5000000000 : ℝ)*x 0 + (2552073367/5000000000 : ℝ)*x 1 + (-129153509/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692315221/5000000000 : ℝ)^4543 ≤ (22485082716367/50000000000000 : ℝ)^3519 := by
    have hnat : (2692315221 : ℕ)^4543*50000000000000^3519 ≤ 22485082716367^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692315221 5000000000 22485082716367 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2552073367/5000000000 : ℝ)^4543 ≤ (8393849740741/20000000000000 : ℝ)^3519 := by
    have hnat : (2552073367 : ℕ)^4543*20000000000000^3519 ≤ 8393849740741^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2552073367 5000000000 8393849740741 20000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129153509/625000000 : ℝ)^4543 ≤ (6530292922507/50000000000000 : ℝ)^3519 := by
    have hnat : (129153509 : ℕ)^4543*50000000000000^3519 ≤ 6530292922507^3519*625000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129153509 625000000 6530292922507 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692315221/5000000000 : ℝ), (2552073367/5000000000 : ℝ), (-129153509/625000000 : ℝ)] ![(22485082716367/50000000000000 : ℝ), (8393849740741/20000000000000 : ℝ), (6530292922507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692315221/5000000000 : ℝ)|^4543 ≤ (22485082716367/50000000000000 : ℝ)^3519
        have hw : |(2692315221/5000000000 : ℝ)|=(2692315221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2552073367/5000000000 : ℝ)|^4543 ≤ (8393849740741/20000000000000 : ℝ)^3519
        have hw : |(2552073367/5000000000 : ℝ)|=(2552073367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-129153509/625000000 : ℝ)|^4543 ≤ (6530292922507/50000000000000 : ℝ)^3519
        have hw : |(-129153509/625000000 : ℝ)|=(129153509/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s1_3 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4245598837/10000000000 : ℝ)*x 0 + (937026839/2500000000 : ℝ)*x 1 + (4797344023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4245598837/10000000000 : ℝ)^4543 ≤ (8272033157421/25000000000000 : ℝ)^3519 := by
    have hnat : (4245598837 : ℕ)^4543*25000000000000^3519 ≤ 8272033157421^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245598837 10000000000 8272033157421 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (937026839/2500000000 : ℝ)^4543 ≤ (14085258981741/50000000000000 : ℝ)^3519 := by
    have hnat : (937026839 : ℕ)^4543*50000000000000^3519 ≤ 14085258981741^3519*2500000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937026839 2500000000 14085258981741 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4797344023/10000000000 : ℝ)^4543 ≤ (9685337347121/25000000000000 : ℝ)^3519 := by
    have hnat : (4797344023 : ℕ)^4543*25000000000000^3519 ≤ 9685337347121^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4797344023 10000000000 9685337347121 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4245598837/10000000000 : ℝ), (937026839/2500000000 : ℝ), (4797344023/10000000000 : ℝ)] ![(8272033157421/25000000000000 : ℝ), (14085258981741/50000000000000 : ℝ), (9685337347121/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4245598837/10000000000 : ℝ)|^4543 ≤ (8272033157421/25000000000000 : ℝ)^3519
        have hw : |(4245598837/10000000000 : ℝ)|=(4245598837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(937026839/2500000000 : ℝ)|^4543 ≤ (14085258981741/50000000000000 : ℝ)^3519
        have hw : |(937026839/2500000000 : ℝ)|=(937026839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4797344023/10000000000 : ℝ)|^4543 ≤ (9685337347121/25000000000000 : ℝ)^3519
        have hw : |(4797344023/10000000000 : ℝ)|=(4797344023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s1_4 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1825292689/10000000000 : ℝ)*x 0 + (5109203539/10000000000 : ℝ)*x 1 + (1389540357/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1825292689/10000000000 : ℝ)^4543 ≤ (2781803005187/25000000000000 : ℝ)^3519 := by
    have hnat : (1825292689 : ℕ)^4543*25000000000000^3519 ≤ 2781803005187^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1825292689 10000000000 2781803005187 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5109203539/10000000000 : ℝ)^4543 ≤ (10505733961991/25000000000000 : ℝ)^3519 := by
    have hnat : (5109203539 : ℕ)^4543*25000000000000^3519 ≤ 10505733961991^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5109203539 10000000000 10505733961991 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1389540357/2500000000 : ℝ)^4543 ≤ (1873994085011/4000000000000 : ℝ)^3519 := by
    have hnat : (1389540357 : ℕ)^4543*4000000000000^3519 ≤ 1873994085011^3519*2500000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389540357 2500000000 1873994085011 4000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1825292689/10000000000 : ℝ), (5109203539/10000000000 : ℝ), (1389540357/2500000000 : ℝ)] ![(2781803005187/25000000000000 : ℝ), (10505733961991/25000000000000 : ℝ), (1873994085011/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1825292689/10000000000 : ℝ)|^4543 ≤ (2781803005187/25000000000000 : ℝ)^3519
        have hw : |(-1825292689/10000000000 : ℝ)|=(1825292689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5109203539/10000000000 : ℝ)|^4543 ≤ (10505733961991/25000000000000 : ℝ)^3519
        have hw : |(5109203539/10000000000 : ℝ)|=(5109203539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1389540357/2500000000 : ℝ)|^4543 ≤ (1873994085011/4000000000000 : ℝ)^3519
        have hw : |(1389540357/2500000000 : ℝ)|=(1389540357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s1_5 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5263535433/10000000000 : ℝ)*x 0 + (-322488317/2000000000 : ℝ)*x 1 + (222326463/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5263535433/10000000000 : ℝ)^4543 ≤ (43668835921519/100000000000000 : ℝ)^3519 := by
    have hnat : (5263535433 : ℕ)^4543*100000000000000^3519 ≤ 43668835921519^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263535433 10000000000 43668835921519 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (322488317/2000000000 : ℝ)^4543 ≤ (1896262069367/20000000000000 : ℝ)^3519 := by
    have hnat : (322488317 : ℕ)^4543*20000000000000^3519 ≤ 1896262069367^3519*2000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322488317 2000000000 1896262069367 20000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222326463/400000000 : ℝ)^4543 ≤ (46849853724899/100000000000000 : ℝ)^3519 := by
    have hnat : (222326463 : ℕ)^4543*100000000000000^3519 ≤ 46849853724899^3519*400000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222326463 400000000 46849853724899 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5263535433/10000000000 : ℝ), (-322488317/2000000000 : ℝ), (222326463/400000000 : ℝ)] ![(43668835921519/100000000000000 : ℝ), (1896262069367/20000000000000 : ℝ), (46849853724899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5263535433/10000000000 : ℝ)|^4543 ≤ (43668835921519/100000000000000 : ℝ)^3519
        have hw : |(5263535433/10000000000 : ℝ)|=(5263535433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-322488317/2000000000 : ℝ)|^4543 ≤ (1896262069367/20000000000000 : ℝ)^3519
        have hw : |(-322488317/2000000000 : ℝ)|=(322488317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(222326463/400000000 : ℝ)|^4543 ≤ (46849853724899/100000000000000 : ℝ)^3519
        have hw : |(222326463/400000000 : ℝ)|=(222326463/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s1_6 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5263535129/10000000000 : ℝ)*x 0 + (2779080873/5000000000 : ℝ)*x 1 + (-201555221/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5263535129/10000000000 : ℝ)^4543 ≤ (10917208166367/25000000000000 : ℝ)^3519 := by
    have hnat : (5263535129 : ℕ)^4543*25000000000000^3519 ≤ 10917208166367^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263535129 10000000000 10917208166367 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2779080873/5000000000 : ℝ)^4543 ≤ (23424927792843/50000000000000 : ℝ)^3519 := by
    have hnat : (2779080873 : ℕ)^4543*50000000000000^3519 ≤ 23424927792843^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2779080873 5000000000 23424927792843 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201555221/1250000000 : ℝ)^4543 ≤ (592581983501/6250000000000 : ℝ)^3519 := by
    have hnat : (201555221 : ℕ)^4543*6250000000000^3519 ≤ 592581983501^3519*1250000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201555221 1250000000 592581983501 6250000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5263535129/10000000000 : ℝ), (2779080873/5000000000 : ℝ), (-201555221/1250000000 : ℝ)] ![(10917208166367/25000000000000 : ℝ), (23424927792843/50000000000000 : ℝ), (592581983501/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5263535129/10000000000 : ℝ)|^4543 ≤ (10917208166367/25000000000000 : ℝ)^3519
        have hw : |(5263535129/10000000000 : ℝ)|=(5263535129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2779080873/5000000000 : ℝ)|^4543 ≤ (23424927792843/50000000000000 : ℝ)^3519
        have hw : |(2779080873/5000000000 : ℝ)|=(2779080873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-201555221/1250000000 : ℝ)|^4543 ≤ (592581983501/6250000000000 : ℝ)^3519
        have hw : |(-201555221/1250000000 : ℝ)|=(201555221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s1_7 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (169849753/400000000 : ℝ)*x 0 + (47857903/100000000 : ℝ)*x 1 + (30078743/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (169849753/400000000 : ℝ)^4543 ≤ (33094622230833/100000000000000 : ℝ)^3519 := by
    have hnat : (169849753 : ℕ)^4543*100000000000000^3519 ≤ 33094622230833^3519*400000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169849753 400000000 33094622230833 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47857903/100000000 : ℝ)^4543 ≤ (482761726927/1250000000000 : ℝ)^3519 := by
    have hnat : (47857903 : ℕ)^4543*1250000000000^3519 ≤ 482761726927^3519*100000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47857903 100000000 482761726927 1250000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30078743/80000000 : ℝ)^4543 ≤ (14142219802653/50000000000000 : ℝ)^3519 := by
    have hnat : (30078743 : ℕ)^4543*50000000000000^3519 ≤ 14142219802653^3519*80000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30078743 80000000 14142219802653 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(169849753/400000000 : ℝ), (47857903/100000000 : ℝ), (30078743/80000000 : ℝ)] ![(33094622230833/100000000000000 : ℝ), (482761726927/1250000000000 : ℝ), (14142219802653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(169849753/400000000 : ℝ)|^4543 ≤ (33094622230833/100000000000000 : ℝ)^3519
        have hw : |(169849753/400000000 : ℝ)|=(169849753/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(47857903/100000000 : ℝ)|^4543 ≤ (482761726927/1250000000000 : ℝ)^3519
        have hw : |(47857903/100000000 : ℝ)|=(47857903/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(30078743/80000000 : ℝ)|^4543 ≤ (14142219802653/50000000000000 : ℝ)^3519
        have hw : |(30078743/80000000 : ℝ)|=(30078743/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1523_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41064659/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12671/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (371/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (8501/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3643/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12671/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (371/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12671/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (371/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12671/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (371/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12671/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (371/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12671/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (371/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12671/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (371/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (371/12500 : ℝ) ^ (4541/1024 : ℝ) ≤ (525876503029/3125000000000000000 : ℝ) := by
    have hpowers : (371/12500 : ℝ)^4541 ≤ (525876503029/3125000000000000000 : ℝ)^1024 := by
      have hnat : (371 : ℕ)^4541*3125000000000000000^1024 ≤ 525876503029^1024*12500^4541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        371 12500 525876503029 3125000000000000000 4541 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (371/12500 : ℝ)) (X := (525876503029/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12671/50000 : ℝ) ^ (4541/1024 : ℝ) ≤ (227138364376879279/100000000000000000000 : ℝ) := by
    have hpowers : (12671/50000 : ℝ)^4541 ≤ (227138364376879279/100000000000000000000 : ℝ)^1024 := by
      have hnat : (12671 : ℕ)^4541*100000000000000000000^1024 ≤ 227138364376879279^1024*50000^4541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12671 50000 227138364376879279 100000000000000000000 4541 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12671/50000 : ℝ)) (X := (227138364376879279/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562500525876503029/1562500000000000000 : ℝ) ≤ (5000000379474103/5000000000000000 : ℝ) ^ (4541/1024 : ℝ) := by
    have hpowers : (1562500525876503029/1562500000000000000 : ℝ)^1024 ≤ (5000000379474103/5000000000000000 : ℝ)^4541 := by
      have hnat : (1562500525876503029 : ℕ)^1024*5000000000000000^4541 ≤ 5000000379474103^4541*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562500525876503029 1562500000000000000 5000000379474103 5000000000000000 1024 4541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000379474103/5000000000000000 : ℝ)) (X := (1562500525876503029/1562500000000000000 : ℝ)) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100227155192424976207/100000000000000000000 : ℝ) ≤ (2501279468053013/2500000000000000 : ℝ) ^ (4541/1024 : ℝ) := by
    have hpowers : (100227155192424976207/100000000000000000000 : ℝ)^1024 ≤ (2501279468053013/2500000000000000 : ℝ)^4541 := by
      have hnat : (100227155192424976207 : ℕ)^1024*2500000000000000^4541 ≤ 2501279468053013^4541*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100227155192424976207 100000000000000000000 2501279468053013 2500000000000000 1024 4541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501279468053013/2500000000000000 : ℝ)) (X := (100227155192424976207/100000000000000000000 : ℝ)) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50227138364376879279/50000000000000000000 : ℝ) ≤ (5005117492737949/5000000000000000 : ℝ) ^ (4541/1024 : ℝ) := by
    have hpowers : (50227138364376879279/50000000000000000000 : ℝ)^1024 ≤ (5005117492737949/5000000000000000 : ℝ)^4541 := by
      have hnat : (50227138364376879279 : ℕ)^1024*5000000000000000^4541 ≤ 5005117492737949^4541*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50227138364376879279 50000000000000000000 5005117492737949 5000000000000000 1024 4541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005117492737949/5000000000000000 : ℝ)) (X := (50227138364376879279/50000000000000000000 : ℝ)) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(525876503029/3125000000000000000 : ℝ) ≤ ((18642470149697747599/18645000000000000000 : ℝ)+2*(852852210641/372900000000000 : ℝ)*(371/12500 : ℝ))^(4541/1024 : ℝ) := by
    rw [show (18642470149697747599/18645000000000000000 : ℝ)+2*(852852210641/372900000000000 : ℝ)*(371/12500 : ℝ)=(5000000379474103/5000000000000000 : ℝ) by norm_num, show 1+2*(525876503029/3125000000000000000 : ℝ)=(1562500525876503029/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(227138364376879279/100000000000000000000 : ℝ)+(525876503029/3125000000000000000 : ℝ) ≤ ((18642470149697747599/18645000000000000000 : ℝ)+(852852210641/372900000000000 : ℝ)*((12671/50000 : ℝ)+(371/12500 : ℝ)))^(4541/1024 : ℝ) := by
    rw [show (18642470149697747599/18645000000000000000 : ℝ)+(852852210641/372900000000000 : ℝ)*((12671/50000 : ℝ)+(371/12500 : ℝ))=(2501279468053013/2500000000000000 : ℝ) by norm_num, show 1+(227138364376879279/100000000000000000000 : ℝ)+(525876503029/3125000000000000000 : ℝ)=(100227155192424976207/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(227138364376879279/100000000000000000000 : ℝ) ≤ ((18642470149697747599/18645000000000000000 : ℝ)+2*(852852210641/372900000000000 : ℝ)*(12671/50000 : ℝ))^(4541/1024 : ℝ) := by
    rw [show (18642470149697747599/18645000000000000000 : ℝ)+2*(852852210641/372900000000000 : ℝ)*(12671/50000 : ℝ)=(5005117492737949/5000000000000000 : ℝ) by norm_num, show 1+2*(227138364376879279/100000000000000000000 : ℝ)=(50227138364376879279/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18642470149697747599/18645000000000000000 : ℝ)*(X 1 0+X 2 0)+(852852210641/372900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4541/1024 : ℝ)) (lo := (371/12500 : ℝ)) (hi := (12671/50000 : ℝ)) (c := (18642470149697747599/18645000000000000000 : ℝ)) (alpha := (852852210641/372900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18642470149697747599/18645000000000000000 : ℝ)*(X 0 1+X 2 1)+(852852210641/372900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4541/1024 : ℝ)) (lo := (371/12500 : ℝ)) (hi := (12671/50000 : ℝ)) (c := (18642470149697747599/18645000000000000000 : ℝ)) (alpha := (852852210641/372900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18642470149697747599/18645000000000000000 : ℝ)*(X 0 2+X 1 2)+(852852210641/372900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4541/1024 : ℝ)) (lo := (371/12500 : ℝ)) (hi := (12671/50000 : ℝ)) (c := (18642470149697747599/18645000000000000000 : ℝ)) (alpha := (852852210641/372900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-228126357/1250000000 : ℝ)*X 0 0+(1390824353/2500000000 : ℝ)*X 0 1+(5104147571/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5384628353/10000000000 : ℝ)*X 1 0+(-1033228243/5000000000 : ℝ)*X 1 1+(2552074297/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2692315221/5000000000 : ℝ)*X 2 0+(2552073367/5000000000 : ℝ)*X 2 1+(-129153509/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4245598837/10000000000 : ℝ)*X 0 0+(937026839/2500000000 : ℝ)*X 0 1+(4797344023/10000000000 : ℝ)*X 0 2+(4245598837/10000000000 : ℝ)*X 1 0+(937026839/2500000000 : ℝ)*X 1 1+(4797344023/10000000000 : ℝ)*X 1 2+(4245598837/10000000000 : ℝ)*X 2 0+(937026839/2500000000 : ℝ)*X 2 1+(4797344023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1825292689/10000000000 : ℝ)*X 0 0+(5109203539/10000000000 : ℝ)*X 0 1+(1389540357/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5263535433/10000000000 : ℝ)*X 1 0+(-322488317/2000000000 : ℝ)*X 1 1+(222326463/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5263535129/10000000000 : ℝ)*X 2 0+(2779080873/5000000000 : ℝ)*X 2 1+(-201555221/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((169849753/400000000 : ℝ)*X 0 0+(47857903/100000000 : ℝ)*X 0 1+(30078743/80000000 : ℝ)*X 0 2+(169849753/400000000 : ℝ)*X 1 0+(47857903/100000000 : ℝ)*X 1 1+(30078743/80000000 : ℝ)*X 1 2+(169849753/400000000 : ℝ)*X 2 0+(47857903/100000000 : ℝ)*X 2 1+(30078743/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3562248987715849859779615479/310750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (810547/50000000000000 : ℝ)*(base1) + (1016277457/100000000000000 : ℝ)*(base19) + (1861230537/100000000000000 : ℝ)*(base23) + (2122639/20000000000000 : ℝ)*(upper3) + (22234023/6250000000000 : ℝ)*(upper5) + (1565523226594121/100000000000000 : ℝ)*(major0) + (1565523226594121/100000000000000 : ℝ)*(major1) + (1565523226594121/100000000000000 : ℝ)*(major2) + (217794618531351/10000000000000 : ℝ)*(sp0) + (2177960781898903/100000000000000 : ℝ)*(sp1) + (2177959936945823/100000000000000 : ℝ)*(sp2) + (59567465663067/6250000000000 : ℝ)*(sp3) + (1951810493/12500000000000 : ℝ)*(sp4) + (964133731/20000000000000 : ℝ)*(sp7) + (953084272898821/100000000000000 : ℝ)*(f.failure) + (54449044954409/2500000000000 : ℝ)*(f.sum) + (29673836100037/9322500000000000000000000000 : ℝ)*base66 + (7731520932167315479/1864500000000000000000000000000000 : ℝ)*base67 + (4395489032930184521/1864500000000000000000000000000000 : ℝ)*base70 + (2971375309617684521/1864500000000000000000000000000000 : ℝ)*base72 + (17640504607831/18645000000000000000000000000 : ℝ)*base73 + (9600233585960184521/1864500000000000000000000000000000 : ℝ)*base76 + (3074924095830815479/1864500000000000000000000000000000 : ℝ)*base77 + (9916490171049684521/1864500000000000000000000000000000 : ℝ)*base80 + (68579045773/145664062500000000000000000 : ℝ)*base82 + (867039/2500000000000000000000 : ℝ)*base89 + (867039/2500000000000000000000 : ℝ)*base91 + (867039/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7228369238327934910359/1553750000000000000000000000 : ℝ) := by norm_num
    linear_combination (470820697/50000000000000 : ℝ)*(base19) + (57664607/6250000000000 : ℝ)*(base23) + (26418501/20000000000000 : ℝ)*(upper3) + (50812391/100000000000000 : ℝ)*(lower4) + (41840899/100000000000000 : ℝ)*(upper5) + (800521867902019/50000000000000 : ℝ)*(major0) + (800521867902019/50000000000000 : ℝ)*(major1) + (800521867902019/50000000000000 : ℝ)*(major2) + (3512144601/50000000000000 : ℝ)*(sp1) + (1518709309/20000000000000 : ℝ)*(sp2) + (2227378299832253/100000000000000 : ℝ)*(sp4) + (2227370333901657/100000000000000 : ℝ)*(sp5) + (445473956730399/20000000000000 : ℝ)*(sp6) + (194941803340439/20000000000000 : ℝ)*(sp7) + (194941803340439/20000000000000 : ℝ)*(f.failure) + (2227378299832253/100000000000000 : ℝ)*(f.sum) + (970873362431/2330625000000000000000000000 : ℝ)*base65 + (1295773883877297619/932250000000000000000000000000000 : ℝ)*base68 + (2449171280968202381/932250000000000000000000000000000 : ℝ)*base69 + (1405686900016047619/932250000000000000000000000000000 : ℝ)*base72 + (31922695175323/18645000000000000000000000000 : ℝ)*base73 + (3618820177079547619/932250000000000000000000000000000 : ℝ)*base76 + (3230859912513452381/932250000000000000000000000000000 : ℝ)*base77 + (6357650017083452381/932250000000000000000000000000000 : ℝ)*base79 + (104115706303033/18645000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1554699/500000000000000000000 : ℝ)*base90 + (1554699/500000000000000000000 : ℝ)*base92 + (1554699/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1523_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41064659/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12671/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (371/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8501/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3643/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1523_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1523_s2_0 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-462072889/2500000000 : ℝ)*x 0 + (340904993/625000000 : ℝ)*x 1 + (1299466897/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (462072889/2500000000 : ℝ)^4543 ≤ (452341800947/4000000000000 : ℝ)^3519 := by
    have hnat : (462072889 : ℕ)^4543*4000000000000^3519 ≤ 452341800947^3519*2500000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462072889 2500000000 452341800947 4000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340904993/625000000 : ℝ)^4543 ≤ (4572468659967/10000000000000 : ℝ)^3519 := by
    have hnat : (340904993 : ℕ)^4543*10000000000000^3519 ≤ 4572468659967^3519*625000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340904993 625000000 4572468659967 10000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1299466897/2500000000 : ℝ)^4543 ≤ (21483384180049/50000000000000 : ℝ)^3519 := by
    have hnat : (1299466897 : ℕ)^4543*50000000000000^3519 ≤ 21483384180049^3519*2500000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299466897 2500000000 21483384180049 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-462072889/2500000000 : ℝ), (340904993/625000000 : ℝ), (1299466897/2500000000 : ℝ)] ![(452341800947/4000000000000 : ℝ), (4572468659967/10000000000000 : ℝ), (21483384180049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-462072889/2500000000 : ℝ)|^4543 ≤ (452341800947/4000000000000 : ℝ)^3519
        have hw : |(-462072889/2500000000 : ℝ)|=(462072889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340904993/625000000 : ℝ)|^4543 ≤ (4572468659967/10000000000000 : ℝ)^3519
        have hw : |(340904993/625000000 : ℝ)|=(340904993/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1299466897/2500000000 : ℝ)|^4543 ≤ (21483384180049/50000000000000 : ℝ)^3519
        have hw : |(1299466897/2500000000 : ℝ)|=(1299466897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s2_1 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356886937/10000000000 : ℝ)*x 0 + (-396061337/2000000000 : ℝ)*x 1 + (51978681/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356886937/10000000000 : ℝ)^4543 ≤ (44671264484031/100000000000000 : ℝ)^3519 := by
    have hnat : (5356886937 : ℕ)^4543*100000000000000^3519 ≤ 44671264484031^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356886937 10000000000 44671264484031 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (396061337/2000000000 : ℝ)^4543 ≤ (6180980841603/50000000000000 : ℝ)^3519 := by
    have hnat : (396061337 : ℕ)^4543*50000000000000^3519 ≤ 6180980841603^3519*2000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396061337 2000000000 6180980841603 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51978681/100000000 : ℝ)^4543 ≤ (1718670952959/4000000000000 : ℝ)^3519 := by
    have hnat : (51978681 : ℕ)^4543*4000000000000^3519 ≤ 1718670952959^3519*100000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51978681 100000000 1718670952959 4000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356886937/10000000000 : ℝ), (-396061337/2000000000 : ℝ), (51978681/100000000 : ℝ)] ![(44671264484031/100000000000000 : ℝ), (6180980841603/50000000000000 : ℝ), (1718670952959/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356886937/10000000000 : ℝ)|^4543 ≤ (44671264484031/100000000000000 : ℝ)^3519
        have hw : |(5356886937/10000000000 : ℝ)|=(5356886937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-396061337/2000000000 : ℝ)|^4543 ≤ (6180980841603/50000000000000 : ℝ)^3519
        have hw : |(-396061337/2000000000 : ℝ)|=(396061337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(51978681/100000000 : ℝ)|^4543 ≤ (1718670952959/4000000000000 : ℝ)^3519
        have hw : |(51978681/100000000 : ℝ)|=(51978681/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s2_2 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167402741/312500000 : ℝ)*x 0 + (2598933813/5000000000 : ℝ)*x 1 + (-1980306277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167402741/312500000 : ℝ)^4543 ≤ (4467127282739/10000000000000 : ℝ)^3519 := by
    have hnat : (167402741 : ℕ)^4543*10000000000000^3519 ≤ 4467127282739^3519*312500000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167402741 312500000 4467127282739 10000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2598933813/5000000000 : ℝ)^4543 ≤ (2148338438281/5000000000000 : ℝ)^3519 := by
    have hnat : (2598933813 : ℕ)^4543*5000000000000^3519 ≤ 2148338438281^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598933813 5000000000 2148338438281 5000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1980306277/10000000000 : ℝ)^4543 ≤ (2472391679031/20000000000000 : ℝ)^3519 := by
    have hnat : (1980306277 : ℕ)^4543*20000000000000^3519 ≤ 2472391679031^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980306277 10000000000 2472391679031 20000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167402741/312500000 : ℝ), (2598933813/5000000000 : ℝ), (-1980306277/10000000000 : ℝ)] ![(4467127282739/10000000000000 : ℝ), (2148338438281/5000000000000 : ℝ), (2472391679031/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167402741/312500000 : ℝ)|^4543 ≤ (4467127282739/10000000000000 : ℝ)^3519
        have hw : |(167402741/312500000 : ℝ)|=(167402741/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2598933813/5000000000 : ℝ)|^4543 ≤ (2148338438281/5000000000000 : ℝ)^3519
        have hw : |(2598933813/5000000000 : ℝ)|=(2598933813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1980306277/10000000000 : ℝ)|^4543 ≤ (2472391679031/20000000000000 : ℝ)^3519
        have hw : |(-1980306277/10000000000 : ℝ)|=(1980306277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s2_3 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2131171781/5000000000 : ℝ)*x 0 + (1988809109/5000000000 : ℝ)*x 1 + (4564022883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131171781/5000000000 : ℝ)^4543 ≤ (33256703955821/100000000000000 : ℝ)^3519 := by
    have hnat : (2131171781 : ℕ)^4543*100000000000000^3519 ≤ 33256703955821^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131171781 5000000000 33256703955821 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1988809109/5000000000 : ℝ)^4543 ≤ (7604255931767/25000000000000 : ℝ)^3519 := by
    have hnat : (1988809109 : ℕ)^4543*25000000000000^3519 ≤ 7604255931767^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988809109 5000000000 7604255931767 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4564022883/10000000000 : ℝ)^4543 ≤ (7265254461487/20000000000000 : ℝ)^3519 := by
    have hnat : (4564022883 : ℕ)^4543*20000000000000^3519 ≤ 7265254461487^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4564022883 10000000000 7265254461487 20000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2131171781/5000000000 : ℝ), (1988809109/5000000000 : ℝ), (4564022883/10000000000 : ℝ)] ![(33256703955821/100000000000000 : ℝ), (7604255931767/25000000000000 : ℝ), (7265254461487/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2131171781/5000000000 : ℝ)|^4543 ≤ (33256703955821/100000000000000 : ℝ)^3519
        have hw : |(2131171781/5000000000 : ℝ)|=(2131171781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1988809109/5000000000 : ℝ)|^4543 ≤ (7604255931767/25000000000000 : ℝ)^3519
        have hw : |(1988809109/5000000000 : ℝ)|=(1988809109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4564022883/10000000000 : ℝ)|^4543 ≤ (7265254461487/20000000000000 : ℝ)^3519
        have hw : |(4564022883/10000000000 : ℝ)|=(4564022883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s2_4 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-462084919/2500000000 : ℝ)*x 0 + (32496601/62500000 : ℝ)*x 1 + (2726439089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (462084919/2500000000 : ℝ)^4543 ≤ (11308925114149/100000000000000 : ℝ)^3519 := by
    have hnat : (462084919 : ℕ)^4543*100000000000000^3519 ≤ 11308925114149^3519*2500000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462084919 2500000000 11308925114149 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32496601/62500000 : ℝ)^4543 ≤ (4298372177387/10000000000000 : ℝ)^3519 := by
    have hnat : (32496601 : ℕ)^4543*10000000000000^3519 ≤ 4298372177387^3519*62500000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32496601 62500000 4298372177387 10000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2726439089/5000000000 : ℝ)^4543 ≤ (45707353102541/100000000000000 : ℝ)^3519 := by
    have hnat : (2726439089 : ℕ)^4543*100000000000000^3519 ≤ 45707353102541^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726439089 5000000000 45707353102541 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-462084919/2500000000 : ℝ), (32496601/62500000 : ℝ), (2726439089/5000000000 : ℝ)] ![(11308925114149/100000000000000 : ℝ), (4298372177387/10000000000000 : ℝ), (45707353102541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-462084919/2500000000 : ℝ)|^4543 ≤ (11308925114149/100000000000000 : ℝ)^3519
        have hw : |(-462084919/2500000000 : ℝ)|=(462084919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32496601/62500000 : ℝ)|^4543 ≤ (4298372177387/10000000000000 : ℝ)^3519
        have hw : |(32496601/62500000 : ℝ)|=(32496601/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2726439089/5000000000 : ℝ)|^4543 ≤ (45707353102541/100000000000000 : ℝ)^3519
        have hw : |(2726439089/5000000000 : ℝ)|=(2726439089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s2_5 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289398217/10000000000 : ℝ)*x 0 + (-1725296941/10000000000 : ℝ)*x 1 + (340804933/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289398217/10000000000 : ℝ)^4543 ≤ (43946042042581/100000000000000 : ℝ)^3519 := by
    have hnat : (5289398217 : ℕ)^4543*100000000000000^3519 ≤ 43946042042581^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289398217 10000000000 43946042042581 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1725296941/10000000000 : ℝ)^4543 ≤ (2586649182489/25000000000000 : ℝ)^3519 := by
    have hnat : (1725296941 : ℕ)^4543*25000000000000^3519 ≤ 2586649182489^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1725296941 10000000000 2586649182489 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340804933/625000000 : ℝ)^4543 ≤ (45707361218597/100000000000000 : ℝ)^3519 := by
    have hnat : (340804933 : ℕ)^4543*100000000000000^3519 ≤ 45707361218597^3519*625000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340804933 625000000 45707361218597 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289398217/10000000000 : ℝ), (-1725296941/10000000000 : ℝ), (340804933/625000000 : ℝ)] ![(43946042042581/100000000000000 : ℝ), (2586649182489/25000000000000 : ℝ), (45707361218597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289398217/10000000000 : ℝ)|^4543 ≤ (43946042042581/100000000000000 : ℝ)^3519
        have hw : |(5289398217/10000000000 : ℝ)|=(5289398217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1725296941/10000000000 : ℝ)|^4543 ≤ (2586649182489/25000000000000 : ℝ)^3519
        have hw : |(-1725296941/10000000000 : ℝ)|=(1725296941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(340804933/625000000 : ℝ)|^4543 ≤ (45707361218597/100000000000000 : ℝ)^3519
        have hw : |(340804933/625000000 : ℝ)|=(340804933/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s2_6 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289399017/10000000000 : ℝ)*x 0 + (1363219667/2500000000 : ℝ)*x 1 + (-345059239/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289399017/10000000000 : ℝ)^4543 ≤ (8789210124673/20000000000000 : ℝ)^3519 := by
    have hnat : (5289399017 : ℕ)^4543*20000000000000^3519 ≤ 8789210124673^3519*10000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289399017 10000000000 8789210124673 20000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363219667/2500000000 : ℝ)^4543 ≤ (45707358405031/100000000000000 : ℝ)^3519 := by
    have hnat : (1363219667 : ℕ)^4543*100000000000000^3519 ≤ 45707358405031^3519*2500000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363219667 2500000000 45707358405031 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345059239/2000000000 : ℝ)^4543 ≤ (10346590954371/100000000000000 : ℝ)^3519 := by
    have hnat : (345059239 : ℕ)^4543*100000000000000^3519 ≤ 10346590954371^3519*2000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345059239 2000000000 10346590954371 100000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289399017/10000000000 : ℝ), (1363219667/2500000000 : ℝ), (-345059239/2000000000 : ℝ)] ![(8789210124673/20000000000000 : ℝ), (45707358405031/100000000000000 : ℝ), (10346590954371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289399017/10000000000 : ℝ)|^4543 ≤ (8789210124673/20000000000000 : ℝ)^3519
        have hw : |(5289399017/10000000000 : ℝ)|=(5289399017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363219667/2500000000 : ℝ)|^4543 ≤ (45707358405031/100000000000000 : ℝ)^3519
        have hw : |(1363219667/2500000000 : ℝ)|=(1363219667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-345059239/2000000000 : ℝ)|^4543 ≤ (10346590954371/100000000000000 : ℝ)^3519
        have hw : |(-345059239/2000000000 : ℝ)|=(345059239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1523_s2_7 (p : ℝ) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (532807127/1250000000 : ℝ)*x 0 + (2280197203/5000000000 : ℝ)*x 1 + (796255631/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532807127/1250000000 : ℝ)^4543 ≤ (8314461692563/25000000000000 : ℝ)^3519 := by
    have hnat : (532807127 : ℕ)^4543*25000000000000^3519 ≤ 8314461692563^3519*1250000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532807127 1250000000 8314461692563 25000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2280197203/5000000000 : ℝ)^4543 ≤ (18144496380599/50000000000000 : ℝ)^3519 := by
    have hnat : (2280197203 : ℕ)^4543*50000000000000^3519 ≤ 18144496380599^3519*5000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280197203 5000000000 18144496380599 50000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (796255631/2000000000 : ℝ)^4543 ≤ (1218126418197/4000000000000 : ℝ)^3519 := by
    have hnat : (796255631 : ℕ)^4543*4000000000000^3519 ≤ 1218126418197^3519*2000000000^4543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796255631 2000000000 1218126418197 4000000000000 4543 3519 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4543/1024 : ℝ)) 4543 3519 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(532807127/1250000000 : ℝ), (2280197203/5000000000 : ℝ), (796255631/2000000000 : ℝ)] ![(8314461692563/25000000000000 : ℝ), (18144496380599/50000000000000 : ℝ), (1218126418197/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(532807127/1250000000 : ℝ)|^4543 ≤ (8314461692563/25000000000000 : ℝ)^3519
        have hw : |(532807127/1250000000 : ℝ)|=(532807127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2280197203/5000000000 : ℝ)|^4543 ≤ (18144496380599/50000000000000 : ℝ)^3519
        have hw : |(2280197203/5000000000 : ℝ)|=(2280197203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(796255631/2000000000 : ℝ)|^4543 ≤ (1218126418197/4000000000000 : ℝ)^3519
        have hw : |(796255631/2000000000 : ℝ)|=(796255631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1523_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41064659/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3643/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8501/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10523/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3989/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3643/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8501/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3643/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8501/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3643/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8501/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3643/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8501/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3643/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8501/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3643/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8501/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8501/100000 : ℝ) ^ (4541/1024 : ℝ) ≤ (894601288667633/50000000000000000000 : ℝ) := by
    have hpowers : (8501/100000 : ℝ)^4541 ≤ (894601288667633/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8501 : ℕ)^4541*50000000000000000000^1024 ≤ 894601288667633^1024*100000^4541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8501 100000 894601288667633 50000000000000000000 4541 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8501/100000 : ℝ)) (X := (894601288667633/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3643/20000 : ℝ) ^ (4541/1024 : ℝ) ≤ (52519571976967433/100000000000000000000 : ℝ) := by
    have hpowers : (3643/20000 : ℝ)^4541 ≤ (52519571976967433/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3643 : ℕ)^4541*100000000000000000000^1024 ≤ 52519571976967433^1024*20000^4541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3643 20000 52519571976967433 100000000000000000000 4541 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3643/20000 : ℝ)) (X := (52519571976967433/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000894601288667633/25000000000000000000 : ℝ) ≤ (400003227690907/400000000000000 : ℝ) ^ (4541/1024 : ℝ) := by
    have hpowers : (25000894601288667633/25000000000000000000 : ℝ)^1024 ≤ (400003227690907/400000000000000 : ℝ)^4541 := by
      have hnat : (25000894601288667633 : ℕ)^1024*400000000000000^4541 ≤ 400003227690907^4541*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000894601288667633 25000000000000000000 400003227690907 400000000000000 1024 4541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400003227690907/400000000000000 : ℝ)) (X := (25000894601288667633/25000000000000000000 : ℝ)) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100054308774554302699/100000000000000000000 : ℝ) ≤ (5000612205385103/5000000000000000 : ℝ) ^ (4541/1024 : ℝ) := by
    have hpowers : (100054308774554302699/100000000000000000000 : ℝ)^1024 ≤ (5000612205385103/5000000000000000 : ℝ)^4541 := by
      have hnat : (100054308774554302699 : ℕ)^1024*5000000000000000^4541 ≤ 5000612205385103^4541*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100054308774554302699 100000000000000000000 5000612205385103 5000000000000000 1024 4541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000612205385103/5000000000000000 : ℝ)) (X := (100054308774554302699/100000000000000000000 : ℝ)) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50052519571976967433/50000000000000000000 : ℝ) ≤ (10002368129267737/10000000000000000 : ℝ) ^ (4541/1024 : ℝ) := by
    have hpowers : (50052519571976967433/50000000000000000000 : ℝ)^1024 ≤ (10002368129267737/10000000000000000 : ℝ)^4541 := by
      have hnat : (50052519571976967433 : ℕ)^1024*10000000000000000^4541 ≤ 10002368129267737^4541*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50052519571976967433 50000000000000000000 10002368129267737 10000000000000000 1024 4541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002368129267737/10000000000000000 : ℝ)) (X := (50052519571976967433/50000000000000000000 : ℝ)) (by norm_num) 4541 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(894601288667633/50000000000000000000 : ℝ) ≤ ((4046722430951739287/4047500000000000000 : ℝ)+2*(381239499177/323800000000000 : ℝ)*(8501/100000 : ℝ))^(4541/1024 : ℝ) := by
    rw [show (4046722430951739287/4047500000000000000 : ℝ)+2*(381239499177/323800000000000 : ℝ)*(8501/100000 : ℝ)=(400003227690907/400000000000000 : ℝ) by norm_num, show 1+2*(894601288667633/50000000000000000000 : ℝ)=(25000894601288667633/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(52519571976967433/100000000000000000000 : ℝ)+(894601288667633/50000000000000000000 : ℝ) ≤ ((4046722430951739287/4047500000000000000 : ℝ)+(381239499177/323800000000000 : ℝ)*((3643/20000 : ℝ)+(8501/100000 : ℝ)))^(4541/1024 : ℝ) := by
    rw [show (4046722430951739287/4047500000000000000 : ℝ)+(381239499177/323800000000000 : ℝ)*((3643/20000 : ℝ)+(8501/100000 : ℝ))=(5000612205385103/5000000000000000 : ℝ) by norm_num, show 1+(52519571976967433/100000000000000000000 : ℝ)+(894601288667633/50000000000000000000 : ℝ)=(100054308774554302699/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(52519571976967433/100000000000000000000 : ℝ) ≤ ((4046722430951739287/4047500000000000000 : ℝ)+2*(381239499177/323800000000000 : ℝ)*(3643/20000 : ℝ))^(4541/1024 : ℝ) := by
    rw [show (4046722430951739287/4047500000000000000 : ℝ)+2*(381239499177/323800000000000 : ℝ)*(3643/20000 : ℝ)=(10002368129267737/10000000000000000 : ℝ) by norm_num, show 1+2*(52519571976967433/100000000000000000000 : ℝ)=(50052519571976967433/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4046722430951739287/4047500000000000000 : ℝ)*(X 1 0+X 2 0)+(381239499177/323800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4541/1024 : ℝ)) (lo := (8501/100000 : ℝ)) (hi := (3643/20000 : ℝ)) (c := (4046722430951739287/4047500000000000000 : ℝ)) (alpha := (381239499177/323800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4046722430951739287/4047500000000000000 : ℝ)*(X 0 1+X 2 1)+(381239499177/323800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4541/1024 : ℝ)) (lo := (8501/100000 : ℝ)) (hi := (3643/20000 : ℝ)) (c := (4046722430951739287/4047500000000000000 : ℝ)) (alpha := (381239499177/323800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4046722430951739287/4047500000000000000 : ℝ)*(X 0 2+X 1 2)+(381239499177/323800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4541/1024 : ℝ)) (lo := (8501/100000 : ℝ)) (hi := (3643/20000 : ℝ)) (c := (4046722430951739287/4047500000000000000 : ℝ)) (alpha := (381239499177/323800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-462072889/2500000000 : ℝ)*X 0 0+(340904993/625000000 : ℝ)*X 0 1+(1299466897/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356886937/10000000000 : ℝ)*X 1 0+(-396061337/2000000000 : ℝ)*X 1 1+(51978681/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167402741/312500000 : ℝ)*X 2 0+(2598933813/5000000000 : ℝ)*X 2 1+(-1980306277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2131171781/5000000000 : ℝ)*X 0 0+(1988809109/5000000000 : ℝ)*X 0 1+(4564022883/10000000000 : ℝ)*X 0 2+(2131171781/5000000000 : ℝ)*X 1 0+(1988809109/5000000000 : ℝ)*X 1 1+(4564022883/10000000000 : ℝ)*X 1 2+(2131171781/5000000000 : ℝ)*X 2 0+(1988809109/5000000000 : ℝ)*X 2 1+(4564022883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-462084919/2500000000 : ℝ)*X 0 0+(32496601/62500000 : ℝ)*X 0 1+(2726439089/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289398217/10000000000 : ℝ)*X 1 0+(-1725296941/10000000000 : ℝ)*X 1 1+(340804933/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289399017/10000000000 : ℝ)*X 2 0+(1363219667/2500000000 : ℝ)*X 2 1+(-345059239/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((532807127/1250000000 : ℝ)*X 0 0+(2280197203/5000000000 : ℝ)*X 0 1+(796255631/2000000000 : ℝ)*X 0 2+(532807127/1250000000 : ℝ)*X 1 0+(2280197203/5000000000 : ℝ)*X 1 1+(796255631/2000000000 : ℝ)*X 1 2+(532807127/1250000000 : ℝ)*X 2 0+(2280197203/5000000000 : ℝ)*X 2 1+(796255631/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1523_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10491251967817070469278787/6324218750000000000000000000000 : ℝ) := by norm_num
    linear_combination (313621667/50000000000000 : ℝ)*(base19) + (163195217/20000000000000 : ℝ)*(base23) + (8853683/50000000000000 : ℝ)*(upper3) + (2511401/1250000000000 : ℝ)*(upper4) + (187522193/100000000000000 : ℝ)*(upper5) + (700284923310293/25000000000000 : ℝ)*(major0) + (700284923310293/25000000000000 : ℝ)*(major1) + (700284923310293/25000000000000 : ℝ)*(major2) + (389693775862549/10000000000000 : ℝ)*(sp0) + (487119509105517/12500000000000 : ℝ)*(sp1) + (779391176822277/20000000000000 : ℝ)*(sp2) + (1705314555941073/100000000000000 : ℝ)*(sp3) + (947073099/5000000000000 : ℝ)*(sp4) + (8075157101/100000000000000 : ℝ)*(sp7) + (852661315549087/50000000000000 : ℝ)*(f.failure) + (389695670008747/10000000000000 : ℝ)*(f.sum) + (6097977967033/2023750000000000000000000000 : ℝ)*base65 + (506745388822156409/101187500000000000000000000000000 : ℝ)*base68 + (306293541650031409/101187500000000000000000000000000 : ℝ)*base70 + (854856417687531409/101187500000000000000000000000000 : ℝ)*base72 + (11437923790261/4047500000000000000000000000 : ℝ)*base73 + (177397973760031409/101187500000000000000000000000000 : ℝ)*base76 + (1033993676742031409/101187500000000000000000000000000 : ℝ)*base78 + (421793600820968591/101187500000000000000000000000000 : ℝ)*base79 + (12301003351167/8095000000000000000000000000 : ℝ)*base81 + (5416333/1250000000000000000000 : ℝ)*base89 + (5416333/1250000000000000000000 : ℝ)*base91 + (5416333/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (260107013263095007728183621/25296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (58813209/50000000000000 : ℝ)*(base15) + (3069977/800000000000 : ℝ)*(lower2) + (1483857/800000000000 : ℝ)*(upper3) + (68680991/100000000000000 : ℝ)*(lower4) + (709096176190661/25000000000000 : ℝ)*(major0) + (709096176190661/25000000000000 : ℝ)*(major1) + (709096176190661/25000000000000 : ℝ)*(major2) + (454165223/25000000000000 : ℝ)*(sp1) + (1241995291/12500000000000 : ℝ)*(sp2) + (779452063/25000000000000 : ℝ)*(sp3) + (1972994706887101/50000000000000 : ℝ)*(sp4) + (3945987479486893/100000000000000 : ℝ)*(sp5) + (1972989738905937/50000000000000 : ℝ)*(sp6) + (107923533450219/6250000000000 : ℝ)*(sp7) + (431694913252939/25000000000000 : ℝ)*(f.failure) + (1972994706887101/50000000000000 : ℝ)*(f.sum) + (15663490633037/4047500000000000000000000000 : ℝ)*base65 + (246666514581338793/101187500000000000000000000000000 : ℝ)*base68 + (134705964060661207/101187500000000000000000000000000 : ℝ)*base69 + (1813633614535526293/101187500000000000000000000000000 : ℝ)*base72 + (23737456614429/8095000000000000000000000000 : ℝ)*base73 + (10100628677588793/101187500000000000000000000000000 : ℝ)*base76 + (213050124958713793/101187500000000000000000000000000 : ℝ)*base78 + (396475907578838793/101187500000000000000000000000000 : ℝ)*base80 + (747067714121/126484375000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4217199/625000000000000000000 : ℝ)*base90 + (4217199/625000000000000000000 : ℝ)*base92 + (4217199/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1523_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41064659/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3643/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8501/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10523/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3989/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1523_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1523_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41064659/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10523/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3989/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1523_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1523_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1523_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4541/1024 : ℝ) ≤ p) (hpb : p ≤ (4543/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41064659/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10523/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3989/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1523_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
