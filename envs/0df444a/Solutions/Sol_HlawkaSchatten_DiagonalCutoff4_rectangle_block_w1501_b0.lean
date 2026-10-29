-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1501_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:52:22.497702+00:00
-- url     : https://prove2.me/submissions/5d90f7dc-170a-4119-99e2-ba975b192883

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
theorem support_rectangle_w1501_s0_0 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-212195377/1250000000 : ℝ)*x 0 + (5921348189/10000000000 : ℝ)*x 1 + (2425292121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212195377/1250000000 : ℝ)^4499 ≤ (2013278610099/20000000000000 : ℝ)^3475 := by
    have hnat : (212195377 : ℕ)^4499*20000000000000^3475 ≤ 2013278610099^3475*1250000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212195377 1250000000 2013278610099 20000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5921348189/10000000000 : ℝ)^4499 ≤ (6342615228687/12500000000000 : ℝ)^3475 := by
    have hnat : (5921348189 : ℕ)^4499*12500000000000^3475 ≤ 6342615228687^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5921348189 10000000000 6342615228687 12500000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2425292121/5000000000 : ℝ)^4499 ≤ (19596342549707/50000000000000 : ℝ)^3475 := by
    have hnat : (2425292121 : ℕ)^4499*50000000000000^3475 ≤ 19596342549707^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2425292121 5000000000 19596342549707 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-212195377/1250000000 : ℝ), (5921348189/10000000000 : ℝ), (2425292121/5000000000 : ℝ)] ![(2013278610099/20000000000000 : ℝ), (6342615228687/12500000000000 : ℝ), (19596342549707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-212195377/1250000000 : ℝ)|^4499 ≤ (2013278610099/20000000000000 : ℝ)^3475
        have hw : |(-212195377/1250000000 : ℝ)|=(212195377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5921348189/10000000000 : ℝ)|^4499 ≤ (6342615228687/12500000000000 : ℝ)^3475
        have hw : |(5921348189/10000000000 : ℝ)|=(5921348189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2425292121/5000000000 : ℝ)|^4499 ≤ (19596342549707/50000000000000 : ℝ)^3475
        have hw : |(2425292121/5000000000 : ℝ)|=(2425292121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s0_1 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5480377801/10000000000 : ℝ)*x 0 + (-2298602903/10000000000 : ℝ)*x 1 + (4850584191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5480377801/10000000000 : ℝ)^4499 ≤ (45903325905779/100000000000000 : ℝ)^3475 := by
    have hnat : (5480377801 : ℕ)^4499*100000000000000^3475 ≤ 45903325905779^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480377801 10000000000 45903325905779 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2298602903/10000000000 : ℝ)^4499 ≤ (2980797905063/20000000000000 : ℝ)^3475 := by
    have hnat : (2298602903 : ℕ)^4499*20000000000000^3475 ≤ 2980797905063^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2298602903 10000000000 2980797905063 20000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4850584191/10000000000 : ℝ)^4499 ≤ (2449542785369/6250000000000 : ℝ)^3475 := by
    have hnat : (4850584191 : ℕ)^4499*6250000000000^3475 ≤ 2449542785369^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4850584191 10000000000 2449542785369 6250000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5480377801/10000000000 : ℝ), (-2298602903/10000000000 : ℝ), (4850584191/10000000000 : ℝ)] ![(45903325905779/100000000000000 : ℝ), (2980797905063/20000000000000 : ℝ), (2449542785369/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5480377801/10000000000 : ℝ)|^4499 ≤ (45903325905779/100000000000000 : ℝ)^3475
        have hw : |(5480377801/10000000000 : ℝ)|=(5480377801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2298602903/10000000000 : ℝ)|^4499 ≤ (2980797905063/20000000000000 : ℝ)^3475
        have hw : |(-2298602903/10000000000 : ℝ)|=(2298602903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4850584191/10000000000 : ℝ)|^4499 ≤ (2449542785369/6250000000000 : ℝ)^3475
        have hw : |(4850584191/10000000000 : ℝ)|=(4850584191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s0_2 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (548037787/1000000000 : ℝ)*x 0 + (2425292097/5000000000 : ℝ)*x 1 + (-2298602809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548037787/1000000000 : ℝ)^4499 ≤ (5737915831753/12500000000000 : ℝ)^3475 := by
    have hnat : (548037787 : ℕ)^4499*12500000000000^3475 ≤ 5737915831753^3475*1000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548037787 1000000000 5737915831753 12500000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2425292097/5000000000 : ℝ)^4499 ≤ (39192684597287/100000000000000 : ℝ)^3475 := by
    have hnat : (2425292097 : ℕ)^4499*100000000000000^3475 ≤ 39192684597287^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2425292097 5000000000 39192684597287 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2298602809/10000000000 : ℝ)^4499 ≤ (14903988736223/100000000000000 : ℝ)^3475 := by
    have hnat : (2298602809 : ℕ)^4499*100000000000000^3475 ≤ 14903988736223^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2298602809 10000000000 14903988736223 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(548037787/1000000000 : ℝ), (2425292097/5000000000 : ℝ), (-2298602809/10000000000 : ℝ)] ![(5737915831753/12500000000000 : ℝ), (39192684597287/100000000000000 : ℝ), (14903988736223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(548037787/1000000000 : ℝ)|^4499 ≤ (5737915831753/12500000000000 : ℝ)^3475
        have hw : |(548037787/1000000000 : ℝ)|=(548037787/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2425292097/5000000000 : ℝ)|^4499 ≤ (39192684597287/100000000000000 : ℝ)^3475
        have hw : |(2425292097/5000000000 : ℝ)|=(2425292097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2298602809/10000000000 : ℝ)|^4499 ≤ (14903988736223/100000000000000 : ℝ)^3475
        have hw : |(-2298602809/10000000000 : ℝ)|=(2298602809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s0_3 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (414812309/1000000000 : ℝ)*x 0 + (3091234497/10000000000 : ℝ)*x 1 + (5500474807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414812309/1000000000 : ℝ)^4499 ≤ (16003375250211/50000000000000 : ℝ)^3475 := by
    have hnat : (414812309 : ℕ)^4499*50000000000000^3475 ≤ 16003375250211^3475*1000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414812309 1000000000 16003375250211 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091234497/10000000000 : ℝ)^4499 ≤ (6998998823/32000000000 : ℝ)^3475 := by
    have hnat : (3091234497 : ℕ)^4499*32000000000^3475 ≤ 6998998823^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091234497 10000000000 6998998823 32000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5500474807/10000000000 : ℝ)^4499 ≤ (922427563251/2000000000000 : ℝ)^3475 := by
    have hnat : (5500474807 : ℕ)^4499*2000000000000^3475 ≤ 922427563251^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500474807 10000000000 922427563251 2000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(414812309/1000000000 : ℝ), (3091234497/10000000000 : ℝ), (5500474807/10000000000 : ℝ)] ![(16003375250211/50000000000000 : ℝ), (6998998823/32000000000 : ℝ), (922427563251/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(414812309/1000000000 : ℝ)|^4499 ≤ (16003375250211/50000000000000 : ℝ)^3475
        have hw : |(414812309/1000000000 : ℝ)|=(414812309/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091234497/10000000000 : ℝ)|^4499 ≤ (6998998823/32000000000 : ℝ)^3475
        have hw : |(3091234497/10000000000 : ℝ)|=(3091234497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5500474807/10000000000 : ℝ)|^4499 ≤ (922427563251/2000000000000 : ℝ)^3475
        have hw : |(5500474807/10000000000 : ℝ)|=(5500474807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s0_4 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-425294631/2500000000 : ℝ)*x 0 + (152436023/312500000 : ℝ)*x 1 + (29464989/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425294631/2500000000 : ℝ)^4499 ≤ (10094159137731/100000000000000 : ℝ)^3475 := by
    have hnat : (425294631 : ℕ)^4499*100000000000000^3475 ≤ 10094159137731^3475*2500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425294631 2500000000 10094159137731 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (152436023/312500000 : ℝ)^4499 ≤ (19739611958519/50000000000000 : ℝ)^3475 := by
    have hnat : (152436023 : ℕ)^4499*50000000000000^3475 ≤ 19739611958519^3475*312500000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152436023 312500000 19739611958519 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29464989/50000000 : ℝ)^4499 ≤ (1008532338729/2000000000000 : ℝ)^3475 := by
    have hnat : (29464989 : ℕ)^4499*2000000000000^3475 ≤ 1008532338729^3475*50000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29464989 50000000 1008532338729 2000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-425294631/2500000000 : ℝ), (152436023/312500000 : ℝ), (29464989/50000000 : ℝ)] ![(10094159137731/100000000000000 : ℝ), (19739611958519/50000000000000 : ℝ), (1008532338729/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-425294631/2500000000 : ℝ)|^4499 ≤ (10094159137731/100000000000000 : ℝ)^3475
        have hw : |(-425294631/2500000000 : ℝ)|=(425294631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(152436023/312500000 : ℝ)|^4499 ≤ (19739611958519/50000000000000 : ℝ)^3475
        have hw : |(152436023/312500000 : ℝ)|=(152436023/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(29464989/50000000 : ℝ)|^4499 ≤ (1008532338729/2000000000000 : ℝ)^3475
        have hw : |(29464989/50000000 : ℝ)|=(29464989/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s0_5 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1296971777/2500000000 : ℝ)*x 0 + (-1256189231/10000000000 : ℝ)*x 1 + (1473249463/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1296971777/2500000000 : ℝ)^4499 ≤ (21378389879209/50000000000000 : ℝ)^3475 := by
    have hnat : (1296971777 : ℕ)^4499*50000000000000^3475 ≤ 21378389879209^3475*2500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296971777 2500000000 21378389879209 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1256189231/10000000000 : ℝ)^4499 ≤ (6816602716103/100000000000000 : ℝ)^3475 := by
    have hnat : (1256189231 : ℕ)^4499*100000000000000^3475 ≤ 6816602716103^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1256189231 10000000000 6816602716103 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1473249463/2500000000 : ℝ)^4499 ≤ (50426617512537/100000000000000 : ℝ)^3475 := by
    have hnat : (1473249463 : ℕ)^4499*100000000000000^3475 ≤ 50426617512537^3475*2500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1473249463 2500000000 50426617512537 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1296971777/2500000000 : ℝ), (-1256189231/10000000000 : ℝ), (1473249463/2500000000 : ℝ)] ![(21378389879209/50000000000000 : ℝ), (6816602716103/100000000000000 : ℝ), (50426617512537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1296971777/2500000000 : ℝ)|^4499 ≤ (21378389879209/50000000000000 : ℝ)^3475
        have hw : |(1296971777/2500000000 : ℝ)|=(1296971777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1256189231/10000000000 : ℝ)|^4499 ≤ (6816602716103/100000000000000 : ℝ)^3475
        have hw : |(-1256189231/10000000000 : ℝ)|=(1256189231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1473249463/2500000000 : ℝ)|^4499 ≤ (50426617512537/100000000000000 : ℝ)^3475
        have hw : |(1473249463/2500000000 : ℝ)|=(1473249463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s0_6 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1296971783/2500000000 : ℝ)*x 0 + (5892997793/10000000000 : ℝ)*x 1 + (-157023661/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1296971783/2500000000 : ℝ)^4499 ≤ (8551356002901/20000000000000 : ℝ)^3475 := by
    have hnat : (1296971783 : ℕ)^4499*20000000000000^3475 ≤ 8551356002901^3475*2500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296971783 2500000000 8551356002901 20000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5892997793/10000000000 : ℝ)^4499 ≤ (504266168589/1000000000000 : ℝ)^3475 := by
    have hnat : (5892997793 : ℕ)^4499*1000000000000^3475 ≤ 504266168589^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5892997793 10000000000 504266168589 1000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157023661/1250000000 : ℝ)^4499 ≤ (3408301558277/50000000000000 : ℝ)^3475 := by
    have hnat : (157023661 : ℕ)^4499*50000000000000^3475 ≤ 3408301558277^3475*1250000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157023661 1250000000 3408301558277 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1296971783/2500000000 : ℝ), (5892997793/10000000000 : ℝ), (-157023661/1250000000 : ℝ)] ![(8551356002901/20000000000000 : ℝ), (504266168589/1000000000000 : ℝ), (3408301558277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1296971783/2500000000 : ℝ)|^4499 ≤ (8551356002901/20000000000000 : ℝ)^3475
        have hw : |(1296971783/2500000000 : ℝ)|=(1296971783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5892997793/10000000000 : ℝ)|^4499 ≤ (504266168589/1000000000000 : ℝ)^3475
        have hw : |(5892997793/10000000000 : ℝ)|=(5892997793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-157023661/1250000000 : ℝ)|^4499 ≤ (3408301558277/50000000000000 : ℝ)^3475
        have hw : |(-157023661/1250000000 : ℝ)|=(157023661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s0_7 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2078129143/5000000000 : ℝ)*x 0 + (1359723759/2500000000 : ℝ)*x 1 + (12324311/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2078129143/5000000000 : ℝ)^4499 ≤ (32088041894327/100000000000000 : ℝ)^3475 := by
    have hnat : (2078129143 : ℕ)^4499*100000000000000^3475 ≤ 32088041894327^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078129143 5000000000 32088041894327 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359723759/2500000000 : ℝ)^4499 ≤ (45453983866223/100000000000000 : ℝ)^3475 := by
    have hnat : (1359723759 : ℕ)^4499*100000000000000^3475 ≤ 45453983866223^3475*2500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359723759 2500000000 45453983866223 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12324311/39062500 : ℝ)^4499 ≤ (22457974222721/100000000000000 : ℝ)^3475 := by
    have hnat : (12324311 : ℕ)^4499*100000000000000^3475 ≤ 22457974222721^3475*39062500^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12324311 39062500 22457974222721 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2078129143/5000000000 : ℝ), (1359723759/2500000000 : ℝ), (12324311/39062500 : ℝ)] ![(32088041894327/100000000000000 : ℝ), (45453983866223/100000000000000 : ℝ), (22457974222721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2078129143/5000000000 : ℝ)|^4499 ≤ (32088041894327/100000000000000 : ℝ)^3475
        have hw : |(2078129143/5000000000 : ℝ)|=(2078129143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359723759/2500000000 : ℝ)|^4499 ≤ (45453983866223/100000000000000 : ℝ)^3475
        have hw : |(1359723759/2500000000 : ℝ)|=(1359723759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(12324311/39062500 : ℝ)|^4499 ≤ (22457974222721/100000000000000 : ℝ)^3475
        have hw : |(12324311/39062500 : ℝ)|=(12324311/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1501_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1269539/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (537/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25627/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4497/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4497 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4497*1^1024 ≤ 0^1024*1^4497 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4497 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4497/1024 : ℝ) ≤ (1788158601621755377/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4497 ≤ (1788158601621755377/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4497*100000000000000000000^1024 ≤ 1788158601621755377^1024*5^4497 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1788158601621755377 100000000000000000000 4497 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1788158601621755377/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4497/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4497 := by
      have hnat : (1 : ℕ)^1024*1^4497 ≤ 1^4497*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4497 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101788158601621755377/100000000000000000000 : ℝ) ≤ (10040439469328441/10000000000000000 : ℝ) ^ (4497/1024 : ℝ) := by
    have hpowers : (101788158601621755377/100000000000000000000 : ℝ)^1024 ≤ (10040439469328441/10000000000000000 : ℝ)^4497 := by
      have hnat : (101788158601621755377 : ℕ)^1024*10000000000000000^4497 ≤ 10040439469328441^4497*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101788158601621755377 100000000000000000000 10040439469328441 10000000000000000 1024 4497 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10040439469328441/10000000000000000 : ℝ)) (X := (101788158601621755377/100000000000000000000 : ℝ)) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51788158601621755377/50000000000000000000 : ℝ) ≤ (5040439469328441/5000000000000000 : ℝ) ^ (4497/1024 : ℝ) := by
    have hpowers : (51788158601621755377/50000000000000000000 : ℝ)^1024 ≤ (5040439469328441/5000000000000000 : ℝ)^4497 := by
      have hnat : (51788158601621755377 : ℕ)^1024*5000000000000000^4497 ≤ 5040439469328441^4497*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51788158601621755377 50000000000000000000 5040439469328441 5000000000000000 1024 4497 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5040439469328441/5000000000000000 : ℝ)) (X := (51788158601621755377/50000000000000000000 : ℝ)) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(40439469328441/4000000000000000 : ℝ)*(0 : ℝ))^(4497/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(40439469328441/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1788158601621755377/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(40439469328441/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4497/1024 : ℝ) := by
    rw [show (1 : ℝ)+(40439469328441/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10040439469328441/10000000000000000 : ℝ) by norm_num, show 1+(1788158601621755377/100000000000000000000 : ℝ)+(0 : ℝ)=(101788158601621755377/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1788158601621755377/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(40439469328441/4000000000000000 : ℝ)*(2/5 : ℝ))^(4497/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(40439469328441/4000000000000000 : ℝ)*(2/5 : ℝ)=(5040439469328441/5000000000000000 : ℝ) by norm_num, show 1+2*(1788158601621755377/100000000000000000000 : ℝ)=(51788158601621755377/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(40439469328441/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4497/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (40439469328441/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(40439469328441/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4497/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (40439469328441/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(40439469328441/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4497/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (40439469328441/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-212195377/1250000000 : ℝ)*X 0 0+(5921348189/10000000000 : ℝ)*X 0 1+(2425292121/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5480377801/10000000000 : ℝ)*X 1 0+(-2298602903/10000000000 : ℝ)*X 1 1+(4850584191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((548037787/1000000000 : ℝ)*X 2 0+(2425292097/5000000000 : ℝ)*X 2 1+(-2298602809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((414812309/1000000000 : ℝ)*X 0 0+(3091234497/10000000000 : ℝ)*X 0 1+(5500474807/10000000000 : ℝ)*X 0 2+(414812309/1000000000 : ℝ)*X 1 0+(3091234497/10000000000 : ℝ)*X 1 1+(5500474807/10000000000 : ℝ)*X 1 2+(414812309/1000000000 : ℝ)*X 2 0+(3091234497/10000000000 : ℝ)*X 2 1+(5500474807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-425294631/2500000000 : ℝ)*X 0 0+(152436023/312500000 : ℝ)*X 0 1+(29464989/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1296971777/2500000000 : ℝ)*X 1 0+(-1256189231/10000000000 : ℝ)*X 1 1+(1473249463/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1296971783/2500000000 : ℝ)*X 2 0+(5892997793/10000000000 : ℝ)*X 2 1+(-157023661/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2078129143/5000000000 : ℝ)*X 0 0+(1359723759/2500000000 : ℝ)*X 0 1+(12324311/39062500 : ℝ)*X 0 2+(2078129143/5000000000 : ℝ)*X 1 0+(1359723759/2500000000 : ℝ)*X 1 1+(12324311/39062500 : ℝ)*X 1 2+(2078129143/5000000000 : ℝ)*X 2 0+(1359723759/2500000000 : ℝ)*X 2 1+(12324311/39062500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29030879766328947178503/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8717693/50000000000000 : ℝ)*(base1) + (27716201/5000000000000 : ℝ)*(base19) + (566082369/100000000000000 : ℝ)*(base23) + (55129367/100000000000000 : ℝ)*(upper3) + (42411871/50000000000000 : ℝ)*(upper5) + (168623364589339/25000000000000 : ℝ)*(major0) + (168623364589339/25000000000000 : ℝ)*(major1) + (168623364589339/25000000000000 : ℝ)*(major2) + (116739301313783/12500000000000 : ℝ)*(sp0) + (933915921369253/100000000000000 : ℝ)*(sp1) + (933915909610903/100000000000000 : ℝ)*(sp2) + (415069488029403/100000000000000 : ℝ)*(sp3) + (416523679/20000000000000 : ℝ)*(sp4) + (858140963/100000000000000 : ℝ)*(sp7) + (415070363605753/100000000000000 : ℝ)*(f.failure) + (933916475693273/100000000000000 : ℝ)*(f.sum) + (94118103890499/50000000000000000000000000000 : ℝ)*base65 + (379773520590499/100000000000000000000000000000 : ℝ)*base67 + (12382253609501/100000000000000000000000000000 : ℝ)*base70 + (211396343990499/100000000000000000000000000000 : ℝ)*base71 + (185103403090499/50000000000000000000000000000 : ℝ)*base73 + (208691097109501/100000000000000000000000000000 : ℝ)*base76 + (466719948290499/100000000000000000000000000000 : ℝ)*base77 + (725235863990499/100000000000000000000000000000 : ℝ)*base79 + (15414782990499/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (317133/78125000000000000000 : ℝ)*base90 + (317133/78125000000000000000 : ℝ)*base92 + (317133/78125000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (835861023334445679/250000000000000000000000 : ℝ) := by norm_num
    linear_combination (374723269/50000000000000 : ℝ)*(base19) + (189644921/25000000000000 : ℝ)*(base23) + (3131641/5000000000000 : ℝ)*(base32) + (113711067/100000000000000 : ℝ)*(upper3) + (74628787/100000000000000 : ℝ)*(upper5) + (711515344270179/100000000000000 : ℝ)*(major0) + (711515344270179/100000000000000 : ℝ)*(major1) + (711515344270179/100000000000000 : ℝ)*(major2) + (1911042787/100000000000000 : ℝ)*(sp1) + (996099427/50000000000000 : ℝ)*(sp2) + (492588826770977/50000000000000 : ℝ)*(sp4) + (985174993052629/100000000000000 : ℝ)*(sp5) + (123146862845427/12500000000000 : ℝ)*(sp6) + (437852860917443/100000000000000 : ℝ)*(sp7) + (437852923550263/100000000000000 : ℝ)*(f.failure) + (492588826770977/50000000000000 : ℝ)*(f.sum) + (371905032460939/200000000000000000000000000000 : ℝ)*base65 + (1254957243939061/400000000000000000000000000000 : ℝ)*base68 + (1045931642339061/400000000000000000000000000000 : ℝ)*base70 + (2246022013939061/400000000000000000000000000000 : ℝ)*base72 + (1279069595260939/200000000000000000000000000000 : ℝ)*base73 + (1620744452339061/400000000000000000000000000000 : ℝ)*base76 + (1852880243139061/400000000000000000000000000000 : ℝ)*base78 + (4455504611939061/400000000000000000000000000000 : ℝ)*base80 + (1157909354060939/200000000000000000000000000000 : ℝ)*base81 + (4993/78125000000000000000 : ℝ)*base90 + (4993/78125000000000000000 : ℝ)*base92 + (4993/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1501_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1269539/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (537/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25627/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1501_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1501_s1_0 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1854239367/10000000000 : ℝ)*x 0 + (5577929151/10000000000 : ℝ)*x 1 + (159167267/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1854239367/10000000000 : ℝ)^4499 ≤ (11285261637017/100000000000000 : ℝ)^3475 := by
    have hnat : (1854239367 : ℕ)^4499*100000000000000^3475 ≤ 11285261637017^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1854239367 10000000000 11285261637017 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5577929151/10000000000 : ℝ)^4499 ≤ (11740987146421/25000000000000 : ℝ)^3475 := by
    have hnat : (5577929151 : ℕ)^4499*25000000000000^3475 ≤ 11740987146421^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5577929151 10000000000 11740987146421 25000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (159167267/312500000 : ℝ)^4499 ≤ (41750789760851/100000000000000 : ℝ)^3475 := by
    have hnat : (159167267 : ℕ)^4499*100000000000000^3475 ≤ 41750789760851^3475*312500000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159167267 312500000 41750789760851 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1854239367/10000000000 : ℝ), (5577929151/10000000000 : ℝ), (159167267/312500000 : ℝ)] ![(11285261637017/100000000000000 : ℝ), (11740987146421/25000000000000 : ℝ), (41750789760851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1854239367/10000000000 : ℝ)|^4499 ≤ (11285261637017/100000000000000 : ℝ)^3475
        have hw : |(-1854239367/10000000000 : ℝ)|=(1854239367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5577929151/10000000000 : ℝ)|^4499 ≤ (11740987146421/25000000000000 : ℝ)^3475
        have hw : |(5577929151/10000000000 : ℝ)|=(5577929151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(159167267/312500000 : ℝ)|^4499 ≤ (41750789760851/100000000000000 : ℝ)^3475
        have hw : |(159167267/312500000 : ℝ)|=(159167267/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s1_1 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336789833/625000000 : ℝ)*x 0 + (-527438719/2500000000 : ℝ)*x 1 + (2546676543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336789833/625000000 : ℝ)^4499 ≤ (2806933964573/6250000000000 : ℝ)^3475 := by
    have hnat : (336789833 : ℕ)^4499*6250000000000^3475 ≤ 2806933964573^3475*625000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336789833 625000000 2806933964573 6250000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527438719/2500000000 : ℝ)^4499 ≤ (6669130523787/50000000000000 : ℝ)^3475 := by
    have hnat : (527438719 : ℕ)^4499*50000000000000^3475 ≤ 6669130523787^3475*2500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527438719 2500000000 6669130523787 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2546676543/5000000000 : ℝ)^4499 ≤ (8350159102577/20000000000000 : ℝ)^3475 := by
    have hnat : (2546676543 : ℕ)^4499*20000000000000^3475 ≤ 8350159102577^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2546676543 5000000000 8350159102577 20000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336789833/625000000 : ℝ), (-527438719/2500000000 : ℝ), (2546676543/5000000000 : ℝ)] ![(2806933964573/6250000000000 : ℝ), (6669130523787/50000000000000 : ℝ), (8350159102577/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336789833/625000000 : ℝ)|^4499 ≤ (2806933964573/6250000000000 : ℝ)^3475
        have hw : |(336789833/625000000 : ℝ)|=(336789833/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-527438719/2500000000 : ℝ)|^4499 ≤ (6669130523787/50000000000000 : ℝ)^3475
        have hw : |(-527438719/2500000000 : ℝ)|=(527438719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2546676543/5000000000 : ℝ)|^4499 ≤ (8350159102577/20000000000000 : ℝ)^3475
        have hw : |(2546676543/5000000000 : ℝ)|=(2546676543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s1_2 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1347159453/2500000000 : ℝ)*x 0 + (1018670559/2000000000 : ℝ)*x 1 + (-421950923/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347159453/2500000000 : ℝ)^4499 ≤ (11227737163921/25000000000000 : ℝ)^3475 := by
    have hnat : (1347159453 : ℕ)^4499*25000000000000^3475 ≤ 11227737163921^3475*2500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347159453 2500000000 11227737163921 25000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1018670559/2000000000 : ℝ)^4499 ≤ (5218849053077/12500000000000 : ℝ)^3475 := by
    have hnat : (1018670559 : ℕ)^4499*12500000000000^3475 ≤ 5218849053077^3475*2000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018670559 2000000000 5218849053077 12500000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (421950923/2000000000 : ℝ)^4499 ≤ (13338258911241/100000000000000 : ℝ)^3475 := by
    have hnat : (421950923 : ℕ)^4499*100000000000000^3475 ≤ 13338258911241^3475*2000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421950923 2000000000 13338258911241 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1347159453/2500000000 : ℝ), (1018670559/2000000000 : ℝ), (-421950923/2000000000 : ℝ)] ![(11227737163921/25000000000000 : ℝ), (5218849053077/12500000000000 : ℝ), (13338258911241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1347159453/2500000000 : ℝ)|^4499 ≤ (11227737163921/25000000000000 : ℝ)^3475
        have hw : |(1347159453/2500000000 : ℝ)|=(1347159453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1018670559/2000000000 : ℝ)|^4499 ≤ (5218849053077/12500000000000 : ℝ)^3475
        have hw : |(1018670559/2000000000 : ℝ)|=(1018670559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-421950923/2000000000 : ℝ)|^4499 ≤ (13338258911241/100000000000000 : ℝ)^3475
        have hw : |(-421950923/2000000000 : ℝ)|=(421950923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s1_3 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4253624559/10000000000 : ℝ)*x 0 + (1869117139/5000000000 : ℝ)*x 1 + (4828540591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4253624559/10000000000 : ℝ)^4499 ≤ (4133075172721/12500000000000 : ℝ)^3475 := by
    have hnat : (4253624559 : ℕ)^4499*12500000000000^3475 ≤ 4133075172721^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253624559 10000000000 4133075172721 12500000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1869117139/5000000000 : ℝ)^4499 ≤ (27973157004407/100000000000000 : ℝ)^3475 := by
    have hnat : (1869117139 : ℕ)^4499*100000000000000^3475 ≤ 27973157004407^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869117139 5000000000 27973157004407 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4828540591/10000000000 : ℝ)^4499 ≤ (38962241594433/100000000000000 : ℝ)^3475 := by
    have hnat : (4828540591 : ℕ)^4499*100000000000000^3475 ≤ 38962241594433^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4828540591 10000000000 38962241594433 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4253624559/10000000000 : ℝ), (1869117139/5000000000 : ℝ), (4828540591/10000000000 : ℝ)] ![(4133075172721/12500000000000 : ℝ), (27973157004407/100000000000000 : ℝ), (38962241594433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4253624559/10000000000 : ℝ)|^4499 ≤ (4133075172721/12500000000000 : ℝ)^3475
        have hw : |(4253624559/10000000000 : ℝ)|=(4253624559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1869117139/5000000000 : ℝ)|^4499 ≤ (27973157004407/100000000000000 : ℝ)^3475
        have hw : |(1869117139/5000000000 : ℝ)|=(1869117139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4828540591/10000000000 : ℝ)|^4499 ≤ (38962241594433/100000000000000 : ℝ)^3475
        have hw : |(4828540591/10000000000 : ℝ)|=(4828540591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s1_4 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-92728129/500000000 : ℝ)*x 0 + (2549428339/5000000000 : ℝ)*x 1 + (5572335141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (92728129/500000000 : ℝ)^4499 ≤ (11287808508277/100000000000000 : ℝ)^3475 := by
    have hnat : (92728129 : ℕ)^4499*100000000000000^3475 ≤ 11287808508277^3475*500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92728129 500000000 11287808508277 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2549428339/5000000000 : ℝ)^4499 ≤ (8361842455631/20000000000000 : ℝ)^3475 := by
    have hnat : (2549428339 : ℕ)^4499*20000000000000^3475 ≤ 8361842455631^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2549428339 5000000000 8361842455631 20000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5572335141/10000000000 : ℝ)^4499 ≤ (1465718099907/3125000000000 : ℝ)^3475 := by
    have hnat : (5572335141 : ℕ)^4499*3125000000000^3475 ≤ 1465718099907^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5572335141 10000000000 1465718099907 3125000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-92728129/500000000 : ℝ), (2549428339/5000000000 : ℝ), (5572335141/10000000000 : ℝ)] ![(11287808508277/100000000000000 : ℝ), (8361842455631/20000000000000 : ℝ), (1465718099907/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-92728129/500000000 : ℝ)|^4499 ≤ (11287808508277/100000000000000 : ℝ)^3475
        have hw : |(-92728129/500000000 : ℝ)|=(92728129/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2549428339/5000000000 : ℝ)|^4499 ≤ (8361842455631/20000000000000 : ℝ)^3475
        have hw : |(2549428339/5000000000 : ℝ)|=(2549428339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5572335141/10000000000 : ℝ)|^4499 ≤ (1465718099907/3125000000000 : ℝ)^3475
        have hw : |(5572335141/10000000000 : ℝ)|=(5572335141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s1_5 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657646803/1250000000 : ℝ)*x 0 + (-407693107/2500000000 : ℝ)*x 1 + (2786167637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657646803/1250000000 : ℝ)^4499 ≤ (43540397917451/100000000000000 : ℝ)^3475 := by
    have hnat : (657646803 : ℕ)^4499*100000000000000^3475 ≤ 43540397917451^3475*1250000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657646803 1250000000 43540397917451 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (407693107/2500000000 : ℝ)^4499 ≤ (9556621416691/100000000000000 : ℝ)^3475 := by
    have hnat : (407693107 : ℕ)^4499*100000000000000^3475 ≤ 9556621416691^3475*2500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407693107 2500000000 9556621416691 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2786167637/5000000000 : ℝ)^4499 ≤ (2931436290399/6250000000000 : ℝ)^3475 := by
    have hnat : (2786167637 : ℕ)^4499*6250000000000^3475 ≤ 2931436290399^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2786167637 5000000000 2931436290399 6250000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657646803/1250000000 : ℝ), (-407693107/2500000000 : ℝ), (2786167637/5000000000 : ℝ)] ![(43540397917451/100000000000000 : ℝ), (9556621416691/100000000000000 : ℝ), (2931436290399/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657646803/1250000000 : ℝ)|^4499 ≤ (43540397917451/100000000000000 : ℝ)^3475
        have hw : |(657646803/1250000000 : ℝ)|=(657646803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-407693107/2500000000 : ℝ)|^4499 ≤ (9556621416691/100000000000000 : ℝ)^3475
        have hw : |(-407693107/2500000000 : ℝ)|=(407693107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2786167637/5000000000 : ℝ)|^4499 ≤ (2931436290399/6250000000000 : ℝ)^3475
        have hw : |(2786167637/5000000000 : ℝ)|=(2786167637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s1_6 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5261174301/10000000000 : ℝ)*x 0 + (557233531/1000000000 : ℝ)*x 1 + (-1630772551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5261174301/10000000000 : ℝ)^4499 ≤ (43540396599571/100000000000000 : ℝ)^3475 := by
    have hnat : (5261174301 : ℕ)^4499*100000000000000^3475 ≤ 43540396599571^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261174301 10000000000 43540396599571 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (557233531/1000000000 : ℝ)^4499 ≤ (46902981038691/100000000000000 : ℝ)^3475 := by
    have hnat : (557233531 : ℕ)^4499*100000000000000^3475 ≤ 46902981038691^3475*1000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557233531 1000000000 46902981038691 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1630772551/10000000000 : ℝ)^4499 ≤ (9556622349897/100000000000000 : ℝ)^3475 := by
    have hnat : (1630772551 : ℕ)^4499*100000000000000^3475 ≤ 9556622349897^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1630772551 10000000000 9556622349897 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5261174301/10000000000 : ℝ), (557233531/1000000000 : ℝ), (-1630772551/10000000000 : ℝ)] ![(43540396599571/100000000000000 : ℝ), (46902981038691/100000000000000 : ℝ), (9556622349897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5261174301/10000000000 : ℝ)|^4499 ≤ (43540396599571/100000000000000 : ℝ)^3475
        have hw : |(5261174301/10000000000 : ℝ)|=(5261174301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(557233531/1000000000 : ℝ)|^4499 ≤ (46902981038691/100000000000000 : ℝ)^3475
        have hw : |(557233531/1000000000 : ℝ)|=(557233531/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1630772551/10000000000 : ℝ)|^4499 ≤ (9556622349897/100000000000000 : ℝ)^3475
        have hw : |(-1630772551/10000000000 : ℝ)|=(1630772551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s1_7 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4254352249/10000000000 : ℝ)*x 0 + (1204039341/2500000000 : ℝ)*x 1 + (37508203/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4254352249/10000000000 : ℝ)^4499 ≤ (33071924949017/100000000000000 : ℝ)^3475 := by
    have hnat : (4254352249 : ℕ)^4499*100000000000000^3475 ≤ 33071924949017^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254352249 10000000000 33071924949017 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1204039341/2500000000 : ℝ)^4499 ≤ (19416461818957/50000000000000 : ℝ)^3475 := by
    have hnat : (1204039341 : ℕ)^4499*50000000000000^3475 ≤ 19416461818957^3475*2500000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204039341 2500000000 19416461818957 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37508203/100000000 : ℝ)^4499 ≤ (5619030278453/20000000000000 : ℝ)^3475 := by
    have hnat : (37508203 : ℕ)^4499*20000000000000^3475 ≤ 5619030278453^3475*100000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37508203 100000000 5619030278453 20000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4254352249/10000000000 : ℝ), (1204039341/2500000000 : ℝ), (37508203/100000000 : ℝ)] ![(33071924949017/100000000000000 : ℝ), (19416461818957/50000000000000 : ℝ), (5619030278453/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4254352249/10000000000 : ℝ)|^4499 ≤ (33071924949017/100000000000000 : ℝ)^3475
        have hw : |(4254352249/10000000000 : ℝ)|=(4254352249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1204039341/2500000000 : ℝ)|^4499 ≤ (19416461818957/50000000000000 : ℝ)^3475
        have hw : |(1204039341/2500000000 : ℝ)|=(1204039341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(37508203/100000000 : ℝ)|^4499 ≤ (5619030278453/20000000000000 : ℝ)^3475
        have hw : |(37508203/100000000 : ℝ)|=(37508203/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1501_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1269539/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25627/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (537/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (4103/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9227/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25627/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (537/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25627/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (537/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25627/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (537/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25627/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (537/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25627/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (537/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25627/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (537/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (537/20000 : ℝ) ^ (4497/1024 : ℝ) ≤ (12605186897141/100000000000000000000 : ℝ) := by
    have hpowers : (537/20000 : ℝ)^4497 ≤ (12605186897141/100000000000000000000 : ℝ)^1024 := by
      have hnat : (537 : ℕ)^4497*100000000000000000000^1024 ≤ 12605186897141^1024*20000^4497 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        537 20000 12605186897141 100000000000000000000 4497 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (537/20000 : ℝ)) (X := (12605186897141/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25627/100000 : ℝ) ^ (4497/1024 : ℝ) ≤ (126533698479795883/50000000000000000000 : ℝ) := by
    have hpowers : (25627/100000 : ℝ)^4497 ≤ (126533698479795883/50000000000000000000 : ℝ)^1024 := by
      have hnat : (25627 : ℕ)^4497*50000000000000000000^1024 ≤ 126533698479795883^1024*100000^4497 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25627 100000 126533698479795883 50000000000000000000 4497 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25627/100000 : ℝ)) (X := (126533698479795883/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000012605186897141/50000000000000000000 : ℝ) ≤ (1250000071757339/1250000000000000 : ℝ) ^ (4497/1024 : ℝ) := by
    have hpowers : (50000012605186897141/50000000000000000000 : ℝ)^1024 ≤ (1250000071757339/1250000000000000 : ℝ)^4497 := by
      have hnat : (50000012605186897141 : ℕ)^1024*1250000000000000^4497 ≤ 1250000071757339^4497*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000012605186897141 50000000000000000000 1250000071757339 1250000000000000 1024 4497 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000071757339/1250000000000000 : ℝ)) (X := (50000012605186897141/50000000000000000000 : ℝ)) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100253080002146488907/100000000000000000000 : ℝ) ≤ (10005757194566467/10000000000000000 : ℝ) ^ (4497/1024 : ℝ) := by
    have hpowers : (100253080002146488907/100000000000000000000 : ℝ)^1024 ≤ (10005757194566467/10000000000000000 : ℝ)^4497 := by
      have hnat : (100253080002146488907 : ℕ)^1024*10000000000000000^4497 ≤ 10005757194566467^4497*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100253080002146488907 100000000000000000000 10005757194566467 10000000000000000 1024 4497 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005757194566467/10000000000000000 : ℝ)) (X := (100253080002146488907/100000000000000000000 : ℝ)) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25126533698479795883/25000000000000000000 : ℝ) ≤ (5005756907537111/5000000000000000 : ℝ) ^ (4497/1024 : ℝ) := by
    have hpowers : (25126533698479795883/25000000000000000000 : ℝ)^1024 ≤ (5005756907537111/5000000000000000 : ℝ)^4497 := by
      have hnat : (25126533698479795883 : ℕ)^1024*5000000000000000^4497 ≤ 5005756907537111^4497*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25126533698479795883 25000000000000000000 5005756907537111 5000000000000000 1024 4497 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005756907537111/5000000000000000 : ℝ)) (X := (25126533698479795883/25000000000000000000 : ℝ)) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12605186897141/100000000000000000000 : ℝ) ≤ ((114694550058964163177/114710000000000000000 : ℝ)+2*(1151324101551/458840000000000 : ℝ)*(537/20000 : ℝ))^(4497/1024 : ℝ) := by
    rw [show (114694550058964163177/114710000000000000000 : ℝ)+2*(1151324101551/458840000000000 : ℝ)*(537/20000 : ℝ)=(1250000071757339/1250000000000000 : ℝ) by norm_num, show 1+2*(12605186897141/100000000000000000000 : ℝ)=(50000012605186897141/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(126533698479795883/50000000000000000000 : ℝ)+(12605186897141/100000000000000000000 : ℝ) ≤ ((114694550058964163177/114710000000000000000 : ℝ)+(1151324101551/458840000000000 : ℝ)*((25627/100000 : ℝ)+(537/20000 : ℝ)))^(4497/1024 : ℝ) := by
    rw [show (114694550058964163177/114710000000000000000 : ℝ)+(1151324101551/458840000000000 : ℝ)*((25627/100000 : ℝ)+(537/20000 : ℝ))=(10005757194566467/10000000000000000 : ℝ) by norm_num, show 1+(126533698479795883/50000000000000000000 : ℝ)+(12605186897141/100000000000000000000 : ℝ)=(100253080002146488907/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(126533698479795883/50000000000000000000 : ℝ) ≤ ((114694550058964163177/114710000000000000000 : ℝ)+2*(1151324101551/458840000000000 : ℝ)*(25627/100000 : ℝ))^(4497/1024 : ℝ) := by
    rw [show (114694550058964163177/114710000000000000000 : ℝ)+2*(1151324101551/458840000000000 : ℝ)*(25627/100000 : ℝ)=(5005756907537111/5000000000000000 : ℝ) by norm_num, show 1+2*(126533698479795883/50000000000000000000 : ℝ)=(25126533698479795883/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (114694550058964163177/114710000000000000000 : ℝ)*(X 1 0+X 2 0)+(1151324101551/458840000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4497/1024 : ℝ)) (lo := (537/20000 : ℝ)) (hi := (25627/100000 : ℝ)) (c := (114694550058964163177/114710000000000000000 : ℝ)) (alpha := (1151324101551/458840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (114694550058964163177/114710000000000000000 : ℝ)*(X 0 1+X 2 1)+(1151324101551/458840000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4497/1024 : ℝ)) (lo := (537/20000 : ℝ)) (hi := (25627/100000 : ℝ)) (c := (114694550058964163177/114710000000000000000 : ℝ)) (alpha := (1151324101551/458840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (114694550058964163177/114710000000000000000 : ℝ)*(X 0 2+X 1 2)+(1151324101551/458840000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4497/1024 : ℝ)) (lo := (537/20000 : ℝ)) (hi := (25627/100000 : ℝ)) (c := (114694550058964163177/114710000000000000000 : ℝ)) (alpha := (1151324101551/458840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1854239367/10000000000 : ℝ)*X 0 0+(5577929151/10000000000 : ℝ)*X 0 1+(159167267/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((336789833/625000000 : ℝ)*X 1 0+(-527438719/2500000000 : ℝ)*X 1 1+(2546676543/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1347159453/2500000000 : ℝ)*X 2 0+(1018670559/2000000000 : ℝ)*X 2 1+(-421950923/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4253624559/10000000000 : ℝ)*X 0 0+(1869117139/5000000000 : ℝ)*X 0 1+(4828540591/10000000000 : ℝ)*X 0 2+(4253624559/10000000000 : ℝ)*X 1 0+(1869117139/5000000000 : ℝ)*X 1 1+(4828540591/10000000000 : ℝ)*X 1 2+(4253624559/10000000000 : ℝ)*X 2 0+(1869117139/5000000000 : ℝ)*X 2 1+(4828540591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-92728129/500000000 : ℝ)*X 0 0+(2549428339/5000000000 : ℝ)*X 0 1+(5572335141/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((657646803/1250000000 : ℝ)*X 1 0+(-407693107/2500000000 : ℝ)*X 1 1+(2786167637/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5261174301/10000000000 : ℝ)*X 2 0+(557233531/1000000000 : ℝ)*X 2 1+(-1630772551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4254352249/10000000000 : ℝ)*X 0 0+(1204039341/2500000000 : ℝ)*X 0 1+(37508203/100000000 : ℝ)*X 0 2+(4254352249/10000000000 : ℝ)*X 1 0+(1204039341/2500000000 : ℝ)*X 1 1+(37508203/100000000 : ℝ)*X 1 2+(4254352249/10000000000 : ℝ)*X 2 0+(1204039341/2500000000 : ℝ)*X 2 1+(37508203/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42468419477640664441746206301/5735500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (794040801/50000000000000 : ℝ)*(base19) + (1773250559/100000000000000 : ℝ)*(base23) + (114894019/100000000000000 : ℝ)*(upper3) + (50751/50000000000000 : ℝ)*(upper4) + (281294377/100000000000000 : ℝ)*(upper5) + (1490436335099443/100000000000000 : ℝ)*(major0) + (1490436335099443/100000000000000 : ℝ)*(major1) + (1490436335099443/100000000000000 : ℝ)*(major2) + (103183511349733/5000000000000 : ℝ)*(sp0) + (2063684843538423/100000000000000 : ℝ)*(sp1) + (1031842329184733/50000000000000 : ℝ)*(sp2) + (917179987850647/100000000000000 : ℝ)*(sp3) + (3240925073/20000000000000 : ℝ)*(sp4) + (6003912063/100000000000000 : ℝ)*(sp7) + (91718599176271/10000000000000 : ℝ)*(f.failure) + (82547457264801/4000000000000 : ℝ)*(f.sum) + (89167574467613/22942000000000000000000000000 : ℝ)*base65 + (42140080318509060411/11471000000000000000000000000000000 : ℝ)*base67 + (81672279576275060411/11471000000000000000000000000000000 : ℝ)*base69 + (101131508217613060411/11471000000000000000000000000000000 : ℝ)*base71 + (90056306022593/22942000000000000000000000000 : ℝ)*base73 + (3305196486092060411/11471000000000000000000000000000000 : ℝ)*base75 + (89961109810405060411/11471000000000000000000000000000000 : ℝ)*base77 + (21033597012369060411/11471000000000000000000000000000000 : ℝ)*base79 + (95478729464939/22942000000000000000000000000 : ℝ)*base81 + (37653/3906250000000000000 : ℝ)*base90 + (37653/3906250000000000000 : ℝ)*base92 + (37653/3906250000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54827591020792511574726174627/5735500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1821304203/100000000000000 : ℝ)*(base19) + (190140919/10000000000000 : ℝ)*(base23) + (260556409/100000000000000 : ℝ)*(upper3) + (54889319/100000000000000 : ℝ)*(lower4) + (20675569/12500000000000 : ℝ)*(upper5) + (1525348646214617/100000000000000 : ℝ)*(major0) + (1525348646214617/100000000000000 : ℝ)*(major1) + (1525348646214617/100000000000000 : ℝ)*(major2) + (1198261641/10000000000000 : ℝ)*(sp1) + (2604151143/20000000000000 : ℝ)*(sp2) + (16896212912223/800000000000 : ℝ)*(sp4) + (1056006405053631/50000000000000 : ℝ)*(sp5) + (2112011691862971/100000000000000 : ℝ)*(sp6) + (938670359756707/100000000000000 : ℝ)*(sp7) + (938670359756707/100000000000000 : ℝ)*(f.failure) + (16896212912223/800000000000 : ℝ)*(f.sum) + (120314732658539/22942000000000000000000000000 : ℝ)*base66 + (34339151365765691791/11471000000000000000000000000000000 : ℝ)*base68 + (27720474217167308209/11471000000000000000000000000000000 : ℝ)*base69 + (55407524258888691791/11471000000000000000000000000000000 : ℝ)*base72 + (60041200748017/22942000000000000000000000000 : ℝ)*base74 + (44034006502184308209/11471000000000000000000000000000000 : ℝ)*base75 + (66194672369181691791/11471000000000000000000000000000000 : ℝ)*base78 + (126914482467900691791/11471000000000000000000000000000000 : ℝ)*base80 + (96684426993499/22942000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (516823/78125000000000000000 : ℝ)*base89 + (516823/78125000000000000000 : ℝ)*base91 + (516823/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1501_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1269539/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25627/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (537/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4103/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9227/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1501_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1501_s2_0 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1880048229/10000000000 : ℝ)*x 0 + (5461527811/10000000000 : ℝ)*x 1 + (41544447/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1880048229/10000000000 : ℝ)^4499 ≤ (11489042178457/100000000000000 : ℝ)^3475 := by
    have hnat : (1880048229 : ℕ)^4499*100000000000000^3475 ≤ 11489042178457^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880048229 10000000000 11489042178457 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5461527811/10000000000 : ℝ)^4499 ≤ (22849508890147/50000000000000 : ℝ)^3475 := by
    have hnat : (5461527811 : ℕ)^4499*50000000000000^3475 ≤ 22849508890147^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461527811 10000000000 22849508890147 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41544447/80000000 : ℝ)^4499 ≤ (1712477600937/4000000000000 : ℝ)^3475 := by
    have hnat : (41544447 : ℕ)^4499*4000000000000^3475 ≤ 1712477600937^3475*80000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41544447 80000000 1712477600937 4000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1880048229/10000000000 : ℝ), (5461527811/10000000000 : ℝ), (41544447/80000000 : ℝ)] ![(11489042178457/100000000000000 : ℝ), (22849508890147/50000000000000 : ℝ), (1712477600937/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1880048229/10000000000 : ℝ)|^4499 ≤ (11489042178457/100000000000000 : ℝ)^3475
        have hw : |(-1880048229/10000000000 : ℝ)|=(1880048229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5461527811/10000000000 : ℝ)|^4499 ≤ (22849508890147/50000000000000 : ℝ)^3475
        have hw : |(5461527811/10000000000 : ℝ)|=(5461527811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41544447/80000000 : ℝ)|^4499 ≤ (1712477600937/4000000000000 : ℝ)^3475
        have hw : |(41544447/80000000 : ℝ)|=(41544447/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s2_1 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071832841/2000000000 : ℝ)*x 0 + (-1009172759/5000000000 : ℝ)*x 1 + (324565991/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071832841/2000000000 : ℝ)^4499 ≤ (44593175559067/100000000000000 : ℝ)^3475 := by
    have hnat : (1071832841 : ℕ)^4499*100000000000000^3475 ≤ 44593175559067^3475*2000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071832841 2000000000 44593175559067 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1009172759/5000000000 : ℝ)^4499 ≤ (12594884605467/100000000000000 : ℝ)^3475 := by
    have hnat : (1009172759 : ℕ)^4499*100000000000000^3475 ≤ 12594884605467^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009172759 5000000000 12594884605467 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (324565991/625000000 : ℝ)^4499 ≤ (4281193982063/10000000000000 : ℝ)^3475 := by
    have hnat : (324565991 : ℕ)^4499*10000000000000^3475 ≤ 4281193982063^3475*625000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324565991 625000000 4281193982063 10000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071832841/2000000000 : ℝ), (-1009172759/5000000000 : ℝ), (324565991/625000000 : ℝ)] ![(44593175559067/100000000000000 : ℝ), (12594884605467/100000000000000 : ℝ), (4281193982063/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071832841/2000000000 : ℝ)|^4499 ≤ (44593175559067/100000000000000 : ℝ)^3475
        have hw : |(1071832841/2000000000 : ℝ)|=(1071832841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1009172759/5000000000 : ℝ)|^4499 ≤ (12594884605467/100000000000000 : ℝ)^3475
        have hw : |(-1009172759/5000000000 : ℝ)|=(1009172759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(324565991/625000000 : ℝ)|^4499 ≤ (4281193982063/10000000000000 : ℝ)^3475
        have hw : |(324565991/625000000 : ℝ)|=(324565991/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s2_2 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53591641/100000000 : ℝ)*x 0 + (5193055917/10000000000 : ℝ)*x 1 + (-2018345577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53591641/100000000 : ℝ)^4499 ≤ (5574146803489/12500000000000 : ℝ)^3475 := by
    have hnat : (53591641 : ℕ)^4499*12500000000000^3475 ≤ 5574146803489^3475*100000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53591641 100000000 5574146803489 12500000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5193055917/10000000000 : ℝ)^4499 ≤ (10702985117927/25000000000000 : ℝ)^3475 := by
    have hnat : (5193055917 : ℕ)^4499*25000000000000^3475 ≤ 10702985117927^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193055917 10000000000 10702985117927 25000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2018345577/10000000000 : ℝ)^4499 ≤ (1259488508213/10000000000000 : ℝ)^3475 := by
    have hnat : (2018345577 : ℕ)^4499*10000000000000^3475 ≤ 1259488508213^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018345577 10000000000 1259488508213 10000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53591641/100000000 : ℝ), (5193055917/10000000000 : ℝ), (-2018345577/10000000000 : ℝ)] ![(5574146803489/12500000000000 : ℝ), (10702985117927/25000000000000 : ℝ), (1259488508213/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53591641/100000000 : ℝ)|^4499 ≤ (5574146803489/12500000000000 : ℝ)^3475
        have hw : |(53591641/100000000 : ℝ)|=(53591641/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5193055917/10000000000 : ℝ)|^4499 ≤ (10702985117927/25000000000000 : ℝ)^3475
        have hw : |(5193055917/10000000000 : ℝ)|=(5193055917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2018345577/10000000000 : ℝ)|^4499 ≤ (1259488508213/10000000000000 : ℝ)^3475
        have hw : |(-2018345577/10000000000 : ℝ)|=(2018345577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s2_3 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2136057727/5000000000 : ℝ)*x 0 + (1989610231/5000000000 : ℝ)*x 1 + (572910871/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136057727/5000000000 : ℝ)^4499 ≤ (33250810542597/100000000000000 : ℝ)^3475 := by
    have hnat : (2136057727 : ℕ)^4499*100000000000000^3475 ≤ 33250810542597^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136057727 5000000000 33250810542597 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989610231/5000000000 : ℝ)^4499 ≤ (7582422533219/25000000000000 : ℝ)^3475 := by
    have hnat : (1989610231 : ℕ)^4499*25000000000000^3475 ≤ 7582422533219^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989610231 5000000000 7582422533219 25000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (572910871/1250000000 : ℝ)^4499 ≤ (18209749648341/50000000000000 : ℝ)^3475 := by
    have hnat : (572910871 : ℕ)^4499*50000000000000^3475 ≤ 18209749648341^3475*1250000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572910871 1250000000 18209749648341 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2136057727/5000000000 : ℝ), (1989610231/5000000000 : ℝ), (572910871/1250000000 : ℝ)] ![(33250810542597/100000000000000 : ℝ), (7582422533219/25000000000000 : ℝ), (18209749648341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2136057727/5000000000 : ℝ)|^4499 ≤ (33250810542597/100000000000000 : ℝ)^3475
        have hw : |(2136057727/5000000000 : ℝ)|=(2136057727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1989610231/5000000000 : ℝ)|^4499 ≤ (7582422533219/25000000000000 : ℝ)^3475
        have hw : |(1989610231/5000000000 : ℝ)|=(1989610231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(572910871/1250000000 : ℝ)|^4499 ≤ (18209749648341/50000000000000 : ℝ)^3475
        have hw : |(572910871/1250000000 : ℝ)|=(572910871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s2_4 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-117506403/625000000 : ℝ)*x 0 + (2597377797/5000000000 : ℝ)*x 1 + (2729906697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (117506403/625000000 : ℝ)^4499 ≤ (11489471150873/100000000000000 : ℝ)^3475 := by
    have hnat : (117506403 : ℕ)^4499*100000000000000^3475 ≤ 11489471150873^3475*625000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117506403 625000000 11489471150873 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2597377797/5000000000 : ℝ)^4499 ≤ (669220042063/1562500000000 : ℝ)^3475 := by
    have hnat : (2597377797 : ℕ)^4499*1562500000000^3475 ≤ 669220042063^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597377797 5000000000 669220042063 1562500000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729906697/5000000000 : ℝ)^4499 ≤ (45680446139433/100000000000000 : ℝ)^3475 := by
    have hnat : (2729906697 : ℕ)^4499*100000000000000^3475 ≤ 45680446139433^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729906697 5000000000 45680446139433 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-117506403/625000000 : ℝ), (2597377797/5000000000 : ℝ), (2729906697/5000000000 : ℝ)] ![(11489471150873/100000000000000 : ℝ), (669220042063/1562500000000 : ℝ), (45680446139433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-117506403/625000000 : ℝ)|^4499 ≤ (11489471150873/100000000000000 : ℝ)^3475
        have hw : |(-117506403/625000000 : ℝ)|=(117506403/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2597377797/5000000000 : ℝ)|^4499 ≤ (669220042063/1562500000000 : ℝ)^3475
        have hw : |(2597377797/5000000000 : ℝ)|=(2597377797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729906697/5000000000 : ℝ)|^4499 ≤ (45680446139433/100000000000000 : ℝ)^3475
        have hw : |(2729906697/5000000000 : ℝ)|=(2729906697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s2_5 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661098417/1250000000 : ℝ)*x 0 + (-1751585393/10000000000 : ℝ)*x 1 + (5459813357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661098417/1250000000 : ℝ)^4499 ≤ (43836484263867/100000000000000 : ℝ)^3475 := by
    have hnat : (661098417 : ℕ)^4499*100000000000000^3475 ≤ 43836484263867^3475*1250000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661098417 1250000000 43836484263867 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1751585393/10000000000 : ℝ)^4499 ≤ (10483069981277/100000000000000 : ℝ)^3475 := by
    have hnat : (1751585393 : ℕ)^4499*100000000000000^3475 ≤ 10483069981277^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1751585393 10000000000 10483069981277 100000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459813357/10000000000 : ℝ)^4499 ≤ (11420111434661/25000000000000 : ℝ)^3475 := by
    have hnat : (5459813357 : ℕ)^4499*25000000000000^3475 ≤ 11420111434661^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459813357 10000000000 11420111434661 25000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661098417/1250000000 : ℝ), (-1751585393/10000000000 : ℝ), (5459813357/10000000000 : ℝ)] ![(43836484263867/100000000000000 : ℝ), (10483069981277/100000000000000 : ℝ), (11420111434661/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661098417/1250000000 : ℝ)|^4499 ≤ (43836484263867/100000000000000 : ℝ)^3475
        have hw : |(661098417/1250000000 : ℝ)|=(661098417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1751585393/10000000000 : ℝ)|^4499 ≤ (10483069981277/100000000000000 : ℝ)^3475
        have hw : |(-1751585393/10000000000 : ℝ)|=(1751585393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459813357/10000000000 : ℝ)|^4499 ≤ (11420111434661/25000000000000 : ℝ)^3475
        have hw : |(5459813357/10000000000 : ℝ)|=(5459813357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s2_6 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644392651/5000000000 : ℝ)*x 0 + (5459813337/10000000000 : ℝ)*x 1 + (-1751588239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644392651/5000000000 : ℝ)^4499 ≤ (5479557804623/12500000000000 : ℝ)^3475 := by
    have hnat : (2644392651 : ℕ)^4499*12500000000000^3475 ≤ 5479557804623^3475*5000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644392651 5000000000 5479557804623 12500000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5459813337/10000000000 : ℝ)^4499 ≤ (22840222761001/50000000000000 : ℝ)^3475 := by
    have hnat : (5459813337 : ℕ)^4499*50000000000000^3475 ≤ 22840222761001^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459813337 10000000000 22840222761001 50000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1751588239/10000000000 : ℝ)^4499 ≤ (209661840671/2000000000000 : ℝ)^3475 := by
    have hnat : (1751588239 : ℕ)^4499*2000000000000^3475 ≤ 209661840671^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1751588239 10000000000 209661840671 2000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644392651/5000000000 : ℝ), (5459813337/10000000000 : ℝ), (-1751588239/10000000000 : ℝ)] ![(5479557804623/12500000000000 : ℝ), (22840222761001/50000000000000 : ℝ), (209661840671/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644392651/5000000000 : ℝ)|^4499 ≤ (5479557804623/12500000000000 : ℝ)^3475
        have hw : |(2644392651/5000000000 : ℝ)|=(2644392651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5459813337/10000000000 : ℝ)|^4499 ≤ (22840222761001/50000000000000 : ℝ)^3475
        have hw : |(5459813337/10000000000 : ℝ)|=(5459813337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1751588239/10000000000 : ℝ)|^4499 ≤ (209661840671/2000000000000 : ℝ)^3475
        have hw : |(-1751588239/10000000000 : ℝ)|=(1751588239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1501_s2_7 (p : ℝ) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4272239207/10000000000 : ℝ)*x 0 + (4579466079/10000000000 : ℝ)*x 1 + (398307643/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4272239207/10000000000 : ℝ)^4499 ≤ (6650411515167/20000000000000 : ℝ)^3475 := by
    have hnat : (4272239207 : ℕ)^4499*20000000000000^3475 ≤ 6650411515167^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4272239207 10000000000 6650411515167 20000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4579466079/10000000000 : ℝ)^4499 ≤ (9095048995733/25000000000000 : ℝ)^3475 := by
    have hnat : (4579466079 : ℕ)^4499*25000000000000^3475 ≤ 9095048995733^3475*10000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4579466079 10000000000 9095048995733 25000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398307643/1000000000 : ℝ)^4499 ≤ (607354928663/2000000000000 : ℝ)^3475 := by
    have hnat : (398307643 : ℕ)^4499*2000000000000^3475 ≤ 607354928663^3475*1000000000^4499 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398307643 1000000000 607354928663 2000000000000 4499 3475 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4499/1024 : ℝ)) 4499 3475 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4272239207/10000000000 : ℝ), (4579466079/10000000000 : ℝ), (398307643/1000000000 : ℝ)] ![(6650411515167/20000000000000 : ℝ), (9095048995733/25000000000000 : ℝ), (607354928663/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4272239207/10000000000 : ℝ)|^4499 ≤ (6650411515167/20000000000000 : ℝ)^3475
        have hw : |(4272239207/10000000000 : ℝ)|=(4272239207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4579466079/10000000000 : ℝ)|^4499 ≤ (9095048995733/25000000000000 : ℝ)^3475
        have hw : |(4579466079/10000000000 : ℝ)|=(4579466079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(398307643/1000000000 : ℝ)|^4499 ≤ (607354928663/2000000000000 : ℝ)^3475
        have hw : |(398307643/1000000000 : ℝ)|=(398307643/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1501_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1269539/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9227/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4103/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5179/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (401/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9227/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4103/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9227/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4103/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9227/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4103/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9227/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4103/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9227/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4103/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9227/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4103/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4103/50000 : ℝ) ^ (4497/1024 : ℝ) ≤ (340665575380121/20000000000000000000 : ℝ) := by
    have hpowers : (4103/50000 : ℝ)^4497 ≤ (340665575380121/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4103 : ℕ)^4497*20000000000000000000^1024 ≤ 340665575380121^1024*50000^4497 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4103 50000 340665575380121 20000000000000000000 4497 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4103/50000 : ℝ)) (X := (340665575380121/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9227/50000 : ℝ) ^ (4497/1024 : ℝ) ≤ (59835918853833431/100000000000000000000 : ℝ) := by
    have hpowers : (9227/50000 : ℝ)^4497 ≤ (59835918853833431/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9227 : ℕ)^4497*100000000000000000000^1024 ≤ 59835918853833431^1024*50000^4497 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9227 50000 59835918853833431 100000000000000000000 4497 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9227/50000 : ℝ)) (X := (59835918853833431/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000340665575380121/10000000000000000000 : ℝ) ≤ (2500019392759639/2500000000000000 : ℝ) ^ (4497/1024 : ℝ) := by
    have hpowers : (10000340665575380121/10000000000000000000 : ℝ)^1024 ≤ (2500019392759639/2500000000000000 : ℝ)^4497 := by
      have hnat : (10000340665575380121 : ℕ)^1024*2500000000000000^4497 ≤ 2500019392759639^4497*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000340665575380121 10000000000000000000 2500019392759639 2500000000000000 1024 4497 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500019392759639/2500000000000000 : ℝ)) (X := (10000340665575380121/10000000000000000000 : ℝ)) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25015384811682683509/25000000000000000000 : ℝ) ≤ (5000700480536583/5000000000000000 : ℝ) ^ (4497/1024 : ℝ) := by
    have hpowers : (25015384811682683509/25000000000000000000 : ℝ)^1024 ≤ (5000700480536583/5000000000000000 : ℝ)^4497 := by
      have hnat : (25015384811682683509 : ℕ)^1024*5000000000000000^4497 ≤ 5000700480536583^4497*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015384811682683509 25000000000000000000 5000700480536583 5000000000000000 1024 4497 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000700480536583/5000000000000000 : ℝ)) (X := (25015384811682683509/25000000000000000000 : ℝ)) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50059835918853833431/50000000000000000000 : ℝ) ≤ (156292567986059/156250000000000 : ℝ) ^ (4497/1024 : ℝ) := by
    have hpowers : (50059835918853833431/50000000000000000000 : ℝ)^1024 ≤ (156292567986059/156250000000000 : ℝ)^4497 := by
      have hnat : (50059835918853833431 : ℕ)^1024*156250000000000^4497 ≤ 156292567986059^4497*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50059835918853833431 50000000000000000000 156292567986059 156250000000000 1024 4497 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156292567986059/156250000000000 : ℝ)) (X := (50059835918853833431/50000000000000000000 : ℝ)) (by norm_num) 4497 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(340665575380121/20000000000000000000 : ℝ) ≤ ((1829626347692055403/1830000000000000000 : ℝ)+2*(18905571923/14640000000000 : ℝ)*(4103/50000 : ℝ))^(4497/1024 : ℝ) := by
    rw [show (1829626347692055403/1830000000000000000 : ℝ)+2*(18905571923/14640000000000 : ℝ)*(4103/50000 : ℝ)=(2500019392759639/2500000000000000 : ℝ) by norm_num, show 1+2*(340665575380121/20000000000000000000 : ℝ)=(10000340665575380121/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(59835918853833431/100000000000000000000 : ℝ)+(340665575380121/20000000000000000000 : ℝ) ≤ ((1829626347692055403/1830000000000000000 : ℝ)+(18905571923/14640000000000 : ℝ)*((9227/50000 : ℝ)+(4103/50000 : ℝ)))^(4497/1024 : ℝ) := by
    rw [show (1829626347692055403/1830000000000000000 : ℝ)+(18905571923/14640000000000 : ℝ)*((9227/50000 : ℝ)+(4103/50000 : ℝ))=(5000700480536583/5000000000000000 : ℝ) by norm_num, show 1+(59835918853833431/100000000000000000000 : ℝ)+(340665575380121/20000000000000000000 : ℝ)=(25015384811682683509/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(59835918853833431/100000000000000000000 : ℝ) ≤ ((1829626347692055403/1830000000000000000 : ℝ)+2*(18905571923/14640000000000 : ℝ)*(9227/50000 : ℝ))^(4497/1024 : ℝ) := by
    rw [show (1829626347692055403/1830000000000000000 : ℝ)+2*(18905571923/14640000000000 : ℝ)*(9227/50000 : ℝ)=(156292567986059/156250000000000 : ℝ) by norm_num, show 1+2*(59835918853833431/100000000000000000000 : ℝ)=(50059835918853833431/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1829626347692055403/1830000000000000000 : ℝ)*(X 1 0+X 2 0)+(18905571923/14640000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4497/1024 : ℝ)) (lo := (4103/50000 : ℝ)) (hi := (9227/50000 : ℝ)) (c := (1829626347692055403/1830000000000000000 : ℝ)) (alpha := (18905571923/14640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1829626347692055403/1830000000000000000 : ℝ)*(X 0 1+X 2 1)+(18905571923/14640000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4497/1024 : ℝ)) (lo := (4103/50000 : ℝ)) (hi := (9227/50000 : ℝ)) (c := (1829626347692055403/1830000000000000000 : ℝ)) (alpha := (18905571923/14640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1829626347692055403/1830000000000000000 : ℝ)*(X 0 2+X 1 2)+(18905571923/14640000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4497/1024 : ℝ)) (lo := (4103/50000 : ℝ)) (hi := (9227/50000 : ℝ)) (c := (1829626347692055403/1830000000000000000 : ℝ)) (alpha := (18905571923/14640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1880048229/10000000000 : ℝ)*X 0 0+(5461527811/10000000000 : ℝ)*X 0 1+(41544447/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071832841/2000000000 : ℝ)*X 1 0+(-1009172759/5000000000 : ℝ)*X 1 1+(324565991/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53591641/100000000 : ℝ)*X 2 0+(5193055917/10000000000 : ℝ)*X 2 1+(-2018345577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2136057727/5000000000 : ℝ)*X 0 0+(1989610231/5000000000 : ℝ)*X 0 1+(572910871/1250000000 : ℝ)*X 0 2+(2136057727/5000000000 : ℝ)*X 1 0+(1989610231/5000000000 : ℝ)*X 1 1+(572910871/1250000000 : ℝ)*X 1 2+(2136057727/5000000000 : ℝ)*X 2 0+(1989610231/5000000000 : ℝ)*X 2 1+(572910871/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-117506403/625000000 : ℝ)*X 0 0+(2597377797/5000000000 : ℝ)*X 0 1+(2729906697/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661098417/1250000000 : ℝ)*X 1 0+(-1751585393/10000000000 : ℝ)*X 1 1+(5459813357/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644392651/5000000000 : ℝ)*X 2 0+(5459813337/10000000000 : ℝ)*X 2 1+(-1751588239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4272239207/10000000000 : ℝ)*X 0 0+(4579466079/10000000000 : ℝ)*X 0 1+(398307643/1000000000 : ℝ)*X 0 2+(4272239207/10000000000 : ℝ)*X 1 0+(4579466079/10000000000 : ℝ)*X 1 1+(398307643/1000000000 : ℝ)*X 1 2+(4272239207/10000000000 : ℝ)*X 2 0+(4579466079/10000000000 : ℝ)*X 2 1+(398307643/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1501_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (140098597329855098196875463/15250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1767930559/100000000000000 : ℝ)*(base19) + (393339027/25000000000000 : ℝ)*(base23) + (4072809/6250000000000 : ℝ)*(lower2) + (16774621/6250000000000 : ℝ)*(upper3) + (113008881/100000000000000 : ℝ)*(upper5) + (1345073977295979/50000000000000 : ℝ)*(major0) + (1345073977295979/50000000000000 : ℝ)*(major1) + (1345073977295979/50000000000000 : ℝ)*(major2) + (465601064161021/12500000000000 : ℝ)*(sp0) + (3724828276643143/100000000000000 : ℝ)*(sp1) + (1862414235608797/50000000000000 : ℝ)*(sp2) + (827727682369571/50000000000000 : ℝ)*(sp3) + (10765642767/50000000000000 : ℝ)*(sp4) + (10193644623/100000000000000 : ℝ)*(sp7) + (827732779191883/50000000000000 : ℝ)*(f.failure) + (1862415022286851/50000000000000 : ℝ)*(f.sum) + (164639020089/122000000000000000000000000 : ℝ)*base65 + (196804188649416821/30500000000000000000000000000000 : ℝ)*base68 + (216675695802083179/30500000000000000000000000000000 : ℝ)*base69 + (233259643741083179/30500000000000000000000000000000 : ℝ)*base71 + (119369456919/24400000000000000000000000 : ℝ)*base74 + (9081532436083179/30500000000000000000000000000000 : ℝ)*base75 + (125628831648583179/30500000000000000000000000000000 : ℝ)*base77 + (25064369396416821/30500000000000000000000000000000 : ℝ)*base80 + (687486748363/122000000000000000000000000 : ℝ)*base81 + (358187/39062500000000000000 : ℝ)*base89 + (358187/39062500000000000000 : ℝ)*base91 + (358187/39062500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (259823028084909522690349533/30500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2940340153/100000000000000 : ℝ)*(base19) + (427718529/25000000000000 : ℝ)*(base23) + (177988023/50000000000000 : ℝ)*(lower4) + (79965819/100000000000000 : ℝ)*(lower5) + (2724753948687763/100000000000000 : ℝ)*(major0) + (2724753948687763/100000000000000 : ℝ)*(major1) + (2724753948687763/100000000000000 : ℝ)*(major2) + (49521012251/100000000000000 : ℝ)*(sp1) + (3895886367/25000000000000 : ℝ)*(sp2) + (258045361/5000000000000 : ℝ)*(sp3) + (1886373094334291/50000000000000 : ℝ)*(sp4) + (1886346863658089/50000000000000 : ℝ)*(sp5) + (1886364447124499/50000000000000 : ℝ)*(sp6) + (41918906596003/2500000000000 : ℝ)*(sp7) + (1676761424747341/100000000000000 : ℝ)*(f.failure) + (1886373094334291/50000000000000 : ℝ)*(f.sum) + (3547674721961/732000000000000000000000000 : ℝ)*base65 + (1393027794401258489/183000000000000000000000000000000 : ℝ)*base67 + (2251353602081258489/183000000000000000000000000000000 : ℝ)*base69 + (1981850945036258489/183000000000000000000000000000000 : ℝ)*base71 + (1619863297913/732000000000000000000000000 : ℝ)*base73 + (1431642782879258489/183000000000000000000000000000000 : ℝ)*base75 + (998421950297258489/183000000000000000000000000000000 : ℝ)*base77 + (2022790676759258489/183000000000000000000000000000000 : ℝ)*base79 + (503685268957/146400000000000000000000000 : ℝ)*base81 + (297951/78125000000000000000 : ℝ)*base90 + (297951/78125000000000000000 : ℝ)*base92 + (297951/78125000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1501_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1269539/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9227/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4103/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5179/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (401/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1501_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1501_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1269539/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5179/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (401/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1501_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1501_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1501_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4497/1024 : ℝ) ≤ p) (hpb : p ≤ (4499/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1269539/781250 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5179/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (401/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1501_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
