-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1506_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:54:16.977002+00:00
-- url     : https://prove2.me/submissions/d593a7dc-b258-4e45-bc63-cfd82236817d

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
theorem support_rectangle_w1506_s6_0 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1876917239/10000000000 : ℝ)*x 0 + (1358503461/2500000000 : ℝ)*x 1 + (13043323/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1876917239/10000000000 : ℝ)^4509 ≤ (358765782019/3125000000000 : ℝ)^3485 := by
    have hnat : (1876917239 : ℕ)^4509*3125000000000^3485 ≤ 358765782019^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876917239 10000000000 358765782019 3125000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358503461/2500000000 : ℝ)^4509 ≤ (45424596841551/100000000000000 : ℝ)^3485 := by
    have hnat : (1358503461 : ℕ)^4509*100000000000000^3485 ≤ 45424596841551^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358503461 2500000000 45424596841551 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13043323/25000000 : ℝ)^4509 ≤ (5386862264511/12500000000000 : ℝ)^3485 := by
    have hnat : (13043323 : ℕ)^4509*12500000000000^3485 ≤ 5386862264511^3485*25000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13043323 25000000 5386862264511 12500000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1876917239/10000000000 : ℝ), (1358503461/2500000000 : ℝ), (13043323/25000000 : ℝ)] ![(358765782019/3125000000000 : ℝ), (45424596841551/100000000000000 : ℝ), (5386862264511/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1876917239/10000000000 : ℝ)|^4509 ≤ (358765782019/3125000000000 : ℝ)^3485
        have hw : |(-1876917239/10000000000 : ℝ)|=(1876917239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358503461/2500000000 : ℝ)|^4509 ≤ (45424596841551/100000000000000 : ℝ)^3485
        have hw : |(1358503461/2500000000 : ℝ)|=(1358503461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13043323/25000000 : ℝ)|^4509 ≤ (5386862264511/12500000000000 : ℝ)^3485
        have hw : |(13043323/25000000 : ℝ)|=(13043323/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s6_1 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334495131/625000000 : ℝ)*x 0 + (-496976541/2500000000 : ℝ)*x 1 + (13043323/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334495131/625000000 : ℝ)^4509 ≤ (11134677183237/25000000000000 : ℝ)^3485 := by
    have hnat : (334495131 : ℕ)^4509*25000000000000^3485 ≤ 11134677183237^3485*625000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334495131 625000000 11134677183237 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (496976541/2500000000 : ℝ)^4509 ≤ (123663931287/1000000000000 : ℝ)^3485 := by
    have hnat : (496976541 : ℕ)^4509*1000000000000^3485 ≤ 123663931287^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496976541 2500000000 123663931287 1000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13043323/25000000 : ℝ)^4509 ≤ (5386862264511/12500000000000 : ℝ)^3485 := by
    have hnat : (13043323 : ℕ)^4509*12500000000000^3485 ≤ 5386862264511^3485*25000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13043323 25000000 5386862264511 12500000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334495131/625000000 : ℝ), (-496976541/2500000000 : ℝ), (13043323/25000000 : ℝ)] ![(11134677183237/25000000000000 : ℝ), (123663931287/1000000000000 : ℝ), (5386862264511/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334495131/625000000 : ℝ)|^4509 ≤ (11134677183237/25000000000000 : ℝ)^3485
        have hw : |(334495131/625000000 : ℝ)|=(334495131/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-496976541/2500000000 : ℝ)|^4509 ≤ (123663931287/1000000000000 : ℝ)^3485
        have hw : |(-496976541/2500000000 : ℝ)|=(496976541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13043323/25000000 : ℝ)|^4509 ≤ (5386862264511/12500000000000 : ℝ)^3485
        have hw : |(13043323/25000000 : ℝ)|=(13043323/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s6_2 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334495131/625000000 : ℝ)*x 0 + (13043323/25000000 : ℝ)*x 1 + (-496976541/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334495131/625000000 : ℝ)^4509 ≤ (11134677183237/25000000000000 : ℝ)^3485 := by
    have hnat : (334495131 : ℕ)^4509*25000000000000^3485 ≤ 11134677183237^3485*625000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334495131 625000000 11134677183237 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13043323/25000000 : ℝ)^4509 ≤ (5386862264511/12500000000000 : ℝ)^3485 := by
    have hnat : (13043323 : ℕ)^4509*12500000000000^3485 ≤ 5386862264511^3485*25000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13043323 25000000 5386862264511 12500000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (496976541/2500000000 : ℝ)^4509 ≤ (123663931287/1000000000000 : ℝ)^3485 := by
    have hnat : (496976541 : ℕ)^4509*1000000000000^3485 ≤ 123663931287^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496976541 2500000000 123663931287 1000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334495131/625000000 : ℝ), (13043323/25000000 : ℝ), (-496976541/2500000000 : ℝ)] ![(11134677183237/25000000000000 : ℝ), (5386862264511/12500000000000 : ℝ), (123663931287/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334495131/625000000 : ℝ)|^4509 ≤ (11134677183237/25000000000000 : ℝ)^3485
        have hw : |(334495131/625000000 : ℝ)|=(334495131/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13043323/25000000 : ℝ)|^4509 ≤ (5386862264511/12500000000000 : ℝ)^3485
        have hw : |(13043323/25000000 : ℝ)|=(13043323/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-496976541/2500000000 : ℝ)|^4509 ≤ (123663931287/1000000000000 : ℝ)^3485
        have hw : |(-496976541/2500000000 : ℝ)|=(496976541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s6_3 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2136287333/5000000000 : ℝ)*x 0 + (806782719/2000000000 : ℝ)*x 1 + (4523187803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136287333/5000000000 : ℝ)^4509 ≤ (2079959898401/6250000000000 : ℝ)^3485 := by
    have hnat : (2136287333 : ℕ)^4509*6250000000000^3485 ≤ 2079959898401^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136287333 5000000000 2079959898401 6250000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (806782719/2000000000 : ℝ)^4509 ≤ (7723550089647/25000000000000 : ℝ)^3485 := by
    have hnat : (806782719 : ℕ)^4509*25000000000000^3485 ≤ 7723550089647^3485*2000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806782719 2000000000 7723550089647 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4523187803/10000000000 : ℝ)^4509 ≤ (35826441251961/100000000000000 : ℝ)^3485 := by
    have hnat : (4523187803 : ℕ)^4509*100000000000000^3485 ≤ 35826441251961^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523187803 10000000000 35826441251961 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2136287333/5000000000 : ℝ), (806782719/2000000000 : ℝ), (4523187803/10000000000 : ℝ)] ![(2079959898401/6250000000000 : ℝ), (7723550089647/25000000000000 : ℝ), (35826441251961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2136287333/5000000000 : ℝ)|^4509 ≤ (2079959898401/6250000000000 : ℝ)^3485
        have hw : |(2136287333/5000000000 : ℝ)|=(2136287333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(806782719/2000000000 : ℝ)|^4509 ≤ (7723550089647/25000000000000 : ℝ)^3485
        have hw : |(806782719/2000000000 : ℝ)|=(806782719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4523187803/10000000000 : ℝ)|^4509 ≤ (35826441251961/100000000000000 : ℝ)^3485
        have hw : |(4523187803/10000000000 : ℝ)|=(4523187803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s6_4 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1876947841/10000000000 : ℝ)*x 0 + (1043688537/2000000000 : ℝ)*x 1 + (5432891133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1876947841/10000000000 : ℝ)^4509 ≤ (5740373603949/50000000000000 : ℝ)^3485 := by
    have hnat : (1876947841 : ℕ)^4509*50000000000000^3485 ≤ 5740373603949^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876947841 10000000000 5740373603949 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043688537/2000000000 : ℝ)^4509 ≤ (2155339914157/5000000000000 : ℝ)^3485 := by
    have hnat : (1043688537 : ℕ)^4509*5000000000000^3485 ≤ 2155339914157^3485*2000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043688537 2000000000 2155339914157 5000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432891133/10000000000 : ℝ)^4509 ≤ (45412454495993/100000000000000 : ℝ)^3485 := by
    have hnat : (5432891133 : ℕ)^4509*100000000000000^3485 ≤ 45412454495993^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432891133 10000000000 45412454495993 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1876947841/10000000000 : ℝ), (1043688537/2000000000 : ℝ), (5432891133/10000000000 : ℝ)] ![(5740373603949/50000000000000 : ℝ), (2155339914157/5000000000000 : ℝ), (45412454495993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1876947841/10000000000 : ℝ)|^4509 ≤ (5740373603949/50000000000000 : ℝ)^3485
        have hw : |(-1876947841/10000000000 : ℝ)|=(1876947841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043688537/2000000000 : ℝ)|^4509 ≤ (2155339914157/5000000000000 : ℝ)^3485
        have hw : |(1043688537/2000000000 : ℝ)|=(1043688537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432891133/10000000000 : ℝ)|^4509 ≤ (45412454495993/100000000000000 : ℝ)^3485
        have hw : |(5432891133/10000000000 : ℝ)|=(5432891133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s6_5 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647546021/5000000000 : ℝ)*x 0 + (-443086153/2500000000 : ℝ)*x 1 + (5432890791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647546021/5000000000 : ℝ)^4509 ≤ (43927761628143/100000000000000 : ℝ)^3485 := by
    have hnat : (2647546021 : ℕ)^4509*100000000000000^3485 ≤ 43927761628143^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647546021 5000000000 43927761628143 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443086153/2500000000 : ℝ)^4509 ≤ (2131957511787/20000000000000 : ℝ)^3485 := by
    have hnat : (443086153 : ℕ)^4509*20000000000000^3485 ≤ 2131957511787^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443086153 2500000000 2131957511787 20000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432890791/10000000000 : ℝ)^4509 ≤ (45412450797307/100000000000000 : ℝ)^3485 := by
    have hnat : (5432890791 : ℕ)^4509*100000000000000^3485 ≤ 45412450797307^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432890791 10000000000 45412450797307 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647546021/5000000000 : ℝ), (-443086153/2500000000 : ℝ), (5432890791/10000000000 : ℝ)] ![(43927761628143/100000000000000 : ℝ), (2131957511787/20000000000000 : ℝ), (45412450797307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647546021/5000000000 : ℝ)|^4509 ≤ (43927761628143/100000000000000 : ℝ)^3485
        have hw : |(2647546021/5000000000 : ℝ)|=(2647546021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-443086153/2500000000 : ℝ)|^4509 ≤ (2131957511787/20000000000000 : ℝ)^3485
        have hw : |(-443086153/2500000000 : ℝ)|=(443086153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432890791/10000000000 : ℝ)|^4509 ≤ (45412450797307/100000000000000 : ℝ)^3485
        have hw : |(5432890791/10000000000 : ℝ)|=(5432890791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s6_6 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295091989/10000000000 : ℝ)*x 0 + (1358222821/2500000000 : ℝ)*x 1 + (-221543/1250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295091989/10000000000 : ℝ)^4509 ≤ (8785552211853/20000000000000 : ℝ)^3485 := by
    have hnat : (5295091989 : ℕ)^4509*20000000000000^3485 ≤ 8785552211853^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295091989 10000000000 8785552211853 20000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358222821/2500000000 : ℝ)^4509 ≤ (45412456129039/100000000000000 : ℝ)^3485 := by
    have hnat : (1358222821 : ℕ)^4509*100000000000000^3485 ≤ 45412456129039^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358222821 2500000000 45412456129039 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221543/1250000 : ℝ)^4509 ≤ (5329891398249/50000000000000 : ℝ)^3485 := by
    have hnat : (221543 : ℕ)^4509*50000000000000^3485 ≤ 5329891398249^3485*1250000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221543 1250000 5329891398249 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295091989/10000000000 : ℝ), (1358222821/2500000000 : ℝ), (-221543/1250000 : ℝ)] ![(8785552211853/20000000000000 : ℝ), (45412456129039/100000000000000 : ℝ), (5329891398249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295091989/10000000000 : ℝ)|^4509 ≤ (8785552211853/20000000000000 : ℝ)^3485
        have hw : |(5295091989/10000000000 : ℝ)|=(5295091989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358222821/2500000000 : ℝ)|^4509 ≤ (45412456129039/100000000000000 : ℝ)^3485
        have hw : |(1358222821/2500000000 : ℝ)|=(1358222821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-221543/1250000 : ℝ)|^4509 ≤ (5329891398249/50000000000000 : ℝ)^3485
        have hw : |(-221543/1250000 : ℝ)|=(221543/1250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_s6_7 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267040081/625000000 : ℝ)*x 0 + (4520673063/10000000000 : ℝ)*x 1 + (4036446153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267040081/625000000 : ℝ)^4509 ≤ (33280029855131/100000000000000 : ℝ)^3485 := by
    have hnat : (267040081 : ℕ)^4509*100000000000000^3485 ≤ 33280029855131^3485*625000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267040081 625000000 33280029855131 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4520673063/10000000000 : ℝ)^4509 ≤ (35800672456761/100000000000000 : ℝ)^3485 := by
    have hnat : (4520673063 : ℕ)^4509*100000000000000^3485 ≤ 35800672456761^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520673063 10000000000 35800672456761 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4036446153/10000000000 : ℝ)^4509 ≤ (193245610463/625000000000 : ℝ)^3485 := by
    have hnat : (4036446153 : ℕ)^4509*625000000000^3485 ≤ 193245610463^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4036446153 10000000000 193245610463 625000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267040081/625000000 : ℝ), (4520673063/10000000000 : ℝ), (4036446153/10000000000 : ℝ)] ![(33280029855131/100000000000000 : ℝ), (35800672456761/100000000000000 : ℝ), (193245610463/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267040081/625000000 : ℝ)|^4509 ≤ (33280029855131/100000000000000 : ℝ)^3485
        have hw : |(267040081/625000000 : ℝ)|=(267040081/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4520673063/10000000000 : ℝ)|^4509 ≤ (35800672456761/100000000000000 : ℝ)^3485
        have hw : |(4520673063/10000000000 : ℝ)|=(4520673063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4036446153/10000000000 : ℝ)|^4509 ≤ (193245610463/625000000000 : ℝ)^3485
        have hw : |(4036446153/10000000000 : ℝ)|=(4036446153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1506_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2723/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10893/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15481/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2723/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2723/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2723/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2723/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2723/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2723/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2723/25000 : ℝ) ^ (4507/1024 : ℝ) ≤ (7225487305203/125000000000000000 : ℝ) := by
    have hpowers : (2723/25000 : ℝ)^4507 ≤ (7225487305203/125000000000000000 : ℝ)^1024 := by
      have hnat : (2723 : ℕ)^4507*125000000000000000^1024 ≤ 7225487305203^1024*25000^4507 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2723 25000 7225487305203 125000000000000000 4507 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2723/25000 : ℝ)) (X := (7225487305203/125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7741/50000 : ℝ) ^ (4507/1024 : ℝ) ≤ (27172613996834173/100000000000000000000 : ℝ) := by
    have hpowers : (7741/50000 : ℝ)^4507 ≤ (27172613996834173/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7741 : ℕ)^4507*100000000000000000000^1024 ≤ 27172613996834173^1024*50000^4507 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7741 50000 27172613996834173 100000000000000000000 4507 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7741/50000 : ℝ)) (X := (27172613996834173/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (62507225487305203/62500000000000000 : ℝ) ≤ (400010506065777/400000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (62507225487305203/62500000000000000 : ℝ)^1024 ≤ (400010506065777/400000000000000 : ℝ)^4507 := by
      have hnat : (62507225487305203 : ℕ)^1024*400000000000000^4507 ≤ 400010506065777^4507*62500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62507225487305203 62500000000000000 400010506065777 400000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400010506065777/400000000000000 : ℝ)) (X := (62507225487305203/62500000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100032953003840996573/100000000000000000000 : ℝ) ≤ (2500187150988241/2500000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (100032953003840996573/100000000000000000000 : ℝ)^1024 ≤ (2500187150988241/2500000000000000 : ℝ)^4507 := by
      have hnat : (100032953003840996573 : ℕ)^1024*2500000000000000^4507 ≤ 2500187150988241^4507*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100032953003840996573 100000000000000000000 2500187150988241 2500000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500187150988241/2500000000000000 : ℝ)) (X := (100032953003840996573/100000000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027172613996834173/50000000000000000000 : ℝ) ≤ (10001234556261503/10000000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (50027172613996834173/50000000000000000000 : ℝ)^1024 ≤ (10001234556261503/10000000000000000 : ℝ)^4507 := by
      have hnat : (50027172613996834173 : ℕ)^1024*10000000000000000^4507 ≤ 10001234556261503^4507*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027172613996834173 50000000000000000000 10001234556261503 10000000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001234556261503/10000000000000000 : ℝ)) (X := (50027172613996834173/50000000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7225487305203/125000000000000000 : ℝ) ≤ ((22945309792979348587/22950000000000000000 : ℝ)+2*(485952308539/459000000000000 : ℝ)*(2723/25000 : ℝ))^(4507/1024 : ℝ) := by
    rw [show (22945309792979348587/22950000000000000000 : ℝ)+2*(485952308539/459000000000000 : ℝ)*(2723/25000 : ℝ)=(400010506065777/400000000000000 : ℝ) by norm_num, show 1+2*(7225487305203/125000000000000000 : ℝ)=(62507225487305203/62500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27172613996834173/100000000000000000000 : ℝ)+(7225487305203/125000000000000000 : ℝ) ≤ ((22945309792979348587/22950000000000000000 : ℝ)+(485952308539/459000000000000 : ℝ)*((7741/50000 : ℝ)+(2723/25000 : ℝ)))^(4507/1024 : ℝ) := by
    rw [show (22945309792979348587/22950000000000000000 : ℝ)+(485952308539/459000000000000 : ℝ)*((7741/50000 : ℝ)+(2723/25000 : ℝ))=(2500187150988241/2500000000000000 : ℝ) by norm_num, show 1+(27172613996834173/100000000000000000000 : ℝ)+(7225487305203/125000000000000000 : ℝ)=(100032953003840996573/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27172613996834173/100000000000000000000 : ℝ) ≤ ((22945309792979348587/22950000000000000000 : ℝ)+2*(485952308539/459000000000000 : ℝ)*(7741/50000 : ℝ))^(4507/1024 : ℝ) := by
    rw [show (22945309792979348587/22950000000000000000 : ℝ)+2*(485952308539/459000000000000 : ℝ)*(7741/50000 : ℝ)=(10001234556261503/10000000000000000 : ℝ) by norm_num, show 1+2*(27172613996834173/100000000000000000000 : ℝ)=(50027172613996834173/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22945309792979348587/22950000000000000000 : ℝ)*(X 1 0+X 2 0)+(485952308539/459000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (2723/25000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (22945309792979348587/22950000000000000000 : ℝ)) (alpha := (485952308539/459000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22945309792979348587/22950000000000000000 : ℝ)*(X 0 1+X 2 1)+(485952308539/459000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (2723/25000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (22945309792979348587/22950000000000000000 : ℝ)) (alpha := (485952308539/459000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22945309792979348587/22950000000000000000 : ℝ)*(X 0 2+X 1 2)+(485952308539/459000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (2723/25000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (22945309792979348587/22950000000000000000 : ℝ)) (alpha := (485952308539/459000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1876917239/10000000000 : ℝ)*X 0 0+(1358503461/2500000000 : ℝ)*X 0 1+(13043323/25000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334495131/625000000 : ℝ)*X 1 0+(-496976541/2500000000 : ℝ)*X 1 1+(13043323/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334495131/625000000 : ℝ)*X 2 0+(13043323/25000000 : ℝ)*X 2 1+(-496976541/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2136287333/5000000000 : ℝ)*X 0 0+(806782719/2000000000 : ℝ)*X 0 1+(4523187803/10000000000 : ℝ)*X 0 2+(2136287333/5000000000 : ℝ)*X 1 0+(806782719/2000000000 : ℝ)*X 1 1+(4523187803/10000000000 : ℝ)*X 1 2+(2136287333/5000000000 : ℝ)*X 2 0+(806782719/2000000000 : ℝ)*X 2 1+(4523187803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1876947841/10000000000 : ℝ)*X 0 0+(1043688537/2000000000 : ℝ)*X 0 1+(5432891133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647546021/5000000000 : ℝ)*X 1 0+(-443086153/2500000000 : ℝ)*X 1 1+(5432890791/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295091989/10000000000 : ℝ)*X 2 0+(1358222821/2500000000 : ℝ)*X 2 1+(-221543/1250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((267040081/625000000 : ℝ)*X 0 0+(4520673063/10000000000 : ℝ)*X 0 1+(4036446153/10000000000 : ℝ)*X 0 2+(267040081/625000000 : ℝ)*X 1 0+(4520673063/10000000000 : ℝ)*X 1 1+(4036446153/10000000000 : ℝ)*X 1 2+(267040081/625000000 : ℝ)*X 2 0+(4520673063/10000000000 : ℝ)*X 2 1+(4036446153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (454623808554622209743879317/191250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52729353/12500000000000 : ℝ)*(base19) + (393604453/100000000000000 : ℝ)*(base23) + (604347/4000000000000 : ℝ)*(lower2) + (477961/800000000000 : ℝ)*(upper3) + (39077393/100000000000000 : ℝ)*(upper5) + (3329432443413583/100000000000000 : ℝ)*(major0) + (3329432443413583/100000000000000 : ℝ)*(major1) + (208089527713349/6250000000000 : ℝ)*(major2) + (4615008548420027/100000000000000 : ℝ)*(sp0) + (4615014714231869/100000000000000 : ℝ)*(sp1) + (28843842140389/625000000000 : ℝ)*(sp2) + (255480813478147/12500000000000 : ℝ)*(sp3) + (3293823333/50000000000000 : ℝ)*(sp4) + (3163698027/100000000000000 : ℝ)*(sp7) + (2043849671523203/100000000000000 : ℝ)*(f.failure) + (4615015136066693/100000000000000 : ℝ)*(f.sum) + (32523672170029/15300000000000000000000000000 : ℝ)*base66 + (25793138355948542779/2295000000000000000000000000000000 : ℝ)*base68 + (96478424926466497/35859375000000000000000000000000 : ℝ)*base69 + (18862204419783542779/2295000000000000000000000000000000 : ℝ)*base72 + (20955133013171/15300000000000000000000000000 : ℝ)*base73 + (242642176153185247/35859375000000000000000000000000 : ℝ)*base75 + (3490381554643497593/765000000000000000000000000000000 : ℝ)*base78 + (7115757231988497593/765000000000000000000000000000000 : ℝ)*base80 + (20181820263187/22950000000000000000000000000 : ℝ)*base81 + (23541639/2000000000000000000000 : ℝ)*base89 + (23541639/2000000000000000000000 : ℝ)*base91 + (3541639/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (188327294341672338306298333/47812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (387891213/20000000000000 : ℝ)*(base19) + (3177209867/100000000000000 : ℝ)*(base23) + (79688411/100000000000000 : ℝ)*(lower1) + (19403071/4000000000000 : ℝ)*(upper2) + (646604161/100000000000000 : ℝ)*(upper3) + (1380673/400000000000 : ℝ)*(upper5) + (420515774644447/12500000000000 : ℝ)*(major0) + (420515774644447/12500000000000 : ℝ)*(major1) + (420515774644447/12500000000000 : ℝ)*(major2) + (17159891651/50000000000000 : ℝ)*(sp2) + (1165776255623427/25000000000000 : ℝ)*(sp4) + (2331551541518821/50000000000000 : ℝ)*(sp5) + (4663067525500539/100000000000000 : ℝ)*(sp6) + (129071702532607/6250000000000 : ℝ)*(sp7) + (129071702532607/6250000000000 : ℝ)*(f.failure) + (1165776255623427/25000000000000 : ℝ)*(f.sum) + (3738568529521/1434375000000000000000000000 : ℝ)*base66 + (944378134513665463/95625000000000000000000000000000 : ℝ)*base67 + (3254114399893665463/95625000000000000000000000000000 : ℝ)*base69 + (894969282238665463/95625000000000000000000000000000 : ℝ)*base71 + (14026942289383/2868750000000000000000000000 : ℝ)*base73 + (2127014687597415463/95625000000000000000000000000000 : ℝ)*base75 + (145357439021790463/95625000000000000000000000000000 : ℝ)*base77 + (533544973333665463/95625000000000000000000000000000 : ℝ)*base79 + (21145098637483/2868750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1016109/125000000000000000000 : ℝ)*base90 + (1016109/125000000000000000000 : ℝ)*base92 + (1016109/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1506_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2723/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10893/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1506_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1506_box_0 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1662212871/10000000000 : ℝ)*x 0 + (2701740787/5000000000 : ℝ)*x 1 + (2701740579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1662212871/10000000000 : ℝ)^4509 ≤ (2452677558231/25000000000000 : ℝ)^3485 := by
    have hnat : (1662212871 : ℕ)^4509*25000000000000^3485 ≤ 2452677558231^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1662212871 10000000000 2452677558231 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701740787/5000000000 : ℝ)^4509 ≤ (45094647121827/100000000000000 : ℝ)^3485 := by
    have hnat : (2701740787 : ℕ)^4509*100000000000000^3485 ≤ 45094647121827^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701740787 5000000000 45094647121827 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701740579/5000000000 : ℝ)^4509 ≤ (45094642630009/100000000000000 : ℝ)^3485 := by
    have hnat : (2701740579 : ℕ)^4509*100000000000000^3485 ≤ 45094642630009^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701740579 5000000000 45094642630009 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1662212871/10000000000 : ℝ), (2701740787/5000000000 : ℝ), (2701740579/5000000000 : ℝ)] ![(2452677558231/25000000000000 : ℝ), (45094647121827/100000000000000 : ℝ), (45094642630009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1662212871/10000000000 : ℝ)|^4509 ≤ (2452677558231/25000000000000 : ℝ)^3485
        have hw : |(-1662212871/10000000000 : ℝ)|=(1662212871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701740787/5000000000 : ℝ)|^4509 ≤ (45094647121827/100000000000000 : ℝ)^3485
        have hw : |(2701740787/5000000000 : ℝ)|=(2701740787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701740579/5000000000 : ℝ)|^4509 ≤ (45094642630009/100000000000000 : ℝ)^3485
        have hw : |(2701740579/5000000000 : ℝ)|=(2701740579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_box_1 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527069591/1000000000 : ℝ)*x 0 + (-923180777/5000000000 : ℝ)*x 1 + (675435211/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527069591/1000000000 : ℝ)^4509 ≤ (8733216437673/20000000000000 : ℝ)^3485 := by
    have hnat : (527069591 : ℕ)^4509*20000000000000^3485 ≤ 8733216437673^3485*1000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527069591 1000000000 8733216437673 20000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (923180777/5000000000 : ℝ)^4509 ≤ (449570777731/4000000000000 : ℝ)^3485 := by
    have hnat : (923180777 : ℕ)^4509*4000000000000^3485 ≤ 449570777731^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923180777 5000000000 449570777731 4000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675435211/1250000000 : ℝ)^4509 ≤ (45094648352757/100000000000000 : ℝ)^3485 := by
    have hnat : (675435211 : ℕ)^4509*100000000000000^3485 ≤ 45094648352757^3485*1250000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675435211 1250000000 45094648352757 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527069591/1000000000 : ℝ), (-923180777/5000000000 : ℝ), (675435211/1250000000 : ℝ)] ![(8733216437673/20000000000000 : ℝ), (449570777731/4000000000000 : ℝ), (45094648352757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527069591/1000000000 : ℝ)|^4509 ≤ (8733216437673/20000000000000 : ℝ)^3485
        have hw : |(527069591/1000000000 : ℝ)|=(527069591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-923180777/5000000000 : ℝ)|^4509 ≤ (449570777731/4000000000000 : ℝ)^3485
        have hw : |(-923180777/5000000000 : ℝ)|=(923180777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675435211/1250000000 : ℝ)|^4509 ≤ (45094648352757/100000000000000 : ℝ)^3485
        have hw : |(675435211/1250000000 : ℝ)|=(675435211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_box_2 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270695247/10000000000 : ℝ)*x 0 + (5403482019/10000000000 : ℝ)*x 1 + (-1846362003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270695247/10000000000 : ℝ)^4509 ≤ (21833037540839/50000000000000 : ℝ)^3485 := by
    have hnat : (5270695247 : ℕ)^4509*50000000000000^3485 ≤ 21833037540839^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270695247 10000000000 21833037540839 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403482019/10000000000 : ℝ)^4509 ≤ (5636831490847/12500000000000 : ℝ)^3485 := by
    have hnat : (5403482019 : ℕ)^4509*12500000000000^3485 ≤ 5636831490847^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403482019 10000000000 5636831490847 12500000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1846362003/10000000000 : ℝ)^4509 ≤ (11239272979543/100000000000000 : ℝ)^3485 := by
    have hnat : (1846362003 : ℕ)^4509*100000000000000^3485 ≤ 11239272979543^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846362003 10000000000 11239272979543 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270695247/10000000000 : ℝ), (5403482019/10000000000 : ℝ), (-1846362003/10000000000 : ℝ)] ![(21833037540839/50000000000000 : ℝ), (5636831490847/12500000000000 : ℝ), (11239272979543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270695247/10000000000 : ℝ)|^4509 ≤ (21833037540839/50000000000000 : ℝ)^3485
        have hw : |(5270695247/10000000000 : ℝ)|=(5270695247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403482019/10000000000 : ℝ)|^4509 ≤ (5636831490847/12500000000000 : ℝ)^3485
        have hw : |(5403482019/10000000000 : ℝ)|=(5403482019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1846362003/10000000000 : ℝ)|^4509 ≤ (11239272979543/100000000000000 : ℝ)^3485
        have hw : |(-1846362003/10000000000 : ℝ)|=(1846362003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_box_3 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4475911153/10000000000 : ℝ)*x 0 + (835585623/2000000000 : ℝ)*x 1 + (4177926931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4475911153/10000000000 : ℝ)^4509 ≤ (17671349430847/50000000000000 : ℝ)^3485 := by
    have hnat : (4475911153 : ℕ)^4509*50000000000000^3485 ≤ 17671349430847^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475911153 10000000000 17671349430847 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (835585623/2000000000 : ℝ)^4509 ≤ (32328656491501/100000000000000 : ℝ)^3485 := by
    have hnat : (835585623 : ℕ)^4509*100000000000000^3485 ≤ 32328656491501^3485*2000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835585623 2000000000 32328656491501 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4177926931/10000000000 : ℝ)^4509 ≤ (129314578551/400000000000 : ℝ)^3485 := by
    have hnat : (4177926931 : ℕ)^4509*400000000000^3485 ≤ 129314578551^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4177926931 10000000000 129314578551 400000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4475911153/10000000000 : ℝ), (835585623/2000000000 : ℝ), (4177926931/10000000000 : ℝ)] ![(17671349430847/50000000000000 : ℝ), (32328656491501/100000000000000 : ℝ), (129314578551/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4475911153/10000000000 : ℝ)|^4509 ≤ (17671349430847/50000000000000 : ℝ)^3485
        have hw : |(4475911153/10000000000 : ℝ)|=(4475911153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(835585623/2000000000 : ℝ)|^4509 ≤ (32328656491501/100000000000000 : ℝ)^3485
        have hw : |(835585623/2000000000 : ℝ)|=(835585623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4177926931/10000000000 : ℝ)|^4509 ≤ (129314578551/400000000000 : ℝ)^3485
        have hw : |(4177926931/10000000000 : ℝ)|=(4177926931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_box_4 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-32766651/156250000 : ℝ)*x 0 + (2621714109/5000000000 : ℝ)*x 1 + (262171287/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32766651/156250000 : ℝ)^4509 ≤ (13251981323553/100000000000000 : ℝ)^3485 := by
    have hnat : (32766651 : ℕ)^4509*100000000000000^3485 ≤ 13251981323553^3485*156250000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32766651 156250000 13251981323553 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621714109/5000000000 : ℝ)^4509 ≤ (21687011295661/50000000000000 : ℝ)^3485 := by
    have hnat : (2621714109 : ℕ)^4509*50000000000000^3485 ≤ 21687011295661^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621714109 5000000000 21687011295661 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262171287/500000000 : ℝ)^4509 ≤ (21686998035063/50000000000000 : ℝ)^3485 := by
    have hnat : (262171287 : ℕ)^4509*50000000000000^3485 ≤ 21686998035063^3485*500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262171287 500000000 21686998035063 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-32766651/156250000 : ℝ), (2621714109/5000000000 : ℝ), (262171287/500000000 : ℝ)] ![(13251981323553/100000000000000 : ℝ), (21687011295661/50000000000000 : ℝ), (21686998035063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-32766651/156250000 : ℝ)|^4509 ≤ (13251981323553/100000000000000 : ℝ)^3485
        have hw : |(-32766651/156250000 : ℝ)|=(32766651/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621714109/5000000000 : ℝ)|^4509 ≤ (21687011295661/50000000000000 : ℝ)^3485
        have hw : |(2621714109/5000000000 : ℝ)|=(2621714109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262171287/500000000 : ℝ)|^4509 ≤ (21686998035063/50000000000000 : ℝ)^3485
        have hw : |(262171287/500000000 : ℝ)|=(262171287/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_box_5 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5382181001/10000000000 : ℝ)*x 0 + (-956144559/5000000000 : ℝ)*x 1 + (1310856701/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382181001/10000000000 : ℝ)^4509 ≤ (44864784565387/100000000000000 : ℝ)^3485 := by
    have hnat : (5382181001 : ℕ)^4509*100000000000000^3485 ≤ 44864784565387^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382181001 10000000000 44864784565387 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (956144559/5000000000 : ℝ)^4509 ≤ (11761207962251/100000000000000 : ℝ)^3485 := by
    have hnat : (956144559 : ℕ)^4509*100000000000000^3485 ≤ 11761207962251^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956144559 5000000000 11761207962251 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310856701/2500000000 : ℝ)^4509 ≤ (21687003728879/50000000000000 : ℝ)^3485 := by
    have hnat : (1310856701 : ℕ)^4509*50000000000000^3485 ≤ 21687003728879^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310856701 2500000000 21687003728879 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382181001/10000000000 : ℝ), (-956144559/5000000000 : ℝ), (1310856701/2500000000 : ℝ)] ![(44864784565387/100000000000000 : ℝ), (11761207962251/100000000000000 : ℝ), (21687003728879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382181001/10000000000 : ℝ)|^4509 ≤ (44864784565387/100000000000000 : ℝ)^3485
        have hw : |(5382181001/10000000000 : ℝ)|=(5382181001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-956144559/5000000000 : ℝ)|^4509 ≤ (11761207962251/100000000000000 : ℝ)^3485
        have hw : |(-956144559/5000000000 : ℝ)|=(956144559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310856701/2500000000 : ℝ)|^4509 ≤ (21687003728879/50000000000000 : ℝ)^3485
        have hw : |(1310856701/2500000000 : ℝ)|=(1310856701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_box_6 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538218111/1000000000 : ℝ)*x 0 + (2621712961/5000000000 : ℝ)*x 1 + (-478072539/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538218111/1000000000 : ℝ)^4509 ≤ (8972957148193/20000000000000 : ℝ)^3485 := by
    have hnat : (538218111 : ℕ)^4509*20000000000000^3485 ≤ 8972957148193^3485*1000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538218111 1000000000 8972957148193 20000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621712961/5000000000 : ℝ)^4509 ≤ (4337399801801/10000000000000 : ℝ)^3485 := by
    have hnat : (2621712961 : ℕ)^4509*10000000000000^3485 ≤ 4337399801801^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621712961 5000000000 4337399801801 10000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (478072539/2500000000 : ℝ)^4509 ≤ (11761216222121/100000000000000 : ℝ)^3485 := by
    have hnat : (478072539 : ℕ)^4509*100000000000000^3485 ≤ 11761216222121^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478072539 2500000000 11761216222121 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538218111/1000000000 : ℝ), (2621712961/5000000000 : ℝ), (-478072539/2500000000 : ℝ)] ![(8972957148193/20000000000000 : ℝ), (4337399801801/10000000000000 : ℝ), (11761216222121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538218111/1000000000 : ℝ)|^4509 ≤ (8972957148193/20000000000000 : ℝ)^3485
        have hw : |(538218111/1000000000 : ℝ)|=(538218111/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621712961/5000000000 : ℝ)|^4509 ≤ (4337399801801/10000000000000 : ℝ)^3485
        have hw : |(2621712961/5000000000 : ℝ)|=(2621712961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-478072539/2500000000 : ℝ)|^4509 ≤ (11761216222121/100000000000000 : ℝ)^3485
        have hw : |(-478072539/2500000000 : ℝ)|=(478072539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_box_7 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (254177987/625000000 : ℝ)*x 0 + (876464887/2000000000 : ℝ)*x 1 + (1095580951/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (254177987/625000000 : ℝ)^4509 ≤ (31220934495501/100000000000000 : ℝ)^3485 := by
    have hnat : (254177987 : ℕ)^4509*100000000000000^3485 ≤ 31220934495501^3485*625000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254177987 625000000 31220934495501 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (876464887/2000000000 : ℝ)^4509 ≤ (4298691993297/12500000000000 : ℝ)^3485 := by
    have hnat : (876464887 : ℕ)^4509*12500000000000^3485 ≤ 4298691993297^3485*2000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876464887 2000000000 4298691993297 12500000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095580951/2500000000 : ℝ)^4509 ≤ (34389529539761/100000000000000 : ℝ)^3485 := by
    have hnat : (1095580951 : ℕ)^4509*100000000000000^3485 ≤ 34389529539761^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095580951 2500000000 34389529539761 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(254177987/625000000 : ℝ), (876464887/2000000000 : ℝ), (1095580951/2500000000 : ℝ)] ![(31220934495501/100000000000000 : ℝ), (4298691993297/12500000000000 : ℝ), (34389529539761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(254177987/625000000 : ℝ)|^4509 ≤ (31220934495501/100000000000000 : ℝ)^3485
        have hw : |(254177987/625000000 : ℝ)|=(254177987/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(876464887/2000000000 : ℝ)|^4509 ≤ (4298691993297/12500000000000 : ℝ)^3485
        have hw : |(876464887/2000000000 : ℝ)|=(876464887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1095580951/2500000000 : ℝ)|^4509 ≤ (34389529539761/100000000000000 : ℝ)^3485
        have hw : |(1095580951/2500000000 : ℝ)|=(1095580951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_box_8 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1002601543/5000000000 : ℝ)*x 0 + (513136271/1000000000 : ℝ)*x 1 + (677994013/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1002601543/5000000000 : ℝ)^4509 ≤ (6252894053757/50000000000000 : ℝ)^3485 := by
    have hnat : (1002601543 : ℕ)^4509*50000000000000^3485 ≤ 6252894053757^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002601543 5000000000 6252894053757 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513136271/1000000000 : ℝ)^4509 ≤ (42178408474849/100000000000000 : ℝ)^3485 := by
    have hnat : (513136271 : ℕ)^4509*100000000000000^3485 ≤ 42178408474849^3485*1000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513136271 1000000000 42178408474849 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677994013/1250000000 : ℝ)^4509 ≤ (283223771313/625000000000 : ℝ)^3485 := by
    have hnat : (677994013 : ℕ)^4509*625000000000^3485 ≤ 283223771313^3485*1250000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677994013 1250000000 283223771313 625000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1002601543/5000000000 : ℝ), (513136271/1000000000 : ℝ), (677994013/1250000000 : ℝ)] ![(6252894053757/50000000000000 : ℝ), (42178408474849/100000000000000 : ℝ), (283223771313/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1002601543/5000000000 : ℝ)|^4509 ≤ (6252894053757/50000000000000 : ℝ)^3485
        have hw : |(-1002601543/5000000000 : ℝ)|=(1002601543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(513136271/1000000000 : ℝ)|^4509 ≤ (42178408474849/100000000000000 : ℝ)^3485
        have hw : |(513136271/1000000000 : ℝ)|=(513136271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677994013/1250000000 : ℝ)|^4509 ≤ (283223771313/625000000000 : ℝ)^3485
        have hw : |(677994013/1250000000 : ℝ)|=(677994013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_box_9 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051286179/2000000000 : ℝ)*x 0 + (-183768237/1000000000 : ℝ)*x 1 + (2711976029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051286179/2000000000 : ℝ)^4509 ≤ (10878309131099/25000000000000 : ℝ)^3485 := by
    have hnat : (1051286179 : ℕ)^4509*25000000000000^3485 ≤ 10878309131099^3485*2000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051286179 2000000000 10878309131099 25000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183768237/1000000000 : ℝ)^4509 ≤ (5585480269357/50000000000000 : ℝ)^3485 := by
    have hnat : (183768237 : ℕ)^4509*50000000000000^3485 ≤ 5585480269357^3485*1000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183768237 1000000000 5585480269357 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711976029/5000000000 : ℝ)^4509 ≤ (45315802912837/100000000000000 : ℝ)^3485 := by
    have hnat : (2711976029 : ℕ)^4509*100000000000000^3485 ≤ 45315802912837^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711976029 5000000000 45315802912837 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051286179/2000000000 : ℝ), (-183768237/1000000000 : ℝ), (2711976029/5000000000 : ℝ)] ![(10878309131099/25000000000000 : ℝ), (5585480269357/50000000000000 : ℝ), (45315802912837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051286179/2000000000 : ℝ)|^4509 ≤ (10878309131099/25000000000000 : ℝ)^3485
        have hw : |(1051286179/2000000000 : ℝ)|=(1051286179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-183768237/1000000000 : ℝ)|^4509 ≤ (5585480269357/50000000000000 : ℝ)^3485
        have hw : |(-183768237/1000000000 : ℝ)|=(183768237/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711976029/5000000000 : ℝ)|^4509 ≤ (45315802912837/100000000000000 : ℝ)^3485
        have hw : |(2711976029/5000000000 : ℝ)|=(2711976029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_box_10 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628215501/5000000000 : ℝ)*x 0 + (216958097/400000000 : ℝ)*x 1 + (-45942043/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628215501/5000000000 : ℝ)^4509 ≤ (8702647534083/20000000000000 : ℝ)^3485 := by
    have hnat : (2628215501 : ℕ)^4509*20000000000000^3485 ≤ 8702647534083^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628215501 5000000000 8702647534083 20000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216958097/400000000 : ℝ)^4509 ≤ (1812632275199/4000000000000 : ℝ)^3485 := by
    have hnat : (216958097 : ℕ)^4509*4000000000000^3485 ≤ 1812632275199^3485*400000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216958097 400000000 1812632275199 4000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45942043/250000000 : ℝ)^4509 ≤ (5585477713239/50000000000000 : ℝ)^3485 := by
    have hnat : (45942043 : ℕ)^4509*50000000000000^3485 ≤ 5585477713239^3485*250000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45942043 250000000 5585477713239 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628215501/5000000000 : ℝ), (216958097/400000000 : ℝ), (-45942043/250000000 : ℝ)] ![(8702647534083/20000000000000 : ℝ), (1812632275199/4000000000000 : ℝ), (5585477713239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628215501/5000000000 : ℝ)|^4509 ≤ (8702647534083/20000000000000 : ℝ)^3485
        have hw : |(2628215501/5000000000 : ℝ)|=(2628215501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216958097/400000000 : ℝ)|^4509 ≤ (1812632275199/4000000000000 : ℝ)^3485
        have hw : |(216958097/400000000 : ℝ)|=(216958097/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-45942043/250000000 : ℝ)|^4509 ≤ (5585477713239/50000000000000 : ℝ)^3485
        have hw : |(-45942043/250000000 : ℝ)|=(45942043/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_box_11 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4527078457/10000000000 : ℝ)*x 0 + (4151753033/10000000000 : ℝ)*x 1 + (4151752643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4527078457/10000000000 : ℝ)^4509 ≤ (17933158735871/50000000000000 : ℝ)^3485 := by
    have hnat : (4527078457 : ℕ)^4509*50000000000000^3485 ≤ 17933158735871^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527078457 10000000000 17933158735871 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4151753033/10000000000 : ℝ)^4509 ≤ (32066843206103/100000000000000 : ℝ)^3485 := by
    have hnat : (4151753033 : ℕ)^4509*100000000000000^3485 ≤ 32066843206103^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151753033 10000000000 32066843206103 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4151752643/10000000000 : ℝ)^4509 ≤ (32066839308777/100000000000000 : ℝ)^3485 := by
    have hnat : (4151752643 : ℕ)^4509*100000000000000^3485 ≤ 32066839308777^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151752643 10000000000 32066839308777 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4527078457/10000000000 : ℝ), (4151753033/10000000000 : ℝ), (4151752643/10000000000 : ℝ)] ![(17933158735871/50000000000000 : ℝ), (32066843206103/100000000000000 : ℝ), (32066839308777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4527078457/10000000000 : ℝ)|^4509 ≤ (17933158735871/50000000000000 : ℝ)^3485
        have hw : |(4527078457/10000000000 : ℝ)|=(4527078457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4151753033/10000000000 : ℝ)|^4509 ≤ (32066843206103/100000000000000 : ℝ)^3485
        have hw : |(4151753033/10000000000 : ℝ)|=(4151753033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4151752643/10000000000 : ℝ)|^4509 ≤ (32066839308777/100000000000000 : ℝ)^3485
        have hw : |(4151752643/10000000000 : ℝ)|=(4151752643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_box_12 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-175405789/1000000000 : ℝ)*x 0 + (1377980637/2500000000 : ℝ)*x 1 + (653550713/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (175405789/1000000000 : ℝ)^4509 ≤ (5258850456133/50000000000000 : ℝ)^3485 := by
    have hnat : (175405789 : ℕ)^4509*50000000000000^3485 ≤ 5258850456133^3485*1000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175405789 1000000000 5258850456133 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1377980637/2500000000 : ℝ)^4509 ≤ (46268989657769/100000000000000 : ℝ)^3485 := by
    have hnat : (1377980637 : ℕ)^4509*100000000000000^3485 ≤ 46268989657769^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377980637 2500000000 46268989657769 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (653550713/1250000000 : ℝ)^4509 ≤ (21606654708037/50000000000000 : ℝ)^3485 := by
    have hnat : (653550713 : ℕ)^4509*50000000000000^3485 ≤ 21606654708037^3485*1250000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653550713 1250000000 21606654708037 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-175405789/1000000000 : ℝ), (1377980637/2500000000 : ℝ), (653550713/1250000000 : ℝ)] ![(5258850456133/50000000000000 : ℝ), (46268989657769/100000000000000 : ℝ), (21606654708037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-175405789/1000000000 : ℝ)|^4509 ≤ (5258850456133/50000000000000 : ℝ)^3485
        have hw : |(-175405789/1000000000 : ℝ)|=(175405789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1377980637/2500000000 : ℝ)|^4509 ≤ (46268989657769/100000000000000 : ℝ)^3485
        have hw : |(1377980637/2500000000 : ℝ)|=(1377980637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(653550713/1250000000 : ℝ)|^4509 ≤ (21606654708037/50000000000000 : ℝ)^3485
        have hw : |(653550713/1250000000 : ℝ)|=(653550713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_box_13 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392644539/10000000000 : ℝ)*x 0 + (-959148063/5000000000 : ℝ)*x 1 + (2614202509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392644539/10000000000 : ℝ)^4509 ≤ (5622208404157/12500000000000 : ℝ)^3485 := by
    have hnat : (5392644539 : ℕ)^4509*12500000000000^3485 ≤ 5622208404157^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392644539 10000000000 5622208404157 12500000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (959148063/5000000000 : ℝ)^4509 ≤ (2361806136403/20000000000000 : ℝ)^3485 := by
    have hnat : (959148063 : ℕ)^4509*20000000000000^3485 ≤ 2361806136403^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959148063 5000000000 2361806136403 20000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614202509/5000000000 : ℝ)^4509 ≤ (8642660416047/20000000000000 : ℝ)^3485 := by
    have hnat : (2614202509 : ℕ)^4509*20000000000000^3485 ≤ 8642660416047^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614202509 5000000000 8642660416047 20000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392644539/10000000000 : ℝ), (-959148063/5000000000 : ℝ), (2614202509/5000000000 : ℝ)] ![(5622208404157/12500000000000 : ℝ), (2361806136403/20000000000000 : ℝ), (8642660416047/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392644539/10000000000 : ℝ)|^4509 ≤ (5622208404157/12500000000000 : ℝ)^3485
        have hw : |(5392644539/10000000000 : ℝ)|=(5392644539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-959148063/5000000000 : ℝ)|^4509 ≤ (2361806136403/20000000000000 : ℝ)^3485
        have hw : |(-959148063/5000000000 : ℝ)|=(959148063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614202509/5000000000 : ℝ)|^4509 ≤ (8642660416047/20000000000000 : ℝ)^3485
        have hw : |(2614202509/5000000000 : ℝ)|=(2614202509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_box_14 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348161081/2500000000 : ℝ)*x 0 + (5228405331/10000000000 : ℝ)*x 1 + (-479573999/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348161081/2500000000 : ℝ)^4509 ≤ (44977664913133/100000000000000 : ℝ)^3485 := by
    have hnat : (1348161081 : ℕ)^4509*100000000000000^3485 ≤ 44977664913133^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348161081 2500000000 44977664913133 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228405331/10000000000 : ℝ)^4509 ≤ (8642661085469/20000000000000 : ℝ)^3485 := by
    have hnat : (5228405331 : ℕ)^4509*20000000000000^3485 ≤ 8642661085469^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228405331 10000000000 8642661085469 20000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (479573999/2500000000 : ℝ)^4509 ≤ (11809029646589/100000000000000 : ℝ)^3485 := by
    have hnat : (479573999 : ℕ)^4509*100000000000000^3485 ≤ 11809029646589^3485*2500000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479573999 2500000000 11809029646589 100000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348161081/2500000000 : ℝ), (5228405331/10000000000 : ℝ), (-479573999/2500000000 : ℝ)] ![(44977664913133/100000000000000 : ℝ), (8642661085469/20000000000000 : ℝ), (11809029646589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348161081/2500000000 : ℝ)|^4509 ≤ (44977664913133/100000000000000 : ℝ)^3485
        have hw : |(1348161081/2500000000 : ℝ)|=(1348161081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228405331/10000000000 : ℝ)|^4509 ≤ (8642661085469/20000000000000 : ℝ)^3485
        have hw : |(5228405331/10000000000 : ℝ)|=(5228405331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-479573999/2500000000 : ℝ)|^4509 ≤ (11809029646589/100000000000000 : ℝ)^3485
        have hw : |(-479573999/2500000000 : ℝ)|=(479573999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1506_box_15 (p : ℝ) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2013798131/5000000000 : ℝ)*x 0 + (4401483741/10000000000 : ℝ)*x 1 + (4401484591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2013798131/5000000000 : ℝ)^4509 ≤ (6166323320623/20000000000000 : ℝ)^3485 := by
    have hnat : (2013798131 : ℕ)^4509*20000000000000^3485 ≤ 6166323320623^3485*5000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013798131 5000000000 6166323320623 20000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4401483741/10000000000 : ℝ)^4509 ≤ (691683747451/2000000000000 : ℝ)^3485 := by
    have hnat : (4401483741 : ℕ)^4509*2000000000000^3485 ≤ 691683747451^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4401483741 10000000000 691683747451 2000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4401484591/10000000000 : ℝ)^4509 ≤ (17292098006883/50000000000000 : ℝ)^3485 := by
    have hnat : (4401484591 : ℕ)^4509*50000000000000^3485 ≤ 17292098006883^3485*10000000000^4509 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4401484591 10000000000 17292098006883 50000000000000 4509 3485 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4509/1024 : ℝ)) 4509 3485 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2013798131/5000000000 : ℝ), (4401483741/10000000000 : ℝ), (4401484591/10000000000 : ℝ)] ![(6166323320623/20000000000000 : ℝ), (691683747451/2000000000000 : ℝ), (17292098006883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2013798131/5000000000 : ℝ)|^4509 ≤ (6166323320623/20000000000000 : ℝ)^3485
        have hw : |(2013798131/5000000000 : ℝ)|=(2013798131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4401483741/10000000000 : ℝ)|^4509 ≤ (691683747451/2000000000000 : ℝ)^3485
        have hw : |(4401483741/10000000000 : ℝ)|=(4401483741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4401484591/10000000000 : ℝ)|^4509 ≤ (17292098006883/50000000000000 : ℝ)^3485
        have hw : |(4401484591/10000000000 : ℝ)|=(4401484591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1506_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10893/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15933/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58599/100000 : ℝ) ∧ (16051/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (85963/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10893/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10893/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10893/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10893/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10893/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10893/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10893/100000 : ℝ) ^ (4507/1024 : ℝ) ≤ (1156545203334003/20000000000000000000 : ℝ) := by
    have hpowers : (10893/100000 : ℝ)^4507 ≤ (1156545203334003/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10893 : ℕ)^4507*20000000000000000000^1024 ≤ 1156545203334003^1024*100000^4507 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10893 100000 1156545203334003 20000000000000000000 4507 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10893/100000 : ℝ)) (X := (1156545203334003/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15481/100000 : ℝ) ^ (4507/1024 : ℝ) ≤ (6791222490379899/25000000000000000000 : ℝ) := by
    have hpowers : (15481/100000 : ℝ)^4507 ≤ (6791222490379899/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15481 : ℕ)^4507*25000000000000000000^1024 ≤ 6791222490379899^1024*100000^4507 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15481 100000 6791222490379899 25000000000000000000 4507 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15481/100000 : ℝ)) (X := (6791222490379899/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001156545203334003/10000000000000000000 : ℝ) ≤ (5000131378895807/5000000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (10001156545203334003/10000000000000000000 : ℝ)^1024 ≤ (5000131378895807/5000000000000000 : ℝ)^4507 := by
      have hnat : (10001156545203334003 : ℕ)^1024*5000000000000000^4507 ≤ 5000131378895807^4507*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001156545203334003 10000000000000000000 5000131378895807 5000000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000131378895807/5000000000000000 : ℝ)) (X := (10001156545203334003/10000000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100032947615978189611/100000000000000000000 : ℝ) ≤ (2000149696314147/2000000000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (100032947615978189611/100000000000000000000 : ℝ)^1024 ≤ (2000149696314147/2000000000000000 : ℝ)^4507 := by
      have hnat : (100032947615978189611 : ℕ)^1024*2000000000000000^4507 ≤ 2000149696314147^4507*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100032947615978189611 100000000000000000000 2000149696314147 2000000000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000149696314147/2000000000000000 : ℝ)) (X := (100032947615978189611/100000000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506791222490379899/12500000000000000000 : ℝ) ≤ (312538568917183/312500000000000 : ℝ) ^ (4507/1024 : ℝ) := by
    have hpowers : (12506791222490379899/12500000000000000000 : ℝ)^1024 ≤ (312538568917183/312500000000000 : ℝ)^4507 := by
      have hnat : (12506791222490379899 : ℕ)^1024*312500000000000^4507 ≤ 312538568917183^4507*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506791222490379899 12500000000000000000 312538568917183 312500000000000 1024 4507 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312538568917183/312500000000000 : ℝ)) (X := (12506791222490379899/12500000000000000000 : ℝ)) (by norm_num) 4507 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1156545203334003/20000000000000000000 : ℝ) ≤ ((22935311777247997463/22940000000000000000 : ℝ)+2*(485723779121/458800000000000 : ℝ)*(10893/100000 : ℝ))^(4507/1024 : ℝ) := by
    rw [show (22935311777247997463/22940000000000000000 : ℝ)+2*(485723779121/458800000000000 : ℝ)*(10893/100000 : ℝ)=(5000131378895807/5000000000000000 : ℝ) by norm_num, show 1+2*(1156545203334003/20000000000000000000 : ℝ)=(10001156545203334003/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6791222490379899/25000000000000000000 : ℝ)+(1156545203334003/20000000000000000000 : ℝ) ≤ ((22935311777247997463/22940000000000000000 : ℝ)+(485723779121/458800000000000 : ℝ)*((15481/100000 : ℝ)+(10893/100000 : ℝ)))^(4507/1024 : ℝ) := by
    rw [show (22935311777247997463/22940000000000000000 : ℝ)+(485723779121/458800000000000 : ℝ)*((15481/100000 : ℝ)+(10893/100000 : ℝ))=(2000149696314147/2000000000000000 : ℝ) by norm_num, show 1+(6791222490379899/25000000000000000000 : ℝ)+(1156545203334003/20000000000000000000 : ℝ)=(100032947615978189611/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6791222490379899/25000000000000000000 : ℝ) ≤ ((22935311777247997463/22940000000000000000 : ℝ)+2*(485723779121/458800000000000 : ℝ)*(15481/100000 : ℝ))^(4507/1024 : ℝ) := by
    rw [show (22935311777247997463/22940000000000000000 : ℝ)+2*(485723779121/458800000000000 : ℝ)*(15481/100000 : ℝ)=(312538568917183/312500000000000 : ℝ) by norm_num, show 1+2*(6791222490379899/25000000000000000000 : ℝ)=(12506791222490379899/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22935311777247997463/22940000000000000000 : ℝ)*(X 1 0+X 2 0)+(485723779121/458800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (10893/100000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (22935311777247997463/22940000000000000000 : ℝ)) (alpha := (485723779121/458800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22935311777247997463/22940000000000000000 : ℝ)*(X 0 1+X 2 1)+(485723779121/458800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (10893/100000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (22935311777247997463/22940000000000000000 : ℝ)) (alpha := (485723779121/458800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22935311777247997463/22940000000000000000 : ℝ)*(X 0 2+X 1 2)+(485723779121/458800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4507/1024 : ℝ)) (lo := (10893/100000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (22935311777247997463/22940000000000000000 : ℝ)) (alpha := (485723779121/458800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1662212871/10000000000 : ℝ)*X 0 0+(2701740787/5000000000 : ℝ)*X 0 1+(2701740579/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((527069591/1000000000 : ℝ)*X 1 0+(-923180777/5000000000 : ℝ)*X 1 1+(675435211/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270695247/10000000000 : ℝ)*X 2 0+(5403482019/10000000000 : ℝ)*X 2 1+(-1846362003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4475911153/10000000000 : ℝ)*X 0 0+(835585623/2000000000 : ℝ)*X 0 1+(4177926931/10000000000 : ℝ)*X 0 2+(4475911153/10000000000 : ℝ)*X 1 0+(835585623/2000000000 : ℝ)*X 1 1+(4177926931/10000000000 : ℝ)*X 1 2+(4475911153/10000000000 : ℝ)*X 2 0+(835585623/2000000000 : ℝ)*X 2 1+(4177926931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-32766651/156250000 : ℝ)*X 0 0+(2621714109/5000000000 : ℝ)*X 0 1+(262171287/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5382181001/10000000000 : ℝ)*X 1 0+(-956144559/5000000000 : ℝ)*X 1 1+(1310856701/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((538218111/1000000000 : ℝ)*X 2 0+(2621712961/5000000000 : ℝ)*X 2 1+(-478072539/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((254177987/625000000 : ℝ)*X 0 0+(876464887/2000000000 : ℝ)*X 0 1+(1095580951/2500000000 : ℝ)*X 0 2+(254177987/625000000 : ℝ)*X 1 0+(876464887/2000000000 : ℝ)*X 1 1+(1095580951/2500000000 : ℝ)*X 1 2+(254177987/625000000 : ℝ)*X 2 0+(876464887/2000000000 : ℝ)*X 2 1+(1095580951/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1002601543/5000000000 : ℝ)*X 0 0+(513136271/1000000000 : ℝ)*X 0 1+(677994013/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1051286179/2000000000 : ℝ)*X 1 0+(-183768237/1000000000 : ℝ)*X 1 1+(2711976029/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2628215501/5000000000 : ℝ)*X 2 0+(216958097/400000000 : ℝ)*X 2 1+(-45942043/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4527078457/10000000000 : ℝ)*X 0 0+(4151753033/10000000000 : ℝ)*X 0 1+(4151752643/10000000000 : ℝ)*X 0 2+(4527078457/10000000000 : ℝ)*X 1 0+(4151753033/10000000000 : ℝ)*X 1 1+(4151752643/10000000000 : ℝ)*X 1 2+(4527078457/10000000000 : ℝ)*X 2 0+(4151753033/10000000000 : ℝ)*X 2 1+(4151752643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-175405789/1000000000 : ℝ)*X 0 0+(1377980637/2500000000 : ℝ)*X 0 1+(653550713/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5392644539/10000000000 : ℝ)*X 1 0+(-959148063/5000000000 : ℝ)*X 1 1+(2614202509/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1348161081/2500000000 : ℝ)*X 2 0+(5228405331/10000000000 : ℝ)*X 2 1+(-479573999/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2013798131/5000000000 : ℝ)*X 0 0+(4401483741/10000000000 : ℝ)*X 0 1+(4401484591/10000000000 : ℝ)*X 0 2+(2013798131/5000000000 : ℝ)*X 1 0+(4401483741/10000000000 : ℝ)*X 1 1+(4401484591/10000000000 : ℝ)*X 1 2+(2013798131/5000000000 : ℝ)*X 2 0+(4401483741/10000000000 : ℝ)*X 2 1+(4401484591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1506_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15933/25000 : ℝ) ≤ (-292389125856540453004766457/458800000000000000000000000 : ℝ) := by norm_num
    linear_combination (158434251/100000000000000 : ℝ)*(upper0) + (32391719/6250000000000 : ℝ)*(upper3) + (4542367/10000000000000 : ℝ)*(lower4) + (221456141487217/10000000000000 : ℝ)*(major0) + (221456141487217/10000000000000 : ℝ)*(major1) + (221456141487217/10000000000000 : ℝ)*(major2) + (10701625993/50000000000000 : ℝ)*(sp1) + (1139979127/4000000000000 : ℝ)*(sp2) + (3045118201/25000000000000 : ℝ)*(sp3) + (1545448630954749/50000000000000 : ℝ)*(sp4) + (309088434353279/10000000000000 : ℝ)*(sp5) + (3090877247306601/100000000000000 : ℝ)*(sp6) + (679723968456997/50000000000000 : ℝ)*(sp7) + (8484875277/100000000000000 : ℝ)*(sp8) + (679730058693399/50000000000000 : ℝ)*(f.failure) + (386363218348097/12500000000000 : ℝ)*(f.sum) + (6114703451053/2294000000000000000000000000 : ℝ)*base65 + (98578133793819529/229400000000000000000000000000000 : ℝ)*base68 + (531779586652580471/229400000000000000000000000000000 : ℝ)*base69 + (849137216961780471/229400000000000000000000000000000 : ℝ)*base71 + (16305934077227/2294000000000000000000000000 : ℝ)*base74 + (1971920504827419529/229400000000000000000000000000000 : ℝ)*base76 + (306573806182780471/229400000000000000000000000000000 : ℝ)*base77 + (5165200866056019529/229400000000000000000000000000000 : ℝ)*base80 + (12618444293071/2294000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2434187/1000000000000000000000 : ℝ)*base89 + (2434187/1000000000000000000000 : ℝ)*base91 + (2434187/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58599/100000 : ℝ) ≤ (67216417881755207179526091/114700000000000000000000000 : ℝ) := by norm_num
    linear_combination (19647459/25000000000000 : ℝ)*(lower0) + (1567773/5000000000000 : ℝ)*(upper1) + (68217791/50000000000000 : ℝ)*(upper2) + (99291129/50000000000000 : ℝ)*(upper3) + (42635041/100000000000000 : ℝ)*(lower5) + (114518988167181/5000000000000 : ℝ)*(major0) + (114518988167181/5000000000000 : ℝ)*(major1) + (114518988167181/5000000000000 : ℝ)*(major2) + (1577611285932127/50000000000000 : ℝ)*(sp0) + (1577611285932127/50000000000000 : ℝ)*(sp1) + (3155216045864247/100000000000000 : ℝ)*(sp2) + (1405973191104009/100000000000000 : ℝ)*(sp3) + (815750001/12500000000000 : ℝ)*(sp6) + (5957167987/20000000000000 : ℝ)*(sp11) + (175750372117993/12500000000000 : ℝ)*(f.failure) + (1577611285932127/50000000000000 : ℝ)*(f.sum) + (380653542503/229400000000000000000000000 : ℝ)*base65 + (221111605081288197/114700000000000000000000000000000 : ℝ)*base68 + (510095271177711803/114700000000000000000000000000000 : ℝ)*base69 + (223539906066511803/114700000000000000000000000000000 : ℝ)*base71 + (3596959436677/1147000000000000000000000000 : ℝ)*base74 + (2449895406263711803/114700000000000000000000000000000 : ℝ)*base75 + (115350620543788197/114700000000000000000000000000000 : ℝ)*base78 + (1320009438594388197/114700000000000000000000000000000 : ℝ)*base80 + (4235989436641/286750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (526091/250000000000000000000 : ℝ)*base90 + (526091/250000000000000000000 : ℝ)*base92 + (526091/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (16051/20000 : ℝ) ≤ (115068554505018709146490608347241/143375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62402127/50000000000000 : ℝ)*(lower3) + (191262473/100000000000000 : ℝ)*(upper4) + (3518257/6250000000000 : ℝ)*(lower5) + (310624316592223/12500000000000 : ℝ)*(major0) + (310624316592223/12500000000000 : ℝ)*(major1) + (310624316592223/12500000000000 : ℝ)*(major2) + (201274049/50000000000000 : ℝ)*(sp0) + (53690573061/100000000000000 : ℝ)*(sp1) + (162141123987/100000000000000 : ℝ)*(sp2) + (31549357/48828125000 : ℝ)*(sp3) + (1708882261861141/50000000000000 : ℝ)*(sp8) + (85442780892433/2500000000000 : ℝ)*(sp9) + (1708801392573197/50000000000000 : ℝ)*(sp10) + (381351793503483/25000000000000 : ℝ)*(sp11) + (1525471787097067/100000000000000 : ℝ)*(f.failure) + (170888246313519/5000000000000 : ℝ)*(f.sum) + (321091671761/89609375000000000000000000 : ℝ)*base66 + (250873698490319751/286750000000000000000000000000000 : ℝ)*base68 + (1158982799963319751/286750000000000000000000000000000 : ℝ)*base70 + (1335472819184819751/286750000000000000000000000000000 : ℝ)*base72 + (1236024966969/358437500000000000000000000 : ℝ)*base74 + (2054036426276319751/286750000000000000000000000000000 : ℝ)*base76 + (2529245949947069751/286750000000000000000000000000000 : ℝ)*base78 + (1248117000104569751/286750000000000000000000000000000 : ℝ)*base80 + (36043698577519/5735000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4878129/2000000000000000000000 : ℝ)*base90 + (4878129/2000000000000000000000 : ℝ)*base92 + (4878129/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-85963/100000 : ℝ) ≤ (-49298456776878155809739818173069/57350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (153679941/100000000000000 : ℝ)*(lower0) + (189949859/100000000000000 : ℝ)*(lower1) + (132133219/100000000000000 : ℝ)*(lower3) + (59934743/100000000000000 : ℝ)*(lower4) + (126196019246121/5000000000000 : ℝ)*(major0) + (126196019246121/5000000000000 : ℝ)*(major1) + (126196019246121/5000000000000 : ℝ)*(major2) + (199561858179/100000000000000 : ℝ)*(sp5) + (184373388947/100000000000000 : ℝ)*(sp6) + (644473299/20000000000000 : ℝ)*(sp7) + (3527127005475127/100000000000000 : ℝ)*(sp12) + (881731860904237/25000000000000 : ℝ)*(sp13) + (176347131604309/5000000000000 : ℝ)*(sp14) + (193670513244217/12500000000000 : ℝ)*(sp15) + (1549367328320231/100000000000000 : ℝ)*(f.failure) + (3527127005475127/100000000000000 : ℝ)*(f.sum) + (3928413193133/1147000000000000000000000000 : ℝ)*base66 + (180718749596741023/114700000000000000000000000000000 : ℝ)*base67 + (1544148695311841023/114700000000000000000000000000000 : ℝ)*base69 + (785880256075458977/114700000000000000000000000000000 : ℝ)*base72 + (57730861827/143375000000000000000000000 : ℝ)*base74 + (1363914784703441023/114700000000000000000000000000000 : ℝ)*base75 + (846102388741241023/114700000000000000000000000000000 : ℝ)*base77 + (379825440137858977/114700000000000000000000000000000 : ℝ)*base80 + (7387629467873/1147000000000000000000000000 : ℝ)*base81 + (5856997/2000000000000000000000 : ℝ)*base90 + (5856997/2000000000000000000000 : ℝ)*base92 + (5856997/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1506_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10893/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15933/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58599/100000 : ℝ) else (16051/20000 : ℝ) ≤ X j i ∧ X j i ≤ (85963/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1506_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1506_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2723/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15933/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58599/100000 : ℝ) else (16051/20000 : ℝ) ≤ X j i ∧ X j i ≤ (85963/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1506_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1506_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4507/1024 : ℝ) ≤ p) (hpb : p ≤ (4509/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32580013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2723/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15933/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58599/100000 : ℝ) else (16051/20000 : ℝ) ≤ X j i ∧ X j i ≤ (85963/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1506_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
