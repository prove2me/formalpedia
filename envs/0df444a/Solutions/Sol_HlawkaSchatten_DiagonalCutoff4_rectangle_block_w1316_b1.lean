-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1316_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:42:12.352753+00:00
-- url     : https://prove2.me/submissions/26ce5ddd-2830-4f71-9ec6-0e1d54e981e9

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
theorem support_rectangle_w1316_s3_0 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-412920157/2000000000 : ℝ)*x 0 + (67882893/125000000 : ℝ)*x 1 + (5228533649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412920157/2000000000 : ℝ)^1069 ≤ (1570361108859/12500000000000 : ℝ)^813 := by
    have hnat : (412920157 : ℕ)^1069*12500000000000^813 ≤ 1570361108859^813*2000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412920157 2000000000 1570361108859 12500000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67882893/125000000 : ℝ)^1069 ≤ (44808372129211/100000000000000 : ℝ)^813 := by
    have hnat : (67882893 : ℕ)^1069*100000000000000^813 ≤ 44808372129211^813*125000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67882893 125000000 44808372129211 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228533649/10000000000 : ℝ)^1069 ≤ (4262873898003/10000000000000 : ℝ)^813 := by
    have hnat : (5228533649 : ℕ)^1069*10000000000000^813 ≤ 4262873898003^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228533649 10000000000 4262873898003 10000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-412920157/2000000000 : ℝ), (67882893/125000000 : ℝ), (5228533649/10000000000 : ℝ)] ![(1570361108859/12500000000000 : ℝ), (44808372129211/100000000000000 : ℝ), (4262873898003/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-412920157/2000000000 : ℝ)|^1069 ≤ (1570361108859/12500000000000 : ℝ)^813
        have hw : |(-412920157/2000000000 : ℝ)|=(412920157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67882893/125000000 : ℝ)|^1069 ≤ (44808372129211/100000000000000 : ℝ)^813
        have hw : |(67882893/125000000 : ℝ)|=(67882893/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228533649/10000000000 : ℝ)|^1069 ≤ (4262873898003/10000000000000 : ℝ)^813
        have hw : |(5228533649/10000000000 : ℝ)|=(5228533649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s3_1 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (167301281/312500000 : ℝ)*x 0 + (-2167959453/10000000000 : ℝ)*x 1 + (653566709/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167301281/312500000 : ℝ)^1069 ≤ (21987480568921/50000000000000 : ℝ)^813 := by
    have hnat : (167301281 : ℕ)^1069*50000000000000^813 ≤ 21987480568921^813*312500000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167301281 312500000 21987480568921 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2167959453/10000000000 : ℝ)^1069 ≤ (3349074906527/25000000000000 : ℝ)^813 := by
    have hnat : (2167959453 : ℕ)^1069*25000000000000^813 ≤ 3349074906527^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167959453 10000000000 3349074906527 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (653566709/1250000000 : ℝ)^1069 ≤ (21314369613299/50000000000000 : ℝ)^813 := by
    have hnat : (653566709 : ℕ)^1069*50000000000000^813 ≤ 21314369613299^813*1250000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653566709 1250000000 21314369613299 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167301281/312500000 : ℝ), (-2167959453/10000000000 : ℝ), (653566709/1250000000 : ℝ)] ![(21987480568921/50000000000000 : ℝ), (3349074906527/25000000000000 : ℝ), (21314369613299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167301281/312500000 : ℝ)|^1069 ≤ (21987480568921/50000000000000 : ℝ)^813
        have hw : |(167301281/312500000 : ℝ)|=(167301281/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2167959453/10000000000 : ℝ)|^1069 ≤ (3349074906527/25000000000000 : ℝ)^813
        have hw : |(-2167959453/10000000000 : ℝ)|=(2167959453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(653566709/1250000000 : ℝ)|^1069 ≤ (21314369613299/50000000000000 : ℝ)^813
        have hw : |(653566709/1250000000 : ℝ)|=(653566709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s3_2 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5353640869/10000000000 : ℝ)*x 0 + (326783369/625000000 : ℝ)*x 1 + (-216795931/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353640869/10000000000 : ℝ)^1069 ≤ (21987479904691/50000000000000 : ℝ)^813 := by
    have hnat : (5353640869 : ℕ)^1069*50000000000000^813 ≤ 21987479904691^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353640869 10000000000 21987479904691 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326783369/625000000 : ℝ)^1069 ≤ (10657185428431/25000000000000 : ℝ)^813 := by
    have hnat : (326783369 : ℕ)^1069*25000000000000^813 ≤ 10657185428431^813*625000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326783369 625000000 10657185428431 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216795931/1000000000 : ℝ)^1069 ≤ (167453730803/1250000000000 : ℝ)^813 := by
    have hnat : (216795931 : ℕ)^1069*1250000000000^813 ≤ 167453730803^813*1000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216795931 1000000000 167453730803 1250000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353640869/10000000000 : ℝ), (326783369/625000000 : ℝ), (-216795931/1000000000 : ℝ)] ![(21987479904691/50000000000000 : ℝ), (10657185428431/25000000000000 : ℝ), (167453730803/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353640869/10000000000 : ℝ)|^1069 ≤ (21987479904691/50000000000000 : ℝ)^813
        have hw : |(5353640869/10000000000 : ℝ)|=(5353640869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326783369/625000000 : ℝ)|^1069 ≤ (10657185428431/25000000000000 : ℝ)^813
        have hw : |(326783369/625000000 : ℝ)|=(326783369/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-216795931/1000000000 : ℝ)|^1069 ≤ (167453730803/1250000000000 : ℝ)^813
        have hw : |(-216795931/1000000000 : ℝ)|=(216795931/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s3_3 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1083057011/2500000000 : ℝ)*x 0 + (515929187/1250000000 : ℝ)*x 1 + (2273302213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083057011/2500000000 : ℝ)^1069 ≤ (1331612348463/4000000000000 : ℝ)^813 := by
    have hnat : (1083057011 : ℕ)^1069*4000000000000^813 ≤ 1331612348463^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083057011 2500000000 1331612348463 4000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515929187/1250000000 : ℝ)^1069 ≤ (1561831664619/5000000000000 : ℝ)^813 := by
    have hnat : (515929187 : ℕ)^1069*5000000000000^813 ≤ 1561831664619^813*1250000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515929187 1250000000 1561831664619 5000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273302213/5000000000 : ℝ)^1069 ≤ (1418922319031/4000000000000 : ℝ)^813 := by
    have hnat : (2273302213 : ℕ)^1069*4000000000000^813 ≤ 1418922319031^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273302213 5000000000 1418922319031 4000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083057011/2500000000 : ℝ), (515929187/1250000000 : ℝ), (2273302213/5000000000 : ℝ)] ![(1331612348463/4000000000000 : ℝ), (1561831664619/5000000000000 : ℝ), (1418922319031/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083057011/2500000000 : ℝ)|^1069 ≤ (1331612348463/4000000000000 : ℝ)^813
        have hw : |(1083057011/2500000000 : ℝ)|=(1083057011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(515929187/1250000000 : ℝ)|^1069 ≤ (1561831664619/5000000000000 : ℝ)^813
        have hw : |(515929187/1250000000 : ℝ)|=(515929187/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2273302213/5000000000 : ℝ)|^1069 ≤ (1418922319031/4000000000000 : ℝ)^813
        have hw : |(2273302213/5000000000 : ℝ)|=(2273302213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s3_4 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2064621643/10000000000 : ℝ)*x 0 + (40854607/78125000 : ℝ)*x 1 + (542977013/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2064621643/10000000000 : ℝ)^1069 ≤ (12563055754581/100000000000000 : ℝ)^813 := by
    have hnat : (2064621643 : ℕ)^1069*100000000000000^813 ≤ 12563055754581^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064621643 10000000000 12563055754581 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40854607/78125000 : ℝ)^1069 ≤ (8527583271277/20000000000000 : ℝ)^813 := by
    have hnat : (40854607 : ℕ)^1069*20000000000000^813 ≤ 8527583271277^813*78125000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40854607 78125000 8527583271277 20000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542977013/1000000000 : ℝ)^1069 ≤ (44799027875087/100000000000000 : ℝ)^813 := by
    have hnat : (542977013 : ℕ)^1069*100000000000000^813 ≤ 44799027875087^813*1000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542977013 1000000000 44799027875087 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2064621643/10000000000 : ℝ), (40854607/78125000 : ℝ), (542977013/1000000000 : ℝ)] ![(12563055754581/100000000000000 : ℝ), (8527583271277/20000000000000 : ℝ), (44799027875087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2064621643/10000000000 : ℝ)|^1069 ≤ (12563055754581/100000000000000 : ℝ)^813
        have hw : |(-2064621643/10000000000 : ℝ)|=(2064621643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40854607/78125000 : ℝ)|^1069 ≤ (8527583271277/20000000000000 : ℝ)^813
        have hw : |(40854607/78125000 : ℝ)|=(40854607/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542977013/1000000000 : ℝ)|^1069 ≤ (44799027875087/100000000000000 : ℝ)^813
        have hw : |(542977013/1000000000 : ℝ)|=(542977013/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s3_5 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (265087119/500000000 : ℝ)*x 0 + (-1966722909/10000000000 : ℝ)*x 1 + (1357442523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265087119/500000000 : ℝ)^1069 ≤ (8683057642521/20000000000000 : ℝ)^813 := by
    have hnat : (265087119 : ℕ)^1069*20000000000000^813 ≤ 8683057642521^813*500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265087119 500000000 8683057642521 20000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1966722909/10000000000 : ℝ)^1069 ≤ (1178568431611/10000000000000 : ℝ)^813 := by
    have hnat : (1966722909 : ℕ)^1069*10000000000000^813 ≤ 1178568431611^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966722909 10000000000 1178568431611 10000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357442523/2500000000 : ℝ)^1069 ≤ (1119975686571/2500000000000 : ℝ)^813 := by
    have hnat : (1357442523 : ℕ)^1069*2500000000000^813 ≤ 1119975686571^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357442523 2500000000 1119975686571 2500000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265087119/500000000 : ℝ), (-1966722909/10000000000 : ℝ), (1357442523/2500000000 : ℝ)] ![(8683057642521/20000000000000 : ℝ), (1178568431611/10000000000000 : ℝ), (1119975686571/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265087119/500000000 : ℝ)|^1069 ≤ (8683057642521/20000000000000 : ℝ)^813
        have hw : |(265087119/500000000 : ℝ)|=(265087119/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1966722909/10000000000 : ℝ)|^1069 ≤ (1178568431611/10000000000000 : ℝ)^813
        have hw : |(-1966722909/10000000000 : ℝ)|=(1966722909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357442523/2500000000 : ℝ)|^1069 ≤ (1119975686571/2500000000000 : ℝ)^813
        have hw : |(1357442523/2500000000 : ℝ)|=(1357442523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s3_6 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2650871261/5000000000 : ℝ)*x 0 + (1357442491/2500000000 : ℝ)*x 1 + (-196672289/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650871261/5000000000 : ℝ)^1069 ≤ (43415289741577/100000000000000 : ℝ)^813 := by
    have hnat : (2650871261 : ℕ)^1069*100000000000000^813 ≤ 43415289741577^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650871261 5000000000 43415289741577 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357442491/2500000000 : ℝ)^1069 ≤ (44799026074217/100000000000000 : ℝ)^813 := by
    have hnat : (1357442491 : ℕ)^1069*100000000000000^813 ≤ 44799026074217^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357442491 2500000000 44799026074217 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (196672289/1000000000 : ℝ)^1069 ≤ (11785684166399/100000000000000 : ℝ)^813 := by
    have hnat : (196672289 : ℕ)^1069*100000000000000^813 ≤ 11785684166399^813*1000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196672289 1000000000 11785684166399 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650871261/5000000000 : ℝ), (1357442491/2500000000 : ℝ), (-196672289/1000000000 : ℝ)] ![(43415289741577/100000000000000 : ℝ), (44799026074217/100000000000000 : ℝ), (11785684166399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650871261/5000000000 : ℝ)|^1069 ≤ (43415289741577/100000000000000 : ℝ)^813
        have hw : |(2650871261/5000000000 : ℝ)|=(2650871261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357442491/2500000000 : ℝ)|^1069 ≤ (44799026074217/100000000000000 : ℝ)^813
        have hw : |(1357442491/2500000000 : ℝ)|=(1357442491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-196672289/1000000000 : ℝ)|^1069 ≤ (11785684166399/100000000000000 : ℝ)^813
        have hw : |(-196672289/1000000000 : ℝ)|=(196672289/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s3_7 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4332271453/10000000000 : ℝ)*x 0 + (71012951/156250000 : ℝ)*x 1 + (2064609829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4332271453/10000000000 : ℝ)^1069 ≤ (33290747317141/100000000000000 : ℝ)^813 := by
    have hnat : (4332271453 : ℕ)^1069*100000000000000^813 ≤ 33290747317141^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4332271453 10000000000 33290747317141 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71012951/156250000 : ℝ)^1069 ≤ (35454843874207/100000000000000 : ℝ)^813 := by
    have hnat : (71012951 : ℕ)^1069*100000000000000^813 ≤ 35454843874207^813*156250000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71012951 156250000 35454843874207 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064609829/5000000000 : ℝ)^1069 ≤ (6250881757661/20000000000000 : ℝ)^813 := by
    have hnat : (2064609829 : ℕ)^1069*20000000000000^813 ≤ 6250881757661^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064609829 5000000000 6250881757661 20000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4332271453/10000000000 : ℝ), (71012951/156250000 : ℝ), (2064609829/5000000000 : ℝ)] ![(33290747317141/100000000000000 : ℝ), (35454843874207/100000000000000 : ℝ), (6250881757661/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4332271453/10000000000 : ℝ)|^1069 ≤ (33290747317141/100000000000000 : ℝ)^813
        have hw : |(4332271453/10000000000 : ℝ)|=(4332271453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(71012951/156250000 : ℝ)|^1069 ≤ (35454843874207/100000000000000 : ℝ)^813
        have hw : |(71012951/156250000 : ℝ)|=(71012951/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2064609829/5000000000 : ℝ)|^1069 ≤ (6250881757661/20000000000000 : ℝ)^813
        have hw : |(2064609829/5000000000 : ℝ)|=(2064609829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1316_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16211/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2419/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10761/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15037/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16211/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2419/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16211/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2419/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16211/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2419/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16211/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2419/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16211/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2419/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16211/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2419/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2419/25000 : ℝ) ^ (4275/1024 : ℝ) ≤ (5827446840769613/100000000000000000000 : ℝ) := by
    have hpowers : (2419/25000 : ℝ)^4275 ≤ (5827446840769613/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2419 : ℕ)^4275*100000000000000000000^1024 ≤ 5827446840769613^1024*25000^4275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2419 25000 5827446840769613 100000000000000000000 4275 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2419/25000 : ℝ)) (X := (5827446840769613/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16211/100000 : ℝ) ^ (4275/1024 : ℝ) ≤ (25123507860899607/50000000000000000000 : ℝ) := by
    have hpowers : (16211/100000 : ℝ)^4275 ≤ (25123507860899607/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16211 : ℕ)^4275*50000000000000000000^1024 ≤ 25123507860899607^1024*100000^4275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16211 100000 25123507860899607 50000000000000000000 4275 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16211/100000 : ℝ)) (X := (25123507860899607/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005827446840769613/50000000000000000000 : ℝ) ≤ (9765897617011/9765625000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (50005827446840769613/50000000000000000000 : ℝ)^1024 ≤ (9765897617011/9765625000000 : ℝ)^4275 := by
      have hnat : (50005827446840769613 : ℕ)^1024*9765625000000^4275 ≤ 9765897617011^4275*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005827446840769613 50000000000000000000 9765897617011 9765625000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (9765897617011/9765625000000 : ℝ)) (X := (50005827446840769613/50000000000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100056074462562568827/100000000000000000000 : ℝ) ≤ (200026857548951/200000000000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (100056074462562568827/100000000000000000000 : ℝ)^1024 ≤ (200026857548951/200000000000000 : ℝ)^4275 := by
      have hnat : (100056074462562568827 : ℕ)^1024*200000000000000^4275 ≤ 200026857548951^4275*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100056074462562568827 100000000000000000000 200026857548951 200000000000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200026857548951/200000000000000 : ℝ)) (X := (100056074462562568827/100000000000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25025123507860899607/25000000000000000000 : ℝ) ≤ (2500601648768959/2500000000000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (25025123507860899607/25000000000000000000 : ℝ)^1024 ≤ (2500601648768959/2500000000000000 : ℝ)^4275 := by
      have hnat : (25025123507860899607 : ℕ)^1024*2500000000000000^4275 ≤ 2500601648768959^4275*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25025123507860899607 25000000000000000000 2500601648768959 2500000000000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500601648768959/2500000000000000 : ℝ)) (X := (25025123507860899607/25000000000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5827446840769613/100000000000000000000 : ℝ) ≤ ((4083202452867268723/4084375000000000000 : ℝ)+2*(531858814143/326750000000000 : ℝ)*(2419/25000 : ℝ))^(4275/1024 : ℝ) := by
    rw [show (4083202452867268723/4084375000000000000 : ℝ)+2*(531858814143/326750000000000 : ℝ)*(2419/25000 : ℝ)=(9765897617011/9765625000000 : ℝ) by norm_num, show 1+2*(5827446840769613/100000000000000000000 : ℝ)=(50005827446840769613/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25123507860899607/50000000000000000000 : ℝ)+(5827446840769613/100000000000000000000 : ℝ) ≤ ((4083202452867268723/4084375000000000000 : ℝ)+(531858814143/326750000000000 : ℝ)*((16211/100000 : ℝ)+(2419/25000 : ℝ)))^(4275/1024 : ℝ) := by
    rw [show (4083202452867268723/4084375000000000000 : ℝ)+(531858814143/326750000000000 : ℝ)*((16211/100000 : ℝ)+(2419/25000 : ℝ))=(200026857548951/200000000000000 : ℝ) by norm_num, show 1+(25123507860899607/50000000000000000000 : ℝ)+(5827446840769613/100000000000000000000 : ℝ)=(100056074462562568827/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25123507860899607/50000000000000000000 : ℝ) ≤ ((4083202452867268723/4084375000000000000 : ℝ)+2*(531858814143/326750000000000 : ℝ)*(16211/100000 : ℝ))^(4275/1024 : ℝ) := by
    rw [show (4083202452867268723/4084375000000000000 : ℝ)+2*(531858814143/326750000000000 : ℝ)*(16211/100000 : ℝ)=(2500601648768959/2500000000000000 : ℝ) by norm_num, show 1+2*(25123507860899607/50000000000000000000 : ℝ)=(25025123507860899607/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4083202452867268723/4084375000000000000 : ℝ)*(X 1 0+X 2 0)+(531858814143/326750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (2419/25000 : ℝ)) (hi := (16211/100000 : ℝ)) (c := (4083202452867268723/4084375000000000000 : ℝ)) (alpha := (531858814143/326750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4083202452867268723/4084375000000000000 : ℝ)*(X 0 1+X 2 1)+(531858814143/326750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (2419/25000 : ℝ)) (hi := (16211/100000 : ℝ)) (c := (4083202452867268723/4084375000000000000 : ℝ)) (alpha := (531858814143/326750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4083202452867268723/4084375000000000000 : ℝ)*(X 0 2+X 1 2)+(531858814143/326750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (2419/25000 : ℝ)) (hi := (16211/100000 : ℝ)) (c := (4083202452867268723/4084375000000000000 : ℝ)) (alpha := (531858814143/326750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-412920157/2000000000 : ℝ)*X 0 0+(67882893/125000000 : ℝ)*X 0 1+(5228533649/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167301281/312500000 : ℝ)*X 1 0+(-2167959453/10000000000 : ℝ)*X 1 1+(653566709/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353640869/10000000000 : ℝ)*X 2 0+(326783369/625000000 : ℝ)*X 2 1+(-216795931/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1083057011/2500000000 : ℝ)*X 0 0+(515929187/1250000000 : ℝ)*X 0 1+(2273302213/5000000000 : ℝ)*X 0 2+(1083057011/2500000000 : ℝ)*X 1 0+(515929187/1250000000 : ℝ)*X 1 1+(2273302213/5000000000 : ℝ)*X 1 2+(1083057011/2500000000 : ℝ)*X 2 0+(515929187/1250000000 : ℝ)*X 2 1+(2273302213/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2064621643/10000000000 : ℝ)*X 0 0+(40854607/78125000 : ℝ)*X 0 1+(542977013/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265087119/500000000 : ℝ)*X 1 0+(-1966722909/10000000000 : ℝ)*X 1 1+(1357442523/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2650871261/5000000000 : ℝ)*X 2 0+(1357442491/2500000000 : ℝ)*X 2 1+(-196672289/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4332271453/10000000000 : ℝ)*X 0 0+(71012951/156250000 : ℝ)*X 0 1+(2064609829/5000000000 : ℝ)*X 0 2+(4332271453/10000000000 : ℝ)*X 1 0+(71012951/156250000 : ℝ)*X 1 1+(2064609829/5000000000 : ℝ)*X 1 2+(4332271453/10000000000 : ℝ)*X 2 0+(71012951/156250000 : ℝ)*X 2 1+(2064609829/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (522218408918231369742060471/102109375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (783202969/100000000000000 : ℝ)*(base19) + (318205447/50000000000000 : ℝ)*(base23) + (40549279/100000000000000 : ℝ)*(upper3) + (8862603/50000000000000 : ℝ)*(upper4) + (35965007/25000000000000 : ℝ)*(upper5) + (1833451525492147/50000000000000 : ℝ)*(major0) + (1833451525492147/50000000000000 : ℝ)*(major1) + (1833451525492147/50000000000000 : ℝ)*(major2) + (4948113683884019/100000000000000 : ℝ)*(sp0) + (4948130021537079/100000000000000 : ℝ)*(sp1) + (2474065084164577/50000000000000 : ℝ)*(sp2) + (7455215986983/312500000000 : ℝ)*(sp3) + (17120856029/100000000000000 : ℝ)*(sp4) + (3005458581/50000000000000 : ℝ)*(sp7) + (2385675126751723/100000000000000 : ℝ)*(f.failure) + (309258175296253/6250000000000 : ℝ)*(f.sum) + (9209364607221/8168750000000000000000000000 : ℝ)*base65 + (1078401377665480781/204218750000000000000000000000000 : ℝ)*base67 + (2393022416041262031/204218750000000000000000000000000 : ℝ)*base69 + (2264912494469543281/204218750000000000000000000000000 : ℝ)*base71 + (70788695667909/32675000000000000000000000000 : ℝ)*base73 + (3598208139789855781/204218750000000000000000000000000 : ℝ)*base75 + (2404546562812355781/204218750000000000000000000000000 : ℝ)*base77 + (3309776581992980781/204218750000000000000000000000000 : ℝ)*base79 + (28642633368071/8168750000000000000000000000 : ℝ)*base81 + (7147129/5000000000000000000000 : ℝ)*base89 + (7147129/5000000000000000000000 : ℝ)*base91 + (7147129/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18150766012807801913941863/2042187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1937205997/100000000000000 : ℝ)*(base19) + (2174768897/100000000000000 : ℝ)*(base23) + (3284213/1562500000000 : ℝ)*(upper3) + (8653707/20000000000000 : ℝ)*(lower4) + (43248599/20000000000000 : ℝ)*(upper5) + (73966144367307/2000000000000 : ℝ)*(major0) + (73966144367307/2000000000000 : ℝ)*(major1) + (73966144367307/2000000000000 : ℝ)*(major2) + (32608119207/100000000000000 : ℝ)*(sp1) + (34885047573/100000000000000 : ℝ)*(sp2) + (1247626891293197/25000000000000 : ℝ)*(sp4) + (998094603969517/20000000000000 : ℝ)*(sp5) + (2495235252678159/50000000000000 : ℝ)*(sp6) + (601526643823611/25000000000000 : ℝ)*(sp7) + (601526643823611/25000000000000 : ℝ)*(f.failure) + (1247626891293197/25000000000000 : ℝ)*(f.sum) + (42044621483/326750000000000000000000000 : ℝ)*base66 + (112795520698301461/8168750000000000000000000000000 : ℝ)*base67 + (103286454222701461/8168750000000000000000000000000 : ℝ)*base69 + (80267813782151461/8168750000000000000000000000000 : ℝ)*base71 + (531585709011/326750000000000000000000000 : ℝ)*base73 + (11390929012776461/8168750000000000000000000000000 : ℝ)*base75 + (140952401402632711/8168750000000000000000000000000 : ℝ)*base77 + (42130481882851461/8168750000000000000000000000000 : ℝ)*base79 + (278988919349/130700000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2679447/1250000000000000000000 : ℝ)*base90 + (2679447/1250000000000000000000 : ℝ)*base92 + (2679447/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1316_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16211/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2419/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10761/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15037/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1316_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1316_s4_0 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2066283329/10000000000 : ℝ)*x 0 + (541712681/1000000000 : ℝ)*x 1 + (65511683/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2066283329/10000000000 : ℝ)^1069 ≤ (2515270503651/20000000000000 : ℝ)^813 := by
    have hnat : (2066283329 : ℕ)^1069*20000000000000^813 ≤ 2515270503651^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066283329 10000000000 2515270503651 20000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541712681/1000000000 : ℝ)^1069 ≤ (22330957836351/50000000000000 : ℝ)^813 := by
    have hnat : (541712681 : ℕ)^1069*50000000000000^813 ≤ 22330957836351^813*1000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541712681 1000000000 22330957836351 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65511683/125000000 : ℝ)^1069 ≤ (8552346359457/20000000000000 : ℝ)^813 := by
    have hnat : (65511683 : ℕ)^1069*20000000000000^813 ≤ 8552346359457^813*125000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65511683 125000000 8552346359457 20000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2066283329/10000000000 : ℝ), (541712681/1000000000 : ℝ), (65511683/125000000 : ℝ)] ![(2515270503651/20000000000000 : ℝ), (22330957836351/50000000000000 : ℝ), (8552346359457/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2066283329/10000000000 : ℝ)|^1069 ≤ (2515270503651/20000000000000 : ℝ)^813
        have hw : |(-2066283329/10000000000 : ℝ)|=(2066283329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541712681/1000000000 : ℝ)|^1069 ≤ (22330957836351/50000000000000 : ℝ)^813
        have hw : |(541712681/1000000000 : ℝ)|=(541712681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65511683/125000000 : ℝ)|^1069 ≤ (8552346359457/20000000000000 : ℝ)^813
        have hw : |(65511683/125000000 : ℝ)|=(65511683/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s4_1 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1070042957/2000000000 : ℝ)*x 0 + (-2156135257/10000000000 : ℝ)*x 1 + (2620467173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070042957/2000000000 : ℝ)^1069 ≤ (43937960159303/100000000000000 : ℝ)^813 := by
    have hnat : (1070042957 : ℕ)^1069*100000000000000^813 ≤ 43937960159303^813*2000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070042957 2000000000 43937960159303 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2156135257/10000000000 : ℝ)^1069 ≤ (665015559419/5000000000000 : ℝ)^813 := by
    have hnat : (2156135257 : ℕ)^1069*5000000000000^813 ≤ 665015559419^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156135257 10000000000 665015559419 5000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620467173/5000000000 : ℝ)^1069 ≤ (8552345728629/20000000000000 : ℝ)^813 := by
    have hnat : (2620467173 : ℕ)^1069*20000000000000^813 ≤ 8552345728629^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620467173 5000000000 8552345728629 20000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070042957/2000000000 : ℝ), (-2156135257/10000000000 : ℝ), (2620467173/5000000000 : ℝ)] ![(43937960159303/100000000000000 : ℝ), (665015559419/5000000000000 : ℝ), (8552345728629/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070042957/2000000000 : ℝ)|^1069 ≤ (43937960159303/100000000000000 : ℝ)^813
        have hw : |(1070042957/2000000000 : ℝ)|=(1070042957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2156135257/10000000000 : ℝ)|^1069 ≤ (665015559419/5000000000000 : ℝ)^813
        have hw : |(-2156135257/10000000000 : ℝ)|=(2156135257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620467173/5000000000 : ℝ)|^1069 ≤ (8552345728629/20000000000000 : ℝ)^813
        have hw : |(2620467173/5000000000 : ℝ)|=(2620467173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s4_2 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1337553663/2500000000 : ℝ)*x 0 + (5240933961/10000000000 : ℝ)*x 1 + (-269516993/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337553663/2500000000 : ℝ)^1069 ≤ (5492244840391/12500000000000 : ℝ)^813 := by
    have hnat : (1337553663 : ℕ)^1069*12500000000000^813 ≤ 5492244840391^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337553663 2500000000 5492244840391 12500000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240933961/10000000000 : ℝ)^1069 ≤ (42761724512723/100000000000000 : ℝ)^813 := by
    have hnat : (5240933961 : ℕ)^1069*100000000000000^813 ≤ 42761724512723^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240933961 10000000000 42761724512723 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269516993/1250000000 : ℝ)^1069 ≤ (13300316760619/100000000000000 : ℝ)^813 := by
    have hnat : (269516993 : ℕ)^1069*100000000000000^813 ≤ 13300316760619^813*1250000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269516993 1250000000 13300316760619 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337553663/2500000000 : ℝ), (5240933961/10000000000 : ℝ), (-269516993/1250000000 : ℝ)] ![(5492244840391/12500000000000 : ℝ), (42761724512723/100000000000000 : ℝ), (13300316760619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337553663/2500000000 : ℝ)|^1069 ≤ (5492244840391/12500000000000 : ℝ)^813
        have hw : |(1337553663/2500000000 : ℝ)|=(1337553663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240933961/10000000000 : ℝ)|^1069 ≤ (42761724512723/100000000000000 : ℝ)^813
        have hw : |(5240933961/10000000000 : ℝ)|=(5240933961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-269516993/1250000000 : ℝ)|^1069 ≤ (13300316760619/100000000000000 : ℝ)^813
        have hw : |(-269516993/1250000000 : ℝ)|=(269516993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s4_3 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (866649793/2000000000 : ℝ)*x 0 + (4154170557/10000000000 : ℝ)*x 1 + (1129903049/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866649793/2000000000 : ℝ)^1069 ≤ (1332024979521/4000000000000 : ℝ)^813 := by
    have hnat : (866649793 : ℕ)^1069*4000000000000^813 ≤ 1332024979521^813*2000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866649793 2000000000 1332024979521 4000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4154170557/10000000000 : ℝ)^1069 ≤ (31502967539737/100000000000000 : ℝ)^813 := by
    have hnat : (4154170557 : ℕ)^1069*100000000000000^813 ≤ 31502967539737^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154170557 10000000000 31502967539737 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129903049/2500000000 : ℝ)^1069 ≤ (35196407954591/100000000000000 : ℝ)^813 := by
    have hnat : (1129903049 : ℕ)^1069*100000000000000^813 ≤ 35196407954591^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129903049 2500000000 35196407954591 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(866649793/2000000000 : ℝ), (4154170557/10000000000 : ℝ), (1129903049/2500000000 : ℝ)] ![(1332024979521/4000000000000 : ℝ), (31502967539737/100000000000000 : ℝ), (35196407954591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(866649793/2000000000 : ℝ)|^1069 ≤ (1332024979521/4000000000000 : ℝ)^813
        have hw : |(866649793/2000000000 : ℝ)|=(866649793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4154170557/10000000000 : ℝ)|^1069 ≤ (31502967539737/100000000000000 : ℝ)^813
        have hw : |(4154170557/10000000000 : ℝ)|=(4154170557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1129903049/2500000000 : ℝ)|^1069 ≤ (35196407954591/100000000000000 : ℝ)^813
        have hw : |(1129903049/2500000000 : ℝ)|=(1129903049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s4_4 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1033148457/5000000000 : ℝ)*x 0 + (209663437/400000000 : ℝ)*x 1 + (5416472217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033148457/5000000000 : ℝ)^1069 ≤ (2515292247783/20000000000000 : ℝ)^813 := by
    have hnat : (1033148457 : ℕ)^1069*20000000000000^813 ≤ 2515292247783^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033148457 5000000000 2515292247783 20000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209663437/400000000 : ℝ)^1069 ≤ (4276871915977/10000000000000 : ℝ)^813 := by
    have hnat : (209663437 : ℕ)^1069*10000000000000^813 ≤ 4276871915977^813*400000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209663437 400000000 4276871915977 10000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416472217/10000000000 : ℝ)^1069 ≤ (44654819591137/100000000000000 : ℝ)^813 := by
    have hnat : (5416472217 : ℕ)^1069*100000000000000^813 ≤ 44654819591137^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416472217 10000000000 44654819591137 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1033148457/5000000000 : ℝ), (209663437/400000000 : ℝ), (5416472217/10000000000 : ℝ)] ![(2515292247783/20000000000000 : ℝ), (4276871915977/10000000000000 : ℝ), (44654819591137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1033148457/5000000000 : ℝ)|^1069 ≤ (2515292247783/20000000000000 : ℝ)^813
        have hw : |(-1033148457/5000000000 : ℝ)|=(1033148457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209663437/400000000 : ℝ)|^1069 ≤ (4276871915977/10000000000000 : ℝ)^813
        have hw : |(209663437/400000000 : ℝ)|=(209663437/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416472217/10000000000 : ℝ)|^1069 ≤ (44654819591137/100000000000000 : ℝ)^813
        have hw : |(5416472217/10000000000 : ℝ)|=(5416472217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s4_5 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5304971039/10000000000 : ℝ)*x 0 + (-79223919/400000000 : ℝ)*x 1 + (541647133/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304971039/10000000000 : ℝ)^1069 ≤ (869001116773/2000000000000 : ℝ)^813 := by
    have hnat : (5304971039 : ℕ)^1069*2000000000000^813 ≤ 869001116773^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304971039 10000000000 869001116773 2000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79223919/400000000 : ℝ)^1069 ≤ (5947567085497/50000000000000 : ℝ)^813 := by
    have hnat : (79223919 : ℕ)^1069*50000000000000^813 ≤ 5947567085497^813*400000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79223919 400000000 5947567085497 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541647133/1000000000 : ℝ)^1069 ≤ (44654809975843/100000000000000 : ℝ)^813 := by
    have hnat : (541647133 : ℕ)^1069*100000000000000^813 ≤ 44654809975843^813*1000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541647133 1000000000 44654809975843 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304971039/10000000000 : ℝ), (-79223919/400000000 : ℝ), (541647133/1000000000 : ℝ)] ![(869001116773/2000000000000 : ℝ), (5947567085497/50000000000000 : ℝ), (44654809975843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304971039/10000000000 : ℝ)|^1069 ≤ (869001116773/2000000000000 : ℝ)^813
        have hw : |(5304971039/10000000000 : ℝ)|=(5304971039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-79223919/400000000 : ℝ)|^1069 ≤ (5947567085497/50000000000000 : ℝ)^813
        have hw : |(-79223919/400000000 : ℝ)|=(79223919/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541647133/1000000000 : ℝ)|^1069 ≤ (44654809975843/100000000000000 : ℝ)^813
        have hw : |(541647133/1000000000 : ℝ)|=(541647133/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s4_6 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (42439759/80000000 : ℝ)*x 0 + (2708236383/5000000000 : ℝ)*x 1 + (-1980597591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42439759/80000000 : ℝ)^1069 ≤ (43450043302983/100000000000000 : ℝ)^813 := by
    have hnat : (42439759 : ℕ)^1069*100000000000000^813 ≤ 43450043302983^813*80000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42439759 80000000 43450043302983 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708236383/5000000000 : ℝ)^1069 ≤ (4465482554243/10000000000000 : ℝ)^813 := by
    have hnat : (2708236383 : ℕ)^1069*10000000000000^813 ≤ 4465482554243^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708236383 5000000000 4465482554243 10000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1980597591/10000000000 : ℝ)^1069 ≤ (4646535601/39062500000 : ℝ)^813 := by
    have hnat : (1980597591 : ℕ)^1069*39062500000^813 ≤ 4646535601^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980597591 10000000000 4646535601 39062500000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42439759/80000000 : ℝ), (2708236383/5000000000 : ℝ), (-1980597591/10000000000 : ℝ)] ![(43450043302983/100000000000000 : ℝ), (4465482554243/10000000000000 : ℝ), (4646535601/39062500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42439759/80000000 : ℝ)|^1069 ≤ (43450043302983/100000000000000 : ℝ)^813
        have hw : |(42439759/80000000 : ℝ)|=(42439759/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708236383/5000000000 : ℝ)|^1069 ≤ (4465482554243/10000000000000 : ℝ)^813
        have hw : |(2708236383/5000000000 : ℝ)|=(2708236383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1980597591/10000000000 : ℝ)|^1069 ≤ (4646535601/39062500000 : ℝ)^813
        have hw : |(-1980597591/10000000000 : ℝ)|=(1980597591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s4_7 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1083319439/2500000000 : ℝ)*x 0 + (4518261561/10000000000 : ℝ)*x 1 + (4155528219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083319439/2500000000 : ℝ)^1069 ≤ (16650457707201/50000000000000 : ℝ)^813 := by
    have hnat : (1083319439 : ℕ)^1069*50000000000000^813 ≤ 16650457707201^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083319439 2500000000 16650457707201 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4518261561/10000000000 : ℝ)^1069 ≤ (8795644650137/25000000000000 : ℝ)^813 := by
    have hnat : (4518261561 : ℕ)^1069*25000000000000^813 ≤ 8795644650137^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518261561 10000000000 8795644650137 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4155528219/10000000000 : ℝ)^1069 ≤ (31516505969897/100000000000000 : ℝ)^813 := by
    have hnat : (4155528219 : ℕ)^1069*100000000000000^813 ≤ 31516505969897^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155528219 10000000000 31516505969897 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083319439/2500000000 : ℝ), (4518261561/10000000000 : ℝ), (4155528219/10000000000 : ℝ)] ![(16650457707201/50000000000000 : ℝ), (8795644650137/25000000000000 : ℝ), (31516505969897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083319439/2500000000 : ℝ)|^1069 ≤ (16650457707201/50000000000000 : ℝ)^813
        have hw : |(1083319439/2500000000 : ℝ)|=(1083319439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4518261561/10000000000 : ℝ)|^1069 ≤ (8795644650137/25000000000000 : ℝ)^813
        have hw : |(4518261561/10000000000 : ℝ)|=(4518261561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4155528219/10000000000 : ℝ)|^1069 ≤ (31516505969897/100000000000000 : ℝ)^813
        have hw : |(4155528219/10000000000 : ℝ)|=(4155528219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1316_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15037/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10761/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5513/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2951/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15037/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10761/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15037/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10761/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15037/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10761/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15037/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10761/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15037/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10761/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15037/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10761/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10761/100000 : ℝ) ^ (4275/1024 : ℝ) ≤ (9081839601487049/100000000000000000000 : ℝ) := by
    have hpowers : (10761/100000 : ℝ)^4275 ≤ (9081839601487049/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10761 : ℕ)^4275*100000000000000000000^1024 ≤ 9081839601487049^1024*100000^4275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10761 100000 9081839601487049 100000000000000000000 4275 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10761/100000 : ℝ)) (X := (9081839601487049/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15037/100000 : ℝ) ^ (4275/1024 : ℝ) ≤ (2294503565545869/6250000000000000000 : ℝ) := by
    have hpowers : (15037/100000 : ℝ)^4275 ≤ (2294503565545869/6250000000000000000 : ℝ)^1024 := by
      have hnat : (15037 : ℕ)^4275*6250000000000000000^1024 ≤ 2294503565545869^1024*100000^4275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15037 100000 2294503565545869 6250000000000000000 4275 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15037/100000 : ℝ)) (X := (2294503565545869/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009081839601487049/50000000000000000000 : ℝ) ≤ (2500108762123209/2500000000000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (50009081839601487049/50000000000000000000 : ℝ)^1024 ≤ (2500108762123209/2500000000000000 : ℝ)^4275 := by
      have hnat : (50009081839601487049 : ℕ)^1024*2500000000000000^4275 ≤ 2500108762123209^4275*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009081839601487049 50000000000000000000 2500108762123209 2500000000000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500108762123209/2500000000000000 : ℝ)) (X := (50009081839601487049/50000000000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045793896650220953/100000000000000000000 : ℝ) ≤ (10001096720167923/10000000000000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (100045793896650220953/100000000000000000000 : ℝ)^1024 ≤ (10001096720167923/10000000000000000 : ℝ)^4275 := by
      have hnat : (100045793896650220953 : ℕ)^1024*10000000000000000^4275 ≤ 10001096720167923^4275*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045793896650220953 100000000000000000000 10001096720167923 10000000000000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001096720167923/10000000000000000 : ℝ)) (X := (100045793896650220953/100000000000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127294503565545869/3125000000000000000 : ℝ) ≤ (1000175839184301/1000000000000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (3127294503565545869/3125000000000000000 : ℝ)^1024 ≤ (1000175839184301/1000000000000000 : ℝ)^4275 := by
      have hnat : (3127294503565545869 : ℕ)^1024*1000000000000000^4275 ≤ 1000175839184301^4275*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127294503565545869 3125000000000000000 1000175839184301 1000000000000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000175839184301/1000000000000000 : ℝ)) (X := (3127294503565545869/3125000000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9081839601487049/100000000000000000000 : ℝ) ≤ ((21373809884782072161/21380000000000000000 : ℝ)+2*(661671675087/427600000000000 : ℝ)*(10761/100000 : ℝ))^(4275/1024 : ℝ) := by
    rw [show (21373809884782072161/21380000000000000000 : ℝ)+2*(661671675087/427600000000000 : ℝ)*(10761/100000 : ℝ)=(2500108762123209/2500000000000000 : ℝ) by norm_num, show 1+2*(9081839601487049/100000000000000000000 : ℝ)=(50009081839601487049/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2294503565545869/6250000000000000000 : ℝ)+(9081839601487049/100000000000000000000 : ℝ) ≤ ((21373809884782072161/21380000000000000000 : ℝ)+(661671675087/427600000000000 : ℝ)*((15037/100000 : ℝ)+(10761/100000 : ℝ)))^(4275/1024 : ℝ) := by
    rw [show (21373809884782072161/21380000000000000000 : ℝ)+(661671675087/427600000000000 : ℝ)*((15037/100000 : ℝ)+(10761/100000 : ℝ))=(10001096720167923/10000000000000000 : ℝ) by norm_num, show 1+(2294503565545869/6250000000000000000 : ℝ)+(9081839601487049/100000000000000000000 : ℝ)=(100045793896650220953/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2294503565545869/6250000000000000000 : ℝ) ≤ ((21373809884782072161/21380000000000000000 : ℝ)+2*(661671675087/427600000000000 : ℝ)*(15037/100000 : ℝ))^(4275/1024 : ℝ) := by
    rw [show (21373809884782072161/21380000000000000000 : ℝ)+2*(661671675087/427600000000000 : ℝ)*(15037/100000 : ℝ)=(1000175839184301/1000000000000000 : ℝ) by norm_num, show 1+2*(2294503565545869/6250000000000000000 : ℝ)=(3127294503565545869/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21373809884782072161/21380000000000000000 : ℝ)*(X 1 0+X 2 0)+(661671675087/427600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (10761/100000 : ℝ)) (hi := (15037/100000 : ℝ)) (c := (21373809884782072161/21380000000000000000 : ℝ)) (alpha := (661671675087/427600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21373809884782072161/21380000000000000000 : ℝ)*(X 0 1+X 2 1)+(661671675087/427600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (10761/100000 : ℝ)) (hi := (15037/100000 : ℝ)) (c := (21373809884782072161/21380000000000000000 : ℝ)) (alpha := (661671675087/427600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21373809884782072161/21380000000000000000 : ℝ)*(X 0 2+X 1 2)+(661671675087/427600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (10761/100000 : ℝ)) (hi := (15037/100000 : ℝ)) (c := (21373809884782072161/21380000000000000000 : ℝ)) (alpha := (661671675087/427600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2066283329/10000000000 : ℝ)*X 0 0+(541712681/1000000000 : ℝ)*X 0 1+(65511683/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070042957/2000000000 : ℝ)*X 1 0+(-2156135257/10000000000 : ℝ)*X 1 1+(2620467173/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337553663/2500000000 : ℝ)*X 2 0+(5240933961/10000000000 : ℝ)*X 2 1+(-269516993/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((866649793/2000000000 : ℝ)*X 0 0+(4154170557/10000000000 : ℝ)*X 0 1+(1129903049/2500000000 : ℝ)*X 0 2+(866649793/2000000000 : ℝ)*X 1 0+(4154170557/10000000000 : ℝ)*X 1 1+(1129903049/2500000000 : ℝ)*X 1 2+(866649793/2000000000 : ℝ)*X 2 0+(4154170557/10000000000 : ℝ)*X 2 1+(1129903049/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1033148457/5000000000 : ℝ)*X 0 0+(209663437/400000000 : ℝ)*X 0 1+(5416472217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304971039/10000000000 : ℝ)*X 1 0+(-79223919/400000000 : ℝ)*X 1 1+(541647133/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((42439759/80000000 : ℝ)*X 2 0+(2708236383/5000000000 : ℝ)*X 2 1+(-1980597591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1083319439/2500000000 : ℝ)*X 0 0+(4518261561/10000000000 : ℝ)*X 0 1+(4155528219/10000000000 : ℝ)*X 0 2+(1083319439/2500000000 : ℝ)*X 1 0+(4518261561/10000000000 : ℝ)*X 1 1+(4155528219/10000000000 : ℝ)*X 1 2+(1083319439/2500000000 : ℝ)*X 2 0+(4518261561/10000000000 : ℝ)*X 2 1+(4155528219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (789323680186797724577842707/534500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1175972829/100000000000000 : ℝ)*(base19) + (429321319/50000000000000 : ℝ)*(base23) + (394301/4000000000000 : ℝ)*(upper2) + (24956663/100000000000000 : ℝ)*(upper3) + (2103028209110929/50000000000000 : ℝ)*(major0) + (2103028209110929/50000000000000 : ℝ)*(major1) + (2103028209110929/50000000000000 : ℝ)*(major2) + (709455661158783/12500000000000 : ℝ)*(sp0) + (5675665067895613/100000000000000 : ℝ)*(sp1) + (5675642366072901/100000000000000 : ℝ)*(sp2) + (1368215569707883/50000000000000 : ℝ)*(sp3) + (20954598177/100000000000000 : ℝ)*(sp4) + (23019152903/100000000000000 : ℝ)*(sp6) + (15403934449/100000000000000 : ℝ)*(sp7) + (342055817918777/12500000000000 : ℝ)*(f.failure) + (2837833121934221/50000000000000 : ℝ)*(f.sum) + (28321360365823/10690000000000000000000000000 : ℝ)*base65 + (4774425835418897569/1069000000000000000000000000000000 : ℝ)*base67 + (2585894356261102431/1069000000000000000000000000000000 : ℝ)*base70 + (1681889164468102431/1069000000000000000000000000000000 : ℝ)*base72 + (14851479208923/10690000000000000000000000000 : ℝ)*base73 + (12287636705562102431/1069000000000000000000000000000000 : ℝ)*base76 + (5207918061863897569/1069000000000000000000000000000000 : ℝ)*base77 + (11792929744167102431/1069000000000000000000000000000000 : ℝ)*base80 + (37655395333323/10690000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (9024371/625000000000000000000 : ℝ)*base89 + (9024371/625000000000000000000 : ℝ)*base91 + (9024371/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1168609982109288400798695057/133625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2320409409/100000000000000 : ℝ)*(base19) + (826089149/50000000000000 : ℝ)*(base23) + (123261797/50000000000000 : ℝ)*(upper3) + (41880137/20000000000000 : ℝ)*(lower4) + (529676753756379/12500000000000 : ℝ)*(major0) + (529676753756379/12500000000000 : ℝ)*(major1) + (529676753756379/12500000000000 : ℝ)*(major2) + (17651999781/100000000000000 : ℝ)*(sp1) + (10031080017/25000000000000 : ℝ)*(sp2) + (1631511577/100000000000000 : ℝ)*(sp3) + (1429495016396009/25000000000000 : ℝ)*(sp4) + (2858980046587423/50000000000000 : ℝ)*(sp5) + (571793828908567/10000000000000 : ℝ)*(sp6) + (689211517872909/25000000000000 : ℝ)*(sp7) + (1378423851501607/50000000000000 : ℝ)*(f.failure) + (1429495016396009/25000000000000 : ℝ)*(f.sum) + (20520452667419/5345000000000000000000000000 : ℝ)*base66 + (2900182324675534981/267250000000000000000000000000000 : ℝ)*base68 + (576269360197715019/267250000000000000000000000000000 : ℝ)*base69 + (3435090740134284981/267250000000000000000000000000000 : ℝ)*base72 + (546205030421/334062500000000000000000000 : ℝ)*base73 + (2983973892701215019/267250000000000000000000000000000 : ℝ)*base75 + (35451730630034981/267250000000000000000000000000000 : ℝ)*base78 + (1031730479048534981/267250000000000000000000000000000 : ℝ)*base80 + (41478334029/1336250000000000000000000000 : ℝ)*base81 + (36504461/2500000000000000000000 : ℝ)*base89 + (36504461/2500000000000000000000 : ℝ)*base91 + (36504461/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1316_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15037/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10761/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5513/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1316_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1316_s5_0 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1033292813/5000000000 : ℝ)*x 0 + (5414537033/10000000000 : ℝ)*x 1 + (2621662823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033292813/5000000000 : ℝ)^1069 ≤ (12578771852263/100000000000000 : ℝ)^813 := by
    have hnat : (1033292813 : ℕ)^1069*100000000000000^813 ≤ 12578771852263^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033292813 5000000000 12578771852263 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414537033/10000000000 : ℝ)^1069 ≤ (11158460727077/25000000000000 : ℝ)^813 := by
    have hnat : (5414537033 : ℕ)^1069*25000000000000^813 ≤ 11158460727077^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414537033 10000000000 11158460727077 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621662823/5000000000 : ℝ)^1069 ≤ (21393692617079/50000000000000 : ℝ)^813 := by
    have hnat : (2621662823 : ℕ)^1069*50000000000000^813 ≤ 21393692617079^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621662823 5000000000 21393692617079 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1033292813/5000000000 : ℝ), (5414537033/10000000000 : ℝ), (2621662823/5000000000 : ℝ)] ![(12578771852263/100000000000000 : ℝ), (11158460727077/25000000000000 : ℝ), (21393692617079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1033292813/5000000000 : ℝ)|^1069 ≤ (12578771852263/100000000000000 : ℝ)^813
        have hw : |(-1033292813/5000000000 : ℝ)|=(1033292813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414537033/10000000000 : ℝ)|^1069 ≤ (11158460727077/25000000000000 : ℝ)^813
        have hw : |(5414537033/10000000000 : ℝ)|=(5414537033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621662823/5000000000 : ℝ)|^1069 ≤ (21393692617079/50000000000000 : ℝ)^813
        have hw : |(2621662823/5000000000 : ℝ)|=(2621662823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s5_1 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1337388839/2500000000 : ℝ)*x 0 + (-2153849551/10000000000 : ℝ)*x 1 + (163853927/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337388839/2500000000 : ℝ)^1069 ≤ (43930839578031/100000000000000 : ℝ)^813 := by
    have hnat : (1337388839 : ℕ)^1069*100000000000000^813 ≤ 43930839578031^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337388839 2500000000 43930839578031 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2153849551/10000000000 : ℝ)^1069 ≤ (6640887491763/50000000000000 : ℝ)^813 := by
    have hnat : (2153849551 : ℕ)^1069*50000000000000^813 ≤ 6640887491763^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153849551 10000000000 6640887491763 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163853927/312500000 : ℝ)^1069 ≤ (42787385427297/100000000000000 : ℝ)^813 := by
    have hnat : (163853927 : ℕ)^1069*100000000000000^813 ≤ 42787385427297^813*312500000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163853927 312500000 42787385427297 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337388839/2500000000 : ℝ), (-2153849551/10000000000 : ℝ), (163853927/312500000 : ℝ)] ![(43930839578031/100000000000000 : ℝ), (6640887491763/50000000000000 : ℝ), (42787385427297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337388839/2500000000 : ℝ)|^1069 ≤ (43930839578031/100000000000000 : ℝ)^813
        have hw : |(1337388839/2500000000 : ℝ)|=(1337388839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2153849551/10000000000 : ℝ)|^1069 ≤ (6640887491763/50000000000000 : ℝ)^813
        have hw : |(-2153849551/10000000000 : ℝ)|=(2153849551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163853927/312500000 : ℝ)|^1069 ≤ (42787385427297/100000000000000 : ℝ)^813
        have hw : |(163853927/312500000 : ℝ)|=(163853927/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s5_2 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349555311/10000000000 : ℝ)*x 0 + (5243325681/10000000000 : ℝ)*x 1 + (-538462397/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349555311/10000000000 : ℝ)^1069 ≤ (21965419546063/50000000000000 : ℝ)^813 := by
    have hnat : (5349555311 : ℕ)^1069*50000000000000^813 ≤ 21965419546063^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349555311 10000000000 21965419546063 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243325681/10000000000 : ℝ)^1069 ≤ (8557477121941/20000000000000 : ℝ)^813 := by
    have hnat : (5243325681 : ℕ)^1069*20000000000000^813 ≤ 8557477121941^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243325681 10000000000 8557477121941 20000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538462397/2500000000 : ℝ)^1069 ≤ (13281775283531/100000000000000 : ℝ)^813 := by
    have hnat : (538462397 : ℕ)^1069*100000000000000^813 ≤ 13281775283531^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538462397 2500000000 13281775283531 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349555311/10000000000 : ℝ), (5243325681/10000000000 : ℝ), (-538462397/2500000000 : ℝ)] ![(21965419546063/50000000000000 : ℝ), (8557477121941/20000000000000 : ℝ), (13281775283531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349555311/10000000000 : ℝ)|^1069 ≤ (21965419546063/50000000000000 : ℝ)^813
        have hw : |(5349555311/10000000000 : ℝ)|=(5349555311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243325681/10000000000 : ℝ)|^1069 ≤ (8557477121941/20000000000000 : ℝ)^813
        have hw : |(5243325681/10000000000 : ℝ)|=(5243325681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-538462397/2500000000 : ℝ)|^1069 ≤ (13281775283531/100000000000000 : ℝ)^813
        have hw : |(-538462397/2500000000 : ℝ)|=(538462397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s5_3 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (135419667/312500000 : ℝ)*x 0 + (1039828497/2500000000 : ℝ)*x 1 + (4514423603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135419667/312500000 : ℝ)^1069 ≤ (33302447186023/100000000000000 : ℝ)^813 := by
    have hnat : (135419667 : ℕ)^1069*100000000000000^813 ≤ 33302447186023^813*312500000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135419667 312500000 33302447186023 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039828497/2500000000 : ℝ)^1069 ≤ (31554264525531/100000000000000 : ℝ)^813 := by
    have hnat : (1039828497 : ℕ)^1069*100000000000000^813 ≤ 31554264525531^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039828497 2500000000 31554264525531 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4514423603/10000000000 : ℝ)^1069 ≤ (17571644139659/50000000000000 : ℝ)^813 := by
    have hnat : (4514423603 : ℕ)^1069*50000000000000^813 ≤ 17571644139659^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514423603 10000000000 17571644139659 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135419667/312500000 : ℝ), (1039828497/2500000000 : ℝ), (4514423603/10000000000 : ℝ)] ![(33302447186023/100000000000000 : ℝ), (31554264525531/100000000000000 : ℝ), (17571644139659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135419667/312500000 : ℝ)|^1069 ≤ (33302447186023/100000000000000 : ℝ)^813
        have hw : |(135419667/312500000 : ℝ)|=(135419667/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039828497/2500000000 : ℝ)|^1069 ≤ (31554264525531/100000000000000 : ℝ)^813
        have hw : |(1039828497/2500000000 : ℝ)|=(1039828497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4514423603/10000000000 : ℝ)|^1069 ≤ (17571644139659/50000000000000 : ℝ)^813
        have hw : |(4514423603/10000000000 : ℝ)|=(4514423603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s5_4 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2066598269/10000000000 : ℝ)*x 0 + (5243940743/10000000000 : ℝ)*x 1 + (5413918769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2066598269/10000000000 : ℝ)^1069 ≤ (6289436519379/50000000000000 : ℝ)^813 := by
    have hnat : (2066598269 : ℕ)^1069*50000000000000^813 ≤ 6289436519379^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066598269 10000000000 6289436519379 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243940743/10000000000 : ℝ)^1069 ≤ (42793985291451/100000000000000 : ℝ)^813 := by
    have hnat : (5243940743 : ℕ)^1069*100000000000000^813 ≤ 42793985291451^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243940743 10000000000 42793985291451 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413918769/10000000000 : ℝ)^1069 ≤ (44627141651473/100000000000000 : ℝ)^813 := by
    have hnat : (5413918769 : ℕ)^1069*100000000000000^813 ≤ 44627141651473^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413918769 10000000000 44627141651473 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2066598269/10000000000 : ℝ), (5243940743/10000000000 : ℝ), (5413918769/10000000000 : ℝ)] ![(6289436519379/50000000000000 : ℝ), (42793985291451/100000000000000 : ℝ), (44627141651473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2066598269/10000000000 : ℝ)|^1069 ≤ (6289436519379/50000000000000 : ℝ)^813
        have hw : |(-2066598269/10000000000 : ℝ)|=(2066598269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243940743/10000000000 : ℝ)|^1069 ≤ (42793985291451/100000000000000 : ℝ)^813
        have hw : |(5243940743/10000000000 : ℝ)|=(5243940743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413918769/10000000000 : ℝ)|^1069 ≤ (44627141651473/100000000000000 : ℝ)^813
        have hw : |(5413918769/10000000000 : ℝ)|=(5413918769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s5_5 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305590331/10000000000 : ℝ)*x 0 + (-1983256429/10000000000 : ℝ)*x 1 + (216556753/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305590331/10000000000 : ℝ)^1069 ≤ (5432090676269/12500000000000 : ℝ)^813 := by
    have hnat : (5305590331 : ℕ)^1069*12500000000000^813 ≤ 5432090676269^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305590331 10000000000 5432090676269 12500000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1983256429/10000000000 : ℝ)^1069 ≤ (11916132322441/100000000000000 : ℝ)^813 := by
    have hnat : (1983256429 : ℕ)^1069*100000000000000^813 ≤ 11916132322441^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983256429 10000000000 11916132322441 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216556753/400000000 : ℝ)^1069 ≤ (11156785564609/25000000000000 : ℝ)^813 := by
    have hnat : (216556753 : ℕ)^1069*25000000000000^813 ≤ 11156785564609^813*400000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216556753 400000000 11156785564609 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305590331/10000000000 : ℝ), (-1983256429/10000000000 : ℝ), (216556753/400000000 : ℝ)] ![(5432090676269/12500000000000 : ℝ), (11916132322441/100000000000000 : ℝ), (11156785564609/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305590331/10000000000 : ℝ)|^1069 ≤ (5432090676269/12500000000000 : ℝ)^813
        have hw : |(5305590331/10000000000 : ℝ)|=(5305590331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1983256429/10000000000 : ℝ)|^1069 ≤ (11916132322441/100000000000000 : ℝ)^813
        have hw : |(-1983256429/10000000000 : ℝ)|=(1983256429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216556753/400000000 : ℝ)|^1069 ≤ (11156785564609/25000000000000 : ℝ)^813
        have hw : |(216556753/400000000 : ℝ)|=(216556753/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s5_6 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305590559/10000000000 : ℝ)*x 0 + (5413918703/10000000000 : ℝ)*x 1 + (-495814071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305590559/10000000000 : ℝ)^1069 ≤ (43456727865683/100000000000000 : ℝ)^813 := by
    have hnat : (5305590559 : ℕ)^1069*100000000000000^813 ≤ 43456727865683^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305590559 10000000000 43456727865683 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413918703/10000000000 : ℝ)^1069 ≤ (44627140936123/100000000000000 : ℝ)^813 := by
    have hnat : (5413918703 : ℕ)^1069*100000000000000^813 ≤ 44627140936123^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413918703 10000000000 44627140936123 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (495814071/2500000000 : ℝ)^1069 ≤ (5958065588449/50000000000000 : ℝ)^813 := by
    have hnat : (495814071 : ℕ)^1069*50000000000000^813 ≤ 5958065588449^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495814071 2500000000 5958065588449 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305590559/10000000000 : ℝ), (5413918703/10000000000 : ℝ), (-495814071/2500000000 : ℝ)] ![(43456727865683/100000000000000 : ℝ), (44627140936123/100000000000000 : ℝ), (5958065588449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305590559/10000000000 : ℝ)|^1069 ≤ (43456727865683/100000000000000 : ℝ)^813
        have hw : |(5305590559/10000000000 : ℝ)|=(5305590559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413918703/10000000000 : ℝ)|^1069 ≤ (44627140936123/100000000000000 : ℝ)^813
        have hw : |(5413918703/10000000000 : ℝ)|=(5413918703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-495814071/2500000000 : ℝ)|^1069 ≤ (5958065588449/50000000000000 : ℝ)^813
        have hw : |(-495814071/2500000000 : ℝ)|=(495814071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_s5_7 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4333455753/10000000000 : ℝ)*x 0 + (902629573/2000000000 : ℝ)*x 1 + (4160596191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4333455753/10000000000 : ℝ)^1069 ≤ (16651357023159/50000000000000 : ℝ)^813 := by
    have hnat : (4333455753 : ℕ)^1069*50000000000000^813 ≤ 16651357023159^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4333455753 10000000000 16651357023159 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (902629573/2000000000 : ℝ)^1069 ≤ (2195639406081/6250000000000 : ℝ)^813 := by
    have hnat : (902629573 : ℕ)^1069*6250000000000^813 ≤ 2195639406081^813*2000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902629573 2000000000 2195639406081 6250000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4160596191/10000000000 : ℝ)^1069 ≤ (15783527716837/50000000000000 : ℝ)^813 := by
    have hnat : (4160596191 : ℕ)^1069*50000000000000^813 ≤ 15783527716837^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4160596191 10000000000 15783527716837 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4333455753/10000000000 : ℝ), (902629573/2000000000 : ℝ), (4160596191/10000000000 : ℝ)] ![(16651357023159/50000000000000 : ℝ), (2195639406081/6250000000000 : ℝ), (15783527716837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4333455753/10000000000 : ℝ)|^1069 ≤ (16651357023159/50000000000000 : ℝ)^813
        have hw : |(4333455753/10000000000 : ℝ)|=(4333455753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(902629573/2000000000 : ℝ)|^1069 ≤ (2195639406081/6250000000000 : ℝ)^813
        have hw : |(902629573/2000000000 : ℝ)|=(902629573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4160596191/10000000000 : ℝ)|^1069 ≤ (15783527716837/50000000000000 : ℝ)^813
        have hw : |(4160596191/10000000000 : ℝ)|=(4160596191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1316_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5513/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11077/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14701/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5513/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5513/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5513/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5513/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5513/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5513/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5513/50000 : ℝ) ^ (4275/1024 : ℝ) ≤ (10052686251011599/100000000000000000000 : ℝ) := by
    have hpowers : (5513/50000 : ℝ)^4275 ≤ (10052686251011599/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5513 : ℕ)^4275*100000000000000000000^1024 ≤ 10052686251011599^1024*50000^4275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5513 50000 10052686251011599 100000000000000000000 4275 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5513/50000 : ℝ)) (X := (10052686251011599/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2951/20000 : ℝ) ^ (4275/1024 : ℝ) ≤ (4240270352230991/12500000000000000000 : ℝ) := by
    have hpowers : (2951/20000 : ℝ)^4275 ≤ (4240270352230991/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2951 : ℕ)^4275*12500000000000000000^1024 ≤ 4240270352230991^1024*20000^4275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2951 20000 4240270352230991 12500000000000000000 4275 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2951/20000 : ℝ)) (X := (4240270352230991/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010052686251011599/50000000000000000000 : ℝ) ≤ (2500120387881493/2500000000000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (50010052686251011599/50000000000000000000 : ℝ)^1024 ≤ (2500120387881493/2500000000000000 : ℝ)^4275 := by
      have hnat : (50010052686251011599 : ℕ)^1024*2500000000000000^4275 ≤ 2500120387881493^4275*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010052686251011599 50000000000000000000 2500120387881493 2500000000000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500120387881493/2500000000000000 : ℝ)) (X := (50010052686251011599/50000000000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043974849068859527/100000000000000000000 : ℝ) ≤ (2000210632598847/2000000000000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (100043974849068859527/100000000000000000000 : ℝ)^1024 ≤ (2000210632598847/2000000000000000 : ℝ)^4275 := by
      have hnat : (100043974849068859527 : ℕ)^1024*2000000000000000^4275 ≤ 2000210632598847^4275*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043974849068859527 100000000000000000000 2000210632598847 2000000000000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000210632598847/2000000000000000 : ℝ)) (X := (100043974849068859527/100000000000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254240270352230991/6250000000000000000 : ℝ) ≤ (5000812387231249/5000000000000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (6254240270352230991/6250000000000000000 : ℝ)^1024 ≤ (5000812387231249/5000000000000000 : ℝ)^4275 := by
      have hnat : (6254240270352230991 : ℕ)^1024*5000000000000000^4275 ≤ 5000812387231249^4275*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254240270352230991 6250000000000000000 5000812387231249 5000000000000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000812387231249/5000000000000000 : ℝ)) (X := (6254240270352230991/6250000000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10052686251011599/100000000000000000000 : ℝ) ≤ ((423627165108434249/423750000000000000 : ℝ)+2*(51964678933/33900000000000 : ℝ)*(5513/50000 : ℝ))^(4275/1024 : ℝ) := by
    rw [show (423627165108434249/423750000000000000 : ℝ)+2*(51964678933/33900000000000 : ℝ)*(5513/50000 : ℝ)=(2500120387881493/2500000000000000 : ℝ) by norm_num, show 1+2*(10052686251011599/100000000000000000000 : ℝ)=(50010052686251011599/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4240270352230991/12500000000000000000 : ℝ)+(10052686251011599/100000000000000000000 : ℝ) ≤ ((423627165108434249/423750000000000000 : ℝ)+(51964678933/33900000000000 : ℝ)*((2951/20000 : ℝ)+(5513/50000 : ℝ)))^(4275/1024 : ℝ) := by
    rw [show (423627165108434249/423750000000000000 : ℝ)+(51964678933/33900000000000 : ℝ)*((2951/20000 : ℝ)+(5513/50000 : ℝ))=(2000210632598847/2000000000000000 : ℝ) by norm_num, show 1+(4240270352230991/12500000000000000000 : ℝ)+(10052686251011599/100000000000000000000 : ℝ)=(100043974849068859527/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4240270352230991/12500000000000000000 : ℝ) ≤ ((423627165108434249/423750000000000000 : ℝ)+2*(51964678933/33900000000000 : ℝ)*(2951/20000 : ℝ))^(4275/1024 : ℝ) := by
    rw [show (423627165108434249/423750000000000000 : ℝ)+2*(51964678933/33900000000000 : ℝ)*(2951/20000 : ℝ)=(5000812387231249/5000000000000000 : ℝ) by norm_num, show 1+2*(4240270352230991/12500000000000000000 : ℝ)=(6254240270352230991/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (423627165108434249/423750000000000000 : ℝ)*(X 1 0+X 2 0)+(51964678933/33900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (5513/50000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (423627165108434249/423750000000000000 : ℝ)) (alpha := (51964678933/33900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (423627165108434249/423750000000000000 : ℝ)*(X 0 1+X 2 1)+(51964678933/33900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (5513/50000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (423627165108434249/423750000000000000 : ℝ)) (alpha := (51964678933/33900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (423627165108434249/423750000000000000 : ℝ)*(X 0 2+X 1 2)+(51964678933/33900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (5513/50000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (423627165108434249/423750000000000000 : ℝ)) (alpha := (51964678933/33900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1033292813/5000000000 : ℝ)*X 0 0+(5414537033/10000000000 : ℝ)*X 0 1+(2621662823/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337388839/2500000000 : ℝ)*X 1 0+(-2153849551/10000000000 : ℝ)*X 1 1+(163853927/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349555311/10000000000 : ℝ)*X 2 0+(5243325681/10000000000 : ℝ)*X 2 1+(-538462397/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((135419667/312500000 : ℝ)*X 0 0+(1039828497/2500000000 : ℝ)*X 0 1+(4514423603/10000000000 : ℝ)*X 0 2+(135419667/312500000 : ℝ)*X 1 0+(1039828497/2500000000 : ℝ)*X 1 1+(4514423603/10000000000 : ℝ)*X 1 2+(135419667/312500000 : ℝ)*X 2 0+(1039828497/2500000000 : ℝ)*X 2 1+(4514423603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2066598269/10000000000 : ℝ)*X 0 0+(5243940743/10000000000 : ℝ)*X 0 1+(5413918769/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305590331/10000000000 : ℝ)*X 1 0+(-1983256429/10000000000 : ℝ)*X 1 1+(216556753/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305590559/10000000000 : ℝ)*X 2 0+(5413918703/10000000000 : ℝ)*X 2 1+(-495814071/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4333455753/10000000000 : ℝ)*X 0 0+(902629573/2000000000 : ℝ)*X 0 1+(4160596191/10000000000 : ℝ)*X 0 2+(4333455753/10000000000 : ℝ)*X 1 0+(902629573/2000000000 : ℝ)*X 1 1+(4160596191/10000000000 : ℝ)*X 1 2+(4333455753/10000000000 : ℝ)*X 2 0+(902629573/2000000000 : ℝ)*X 2 1+(4160596191/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12783153215782569085290501/3531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (342531259/50000000000000 : ℝ)*(base19) + (616807797/100000000000000 : ℝ)*(base23) + (12082069/10000000000000 : ℝ)*(upper3) + (10229821/100000000000000 : ℝ)*(upper4) + (535561/1000000000000 : ℝ)*(upper5) + (2164201408812417/50000000000000 : ℝ)*(major0) + (2164201408812417/50000000000000 : ℝ)*(major1) + (2164201408812417/50000000000000 : ℝ)*(major2) + (29203740842521/500000000000 : ℝ)*(sp0) + (584076011903957/10000000000000 : ℝ)*(sp1) + (5840760187294291/100000000000000 : ℝ)*(sp2) + (2816037839271179/100000000000000 : ℝ)*(sp3) + (197431217/1562500000000 : ℝ)*(sp4) + (6871209461/100000000000000 : ℝ)*(sp7) + (2200034930063/78125000000 : ℝ)*(f.failure) + (730095100512761/12500000000000 : ℝ)*(f.sum) + (974439102531/565000000000000000000000000 : ℝ)*base66 + (55454693678781611/7062500000000000000000000000000 : ℝ)*base67 + (79684139137094111/7062500000000000000000000000000 : ℝ)*base69 + (4102545493531611/7062500000000000000000000000000 : ℝ)*base71 + (2271169986681/565000000000000000000000000 : ℝ)*base74 + (166455063568094111/7062500000000000000000000000000 : ℝ)*base75 + (75648547890219111/7062500000000000000000000000000 : ℝ)*base77 + (29033896808094111/7062500000000000000000000000000 : ℝ)*base79 + (201846470087/282500000000000000000000000 : ℝ)*base81 + (2603/488281250000000000 : ℝ)*base89 + (2603/488281250000000000 : ℝ)*base91 + (2603/488281250000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8966524339859222438189413/882812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1919605471/100000000000000 : ℝ)*(base19) + (2422301763/100000000000000 : ℝ)*(base23) + (24410917/10000000000000 : ℝ)*(upper3) + (87341223/100000000000000 : ℝ)*(lower4) + (224278133/100000000000000 : ℝ)*(upper5) + (1089947250203317/25000000000000 : ℝ)*(major0) + (1089947250203317/25000000000000 : ℝ)*(major1) + (1089947250203317/25000000000000 : ℝ)*(major2) + (7845366257/20000000000000 : ℝ)*(sp1) + (49515751089/100000000000000 : ℝ)*(sp2) + (5883113204501011/100000000000000 : ℝ)*(sp4) + (1176614411612851/20000000000000 : ℝ)*(sp5) + (2941530633224079/50000000000000 : ℝ)*(sp6) + (1418232229283243/50000000000000 : ℝ)*(sp7) + (1418232229283243/50000000000000 : ℝ)*(f.failure) + (5883113204501011/100000000000000 : ℝ)*(f.sum) + (5251936595261/1695000000000000000000000000 : ℝ)*base66 + (138321088040185183/10593750000000000000000000000000 : ℝ)*base67 + (186432744328997683/10593750000000000000000000000000 : ℝ)*base69 + (22950052192060183/10593750000000000000000000000000 : ℝ)*base71 + (666241942711/423750000000000000000000000 : ℝ)*base73 + (96276508395122683/10593750000000000000000000000000 : ℝ)*base75 + (71926090532560183/10593750000000000000000000000000 : ℝ)*base77 + (81475825262372683/10593750000000000000000000000000 : ℝ)*base79 + (4453673765623/847500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (6172089/2500000000000000000000 : ℝ)*base89 + (6172089/2500000000000000000000 : ℝ)*base91 + (6172089/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1316_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5513/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11077/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1316_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1316_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16211/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2419/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11077/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1316_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1316_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1316_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16211/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2419/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11077/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1316_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
