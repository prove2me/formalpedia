-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1339_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:04:03.113218+00:00
-- url     : https://prove2.me/submissions/07dd8b61-20cf-4c10-b298-1187ca5f2b1d

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
theorem support_rectangle_w1339_s6_0 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-511639849/2500000000 : ℝ)*x 0 + (5412879121/10000000000 : ℝ)*x 1 + (131112559/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (511639849/2500000000 : ℝ)^4299 ≤ (2492476796723/20000000000000 : ℝ)^3275 := by
    have hnat : (511639849 : ℕ)^4299*20000000000000^3275 ≤ 2492476796723^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511639849 2500000000 2492476796723 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412879121/10000000000 : ℝ)^4299 ≤ (22338237316573/50000000000000 : ℝ)^3275 := by
    have hnat : (5412879121 : ℕ)^4299*50000000000000^3275 ≤ 22338237316573^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412879121 10000000000 22338237316573 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131112559/250000000 : ℝ)^4299 ≤ (1714445654821/4000000000000 : ℝ)^3275 := by
    have hnat : (131112559 : ℕ)^4299*4000000000000^3275 ≤ 1714445654821^3275*250000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131112559 250000000 1714445654821 4000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-511639849/2500000000 : ℝ), (5412879121/10000000000 : ℝ), (131112559/250000000 : ℝ)] ![(2492476796723/20000000000000 : ℝ), (22338237316573/50000000000000 : ℝ), (1714445654821/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-511639849/2500000000 : ℝ)|^4299 ≤ (2492476796723/20000000000000 : ℝ)^3275
        have hw : |(-511639849/2500000000 : ℝ)|=(511639849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412879121/10000000000 : ℝ)|^4299 ≤ (22338237316573/50000000000000 : ℝ)^3275
        have hw : |(5412879121/10000000000 : ℝ)|=(5412879121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131112559/250000000 : ℝ)|^4299 ≤ (1714445654821/4000000000000 : ℝ)^3275
        have hw : |(131112559/250000000 : ℝ)|=(131112559/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s6_1 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349054843/10000000000 : ℝ)*x 0 + (-533087811/2500000000 : ℝ)*x 1 + (1311125589/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349054843/10000000000 : ℝ)^4299 ≤ (21993126052371/50000000000000 : ℝ)^3275 := by
    have hnat : (5349054843 : ℕ)^4299*50000000000000^3275 ≤ 21993126052371^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349054843 10000000000 21993126052371 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (533087811/2500000000 : ℝ)^4299 ≤ (6576303278693/50000000000000 : ℝ)^3275 := by
    have hnat : (533087811 : ℕ)^4299*50000000000000^3275 ≤ 6576303278693^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533087811 2500000000 6576303278693 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311125589/2500000000 : ℝ)^4299 ≤ (42861141327613/100000000000000 : ℝ)^3275 := by
    have hnat : (1311125589 : ℕ)^4299*100000000000000^3275 ≤ 42861141327613^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311125589 2500000000 42861141327613 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349054843/10000000000 : ℝ), (-533087811/2500000000 : ℝ), (1311125589/2500000000 : ℝ)] ![(21993126052371/50000000000000 : ℝ), (6576303278693/50000000000000 : ℝ), (42861141327613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349054843/10000000000 : ℝ)|^4299 ≤ (21993126052371/50000000000000 : ℝ)^3275
        have hw : |(5349054843/10000000000 : ℝ)|=(5349054843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-533087811/2500000000 : ℝ)|^4299 ≤ (6576303278693/50000000000000 : ℝ)^3275
        have hw : |(-533087811/2500000000 : ℝ)|=(533087811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311125589/2500000000 : ℝ)|^4299 ≤ (42861141327613/100000000000000 : ℝ)^3275
        have hw : |(1311125589/2500000000 : ℝ)|=(1311125589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s6_2 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674527419/5000000000 : ℝ)*x 0 + (163890699/312500000 : ℝ)*x 1 + (-1066175617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674527419/5000000000 : ℝ)^4299 ≤ (4398625205077/10000000000000 : ℝ)^3275 := by
    have hnat : (2674527419 : ℕ)^4299*10000000000000^3275 ≤ 4398625205077^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674527419 5000000000 4398625205077 10000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163890699/312500000 : ℝ)^4299 ≤ (10715285364087/25000000000000 : ℝ)^3275 := by
    have hnat : (163890699 : ℕ)^4299*25000000000000^3275 ≤ 10715285364087^3275*312500000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163890699 312500000 10715285364087 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1066175617/5000000000 : ℝ)^4299 ≤ (6576303238209/50000000000000 : ℝ)^3275 := by
    have hnat : (1066175617 : ℕ)^4299*50000000000000^3275 ≤ 6576303238209^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066175617 5000000000 6576303238209 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674527419/5000000000 : ℝ), (163890699/312500000 : ℝ), (-1066175617/5000000000 : ℝ)] ![(4398625205077/10000000000000 : ℝ), (10715285364087/25000000000000 : ℝ), (6576303238209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674527419/5000000000 : ℝ)|^4299 ≤ (4398625205077/10000000000000 : ℝ)^3275
        have hw : |(2674527419/5000000000 : ℝ)|=(2674527419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163890699/312500000 : ℝ)|^4299 ≤ (10715285364087/25000000000000 : ℝ)^3275
        have hw : |(163890699/312500000 : ℝ)|=(163890699/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1066175617/5000000000 : ℝ)|^4299 ≤ (6576303238209/50000000000000 : ℝ)^3275
        have hw : |(-1066175617/5000000000 : ℝ)|=(1066175617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s6_3 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4327402623/10000000000 : ℝ)*x 0 + (4154617707/10000000000 : ℝ)*x 1 + (2253448463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327402623/10000000000 : ℝ)^4299 ≤ (33303191636131/100000000000000 : ℝ)^3275 := by
    have hnat : (4327402623 : ℕ)^4299*100000000000000^3275 ≤ 33303191636131^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327402623 10000000000 33303191636131 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4154617707/10000000000 : ℝ)^4299 ≤ (7892171527891/25000000000000 : ℝ)^3275 := by
    have hnat : (4154617707 : ℕ)^4299*25000000000000^3275 ≤ 7892171527891^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154617707 10000000000 7892171527891 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253448463/5000000000 : ℝ)^4299 ≤ (35128122233783/100000000000000 : ℝ)^3275 := by
    have hnat : (2253448463 : ℕ)^4299*100000000000000^3275 ≤ 35128122233783^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253448463 5000000000 35128122233783 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327402623/10000000000 : ℝ), (4154617707/10000000000 : ℝ), (2253448463/5000000000 : ℝ)] ![(33303191636131/100000000000000 : ℝ), (7892171527891/25000000000000 : ℝ), (35128122233783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327402623/10000000000 : ℝ)|^4299 ≤ (33303191636131/100000000000000 : ℝ)^3275
        have hw : |(4327402623/10000000000 : ℝ)|=(4327402623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4154617707/10000000000 : ℝ)|^4299 ≤ (7892171527891/25000000000000 : ℝ)^3275
        have hw : |(4154617707/10000000000 : ℝ)|=(4154617707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253448463/5000000000 : ℝ)|^4299 ≤ (35128122233783/100000000000000 : ℝ)^3275
        have hw : |(2253448463/5000000000 : ℝ)|=(2253448463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s6_4 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-409314319/2000000000 : ℝ)*x 0 + (5245105207/10000000000 : ℝ)*x 1 + (5412273179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (409314319/2000000000 : ℝ)^4299 ≤ (24924962991/200000000000 : ℝ)^3275 := by
    have hnat : (409314319 : ℕ)^4299*200000000000^3275 ≤ 24924962991^3275*2000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409314319 2000000000 24924962991 200000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245105207/10000000000 : ℝ)^4299 ≤ (42867608782043/100000000000000 : ℝ)^3275 := by
    have hnat : (5245105207 : ℕ)^4299*100000000000000^3275 ≤ 42867608782043^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245105207 10000000000 42867608782043 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412273179/10000000000 : ℝ)^4299 ≤ (22334954851091/50000000000000 : ℝ)^3275 := by
    have hnat : (5412273179 : ℕ)^4299*50000000000000^3275 ≤ 22334954851091^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412273179 10000000000 22334954851091 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-409314319/2000000000 : ℝ), (5245105207/10000000000 : ℝ), (5412273179/10000000000 : ℝ)] ![(24924962991/200000000000 : ℝ), (42867608782043/100000000000000 : ℝ), (22334954851091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-409314319/2000000000 : ℝ)|^4299 ≤ (24924962991/200000000000 : ℝ)^3275
        have hw : |(-409314319/2000000000 : ℝ)|=(409314319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245105207/10000000000 : ℝ)|^4299 ≤ (42867608782043/100000000000000 : ℝ)^3275
        have hw : |(5245105207/10000000000 : ℝ)|=(5245105207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412273179/10000000000 : ℝ)|^4299 ≤ (22334954851091/50000000000000 : ℝ)^3275
        have hw : |(5412273179/10000000000 : ℝ)|=(5412273179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s6_5 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165803119/312500000 : ℝ)*x 0 + (-982290201/5000000000 : ℝ)*x 1 + (5412273179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165803119/312500000 : ℝ)^4299 ≤ (43518857271627/100000000000000 : ℝ)^3275 := by
    have hnat : (165803119 : ℕ)^4299*100000000000000^3275 ≤ 43518857271627^3275*312500000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165803119 312500000 43518857271627 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (982290201/5000000000 : ℝ)^4299 ≤ (11811233007681/100000000000000 : ℝ)^3275 := by
    have hnat : (982290201 : ℕ)^4299*100000000000000^3275 ≤ 11811233007681^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982290201 5000000000 11811233007681 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412273179/10000000000 : ℝ)^4299 ≤ (22334954851091/50000000000000 : ℝ)^3275 := by
    have hnat : (5412273179 : ℕ)^4299*50000000000000^3275 ≤ 22334954851091^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412273179 10000000000 22334954851091 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165803119/312500000 : ℝ), (-982290201/5000000000 : ℝ), (5412273179/10000000000 : ℝ)] ![(43518857271627/100000000000000 : ℝ), (11811233007681/100000000000000 : ℝ), (22334954851091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165803119/312500000 : ℝ)|^4299 ≤ (43518857271627/100000000000000 : ℝ)^3275
        have hw : |(165803119/312500000 : ℝ)|=(165803119/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-982290201/5000000000 : ℝ)|^4299 ≤ (11811233007681/100000000000000 : ℝ)^3275
        have hw : |(-982290201/5000000000 : ℝ)|=(982290201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412273179/10000000000 : ℝ)|^4299 ≤ (22334954851091/50000000000000 : ℝ)^3275
        have hw : |(5412273179/10000000000 : ℝ)|=(5412273179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s6_6 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165803119/312500000 : ℝ)*x 0 + (5412273179/10000000000 : ℝ)*x 1 + (-982290201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165803119/312500000 : ℝ)^4299 ≤ (43518857271627/100000000000000 : ℝ)^3275 := by
    have hnat : (165803119 : ℕ)^4299*100000000000000^3275 ≤ 43518857271627^3275*312500000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165803119 312500000 43518857271627 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412273179/10000000000 : ℝ)^4299 ≤ (22334954851091/50000000000000 : ℝ)^3275 := by
    have hnat : (5412273179 : ℕ)^4299*50000000000000^3275 ≤ 22334954851091^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412273179 10000000000 22334954851091 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (982290201/5000000000 : ℝ)^4299 ≤ (11811233007681/100000000000000 : ℝ)^3275 := by
    have hnat : (982290201 : ℕ)^4299*100000000000000^3275 ≤ 11811233007681^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982290201 5000000000 11811233007681 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165803119/312500000 : ℝ), (5412273179/10000000000 : ℝ), (-982290201/5000000000 : ℝ)] ![(43518857271627/100000000000000 : ℝ), (22334954851091/50000000000000 : ℝ), (11811233007681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165803119/312500000 : ℝ)|^4299 ≤ (43518857271627/100000000000000 : ℝ)^3275
        have hw : |(165803119/312500000 : ℝ)|=(165803119/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412273179/10000000000 : ℝ)|^4299 ≤ (22334954851091/50000000000000 : ℝ)^3275
        have hw : |(5412273179/10000000000 : ℝ)|=(5412273179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-982290201/5000000000 : ℝ)|^4299 ≤ (11811233007681/100000000000000 : ℝ)^3275
        have hw : |(-982290201/5000000000 : ℝ)|=(982290201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s6_7 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540928517/1250000000 : ℝ)*x 0 + (4505635713/10000000000 : ℝ)*x 1 + (415588547/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540928517/1250000000 : ℝ)^4299 ≤ (8325862343261/25000000000000 : ℝ)^3275 := by
    have hnat : (540928517 : ℕ)^4299*25000000000000^3275 ≤ 8325862343261^3275*1250000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540928517 1250000000 8325862343261 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4505635713/10000000000 : ℝ)^4299 ≤ (35115218871609/100000000000000 : ℝ)^3275 := by
    have hnat : (4505635713 : ℕ)^4299*100000000000000^3275 ≤ 35115218871609^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505635713 10000000000 35115218871609 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415588547/1000000000 : ℝ)^4299 ≤ (31581331738599/100000000000000 : ℝ)^3275 := by
    have hnat : (415588547 : ℕ)^4299*100000000000000^3275 ≤ 31581331738599^3275*1000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415588547 1000000000 31581331738599 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540928517/1250000000 : ℝ), (4505635713/10000000000 : ℝ), (415588547/1000000000 : ℝ)] ![(8325862343261/25000000000000 : ℝ), (35115218871609/100000000000000 : ℝ), (31581331738599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540928517/1250000000 : ℝ)|^4299 ≤ (8325862343261/25000000000000 : ℝ)^3275
        have hw : |(540928517/1250000000 : ℝ)|=(540928517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4505635713/10000000000 : ℝ)|^4299 ≤ (35115218871609/100000000000000 : ℝ)^3275
        have hw : |(4505635713/10000000000 : ℝ)|=(4505635713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(415588547/1000000000 : ℝ)|^4299 ≤ (31581331738599/100000000000000 : ℝ)^3275
        have hw : |(415588547/1000000000 : ℝ)|=(415588547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1339_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5567/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11141/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7353/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7357/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5567/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7357/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5567/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7357/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5567/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7357/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5567/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7357/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5567/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7357/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5567/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5567/50000 : ℝ) ^ (2149/512 : ℝ) ≤ (4983241431668203/50000000000000000000 : ℝ) := by
    have hpowers : (5567/50000 : ℝ)^2149 ≤ (4983241431668203/50000000000000000000 : ℝ)^512 := by
      have hnat : (5567 : ℕ)^2149*50000000000000000000^512 ≤ 4983241431668203^512*50000^2149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5567 50000 4983241431668203 50000000000000000000 2149 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5567/50000 : ℝ)) (X := (4983241431668203/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7357/50000 : ℝ) ^ (2149/512 : ℝ) ≤ (4014716717187469/12500000000000000000 : ℝ) := by
    have hpowers : (7357/50000 : ℝ)^2149 ≤ (4014716717187469/12500000000000000000 : ℝ)^512 := by
      have hnat : (7357 : ℕ)^2149*12500000000000000000^512 ≤ 4014716717187469^512*50000^2149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7357 50000 4014716717187469 12500000000000000000 2149 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7357/50000 : ℝ)) (X := (4014716717187469/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004983241431668203/25000000000000000000 : ℝ) ≤ (10000474867553803/10000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (25004983241431668203/25000000000000000000 : ℝ)^512 ≤ (10000474867553803/10000000000000000 : ℝ)^2149 := by
      have hnat : (25004983241431668203 : ℕ)^512*10000000000000000^2149 ≤ 10000474867553803^2149*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004983241431668203 25000000000000000000 10000474867553803 10000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000474867553803/10000000000000000 : ℝ)) (X := (25004983241431668203/25000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021042108300418079/50000000000000000000 : ℝ) ≤ (10001002497254739/10000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (50021042108300418079/50000000000000000000 : ℝ)^512 ≤ (10001002497254739/10000000000000000 : ℝ)^2149 := by
      have hnat : (50021042108300418079 : ℕ)^512*10000000000000000^2149 ≤ 10001002497254739^2149*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021042108300418079 50000000000000000000 10001002497254739 10000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001002497254739/10000000000000000 : ℝ)) (X := (50021042108300418079/50000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254014716717187469/6250000000000000000 : ℝ) ≤ (400061205078227/400000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (6254014716717187469/6250000000000000000 : ℝ)^512 ≤ (400061205078227/400000000000000 : ℝ)^2149 := by
      have hnat : (6254014716717187469 : ℕ)^512*400000000000000^2149 ≤ 400061205078227^2149*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254014716717187469 6250000000000000000 400061205078227 400000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400061205078227/400000000000000 : ℝ)) (X := (6254014716717187469/6250000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4983241431668203/50000000000000000000 : ℝ) ≤ ((8947487691915542973/8950000000000000000 : ℝ)+2*(65953712617/44750000000000 : ℝ)*(5567/50000 : ℝ))^(2149/512 : ℝ) := by
    rw [show (8947487691915542973/8950000000000000000 : ℝ)+2*(65953712617/44750000000000 : ℝ)*(5567/50000 : ℝ)=(10000474867553803/10000000000000000 : ℝ) by norm_num, show 1+2*(4983241431668203/50000000000000000000 : ℝ)=(25004983241431668203/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4014716717187469/12500000000000000000 : ℝ)+(4983241431668203/50000000000000000000 : ℝ) ≤ ((8947487691915542973/8950000000000000000 : ℝ)+(65953712617/44750000000000 : ℝ)*((7357/50000 : ℝ)+(5567/50000 : ℝ)))^(2149/512 : ℝ) := by
    rw [show (8947487691915542973/8950000000000000000 : ℝ)+(65953712617/44750000000000 : ℝ)*((7357/50000 : ℝ)+(5567/50000 : ℝ))=(10001002497254739/10000000000000000 : ℝ) by norm_num, show 1+(4014716717187469/12500000000000000000 : ℝ)+(4983241431668203/50000000000000000000 : ℝ)=(50021042108300418079/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4014716717187469/12500000000000000000 : ℝ) ≤ ((8947487691915542973/8950000000000000000 : ℝ)+2*(65953712617/44750000000000 : ℝ)*(7357/50000 : ℝ))^(2149/512 : ℝ) := by
    rw [show (8947487691915542973/8950000000000000000 : ℝ)+2*(65953712617/44750000000000 : ℝ)*(7357/50000 : ℝ)=(400061205078227/400000000000000 : ℝ) by norm_num, show 1+2*(4014716717187469/12500000000000000000 : ℝ)=(6254014716717187469/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8947487691915542973/8950000000000000000 : ℝ)*(X 1 0+X 2 0)+(65953712617/44750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (5567/50000 : ℝ)) (hi := (7357/50000 : ℝ)) (c := (8947487691915542973/8950000000000000000 : ℝ)) (alpha := (65953712617/44750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8947487691915542973/8950000000000000000 : ℝ)*(X 0 1+X 2 1)+(65953712617/44750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (5567/50000 : ℝ)) (hi := (7357/50000 : ℝ)) (c := (8947487691915542973/8950000000000000000 : ℝ)) (alpha := (65953712617/44750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8947487691915542973/8950000000000000000 : ℝ)*(X 0 2+X 1 2)+(65953712617/44750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (5567/50000 : ℝ)) (hi := (7357/50000 : ℝ)) (c := (8947487691915542973/8950000000000000000 : ℝ)) (alpha := (65953712617/44750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-511639849/2500000000 : ℝ)*X 0 0+(5412879121/10000000000 : ℝ)*X 0 1+(131112559/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349054843/10000000000 : ℝ)*X 1 0+(-533087811/2500000000 : ℝ)*X 1 1+(1311125589/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674527419/5000000000 : ℝ)*X 2 0+(163890699/312500000 : ℝ)*X 2 1+(-1066175617/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4327402623/10000000000 : ℝ)*X 0 0+(4154617707/10000000000 : ℝ)*X 0 1+(2253448463/5000000000 : ℝ)*X 0 2+(4327402623/10000000000 : ℝ)*X 1 0+(4154617707/10000000000 : ℝ)*X 1 1+(2253448463/5000000000 : ℝ)*X 1 2+(4327402623/10000000000 : ℝ)*X 2 0+(4154617707/10000000000 : ℝ)*X 2 1+(2253448463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-409314319/2000000000 : ℝ)*X 0 0+(5245105207/10000000000 : ℝ)*X 0 1+(5412273179/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165803119/312500000 : ℝ)*X 1 0+(-982290201/5000000000 : ℝ)*X 1 1+(5412273179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165803119/312500000 : ℝ)*X 2 0+(5412273179/10000000000 : ℝ)*X 2 1+(-982290201/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((540928517/1250000000 : ℝ)*X 0 0+(4505635713/10000000000 : ℝ)*X 0 1+(415588547/1000000000 : ℝ)*X 0 2+(540928517/1250000000 : ℝ)*X 1 0+(4505635713/10000000000 : ℝ)*X 1 1+(415588547/1000000000 : ℝ)*X 1 2+(540928517/1250000000 : ℝ)*X 2 0+(4505635713/10000000000 : ℝ)*X 2 1+(415588547/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1147782132981766209363388659/111875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1944711563/100000000000000 : ℝ)*(base19) + (450701249/25000000000000 : ℝ)*(base23) + (72937031/100000000000000 : ℝ)*(lower2) + (33337507/12500000000000 : ℝ)*(upper3) + (44233997/25000000000000 : ℝ)*(upper5) + (2194459234771539/50000000000000 : ℝ)*(major0) + (2194459234771539/50000000000000 : ℝ)*(major1) + (2194459234771539/50000000000000 : ℝ)*(major2) + (2969551207324539/50000000000000 : ℝ)*(sp0) + (5939139554887839/100000000000000 : ℝ)*(sp1) + (1187827939358881/20000000000000 : ℝ)*(sp2) + (2838675231720179/100000000000000 : ℝ)*(sp3) + (9771237581/25000000000000 : ℝ)*(sp4) + (9932891533/50000000000000 : ℝ)*(sp7) + (567739019500649/20000000000000 : ℝ)*(f.failure) + (2969570749799701/50000000000000 : ℝ)*(f.sum) + (7590100788377/4475000000000000000000000000 : ℝ)*base65 + (2481262155446945447/447500000000000000000000000000000 : ℝ)*base67 + (698322929929445447/447500000000000000000000000000000 : ℝ)*base69 + (2805500225729445447/447500000000000000000000000000000 : ℝ)*base71 + (18010437800127/4475000000000000000000000000 : ℝ)*base73 + (946626482150554553/447500000000000000000000000000000 : ℝ)*base76 + (4760257592661945447/447500000000000000000000000000000 : ℝ)*base77 + (2286683098981945447/447500000000000000000000000000000 : ℝ)*base79 + (2442942926581/559375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5581939/1000000000000000000000 : ℝ)*base89 + (5581939/1000000000000000000000 : ℝ)*base91 + (5581939/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2036839013986301014867455339/223750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (158775233/10000000000000 : ℝ)*(base19) + (862507561/50000000000000 : ℝ)*(base23) + (92672387/50000000000000 : ℝ)*(upper3) + (62250923/100000000000000 : ℝ)*(lower4) + (186694711/100000000000000 : ℝ)*(upper5) + (4420594450490819/100000000000000 : ℝ)*(major0) + (4420594450490819/100000000000000 : ℝ)*(major1) + (4420594450490819/100000000000000 : ℝ)*(major2) + (323699087/1000000000000 : ℝ)*(sp1) + (8702360813/25000000000000 : ℝ)*(sp2) + (5982005889605963/100000000000000 : ℝ)*(sp4) + (5981971931944933/100000000000000 : ℝ)*(sp5) + (5981969355147589/100000000000000 : ℝ)*(sp6) + (1429591353967981/50000000000000 : ℝ)*(sp7) + (1429591353967981/50000000000000 : ℝ)*(f.failure) + (5982005889605963/100000000000000 : ℝ)*(f.sum) + (3377215238679/4475000000000000000000000000 : ℝ)*base66 + (2624429766336064887/895000000000000000000000000000000 : ℝ)*base67 + (7688090714686064887/895000000000000000000000000000000 : ℝ)*base69 + (5951794560018935113/895000000000000000000000000000000 : ℝ)*base72 + (2000628936323/2237500000000000000000000000 : ℝ)*base73 + (19849008081836064887/895000000000000000000000000000000 : ℝ)*base75 + (600939774001064887/895000000000000000000000000000000 : ℝ)*base77 + (10055358057066064887/895000000000000000000000000000000 : ℝ)*base79 + (935402267063/559375000000000000000000000 : ℝ)*base82 + (16551009/2500000000000000000000 : ℝ)*base90 + (16551009/2500000000000000000000 : ℝ)*base92 + (16551009/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1339_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5567/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11141/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1339_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1339_s7_0 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-511642041/2500000000 : ℝ)*x 0 + (2706407691/5000000000 : ℝ)*x 1 + (2622280099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (511642041/2500000000 : ℝ)^4299 ≤ (6231227035007/50000000000000 : ℝ)^3275 := by
    have hnat : (511642041 : ℕ)^4299*50000000000000^3275 ≤ 6231227035007^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511642041 2500000000 6231227035007 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706407691/5000000000 : ℝ)^4299 ≤ (22337892028833/50000000000000 : ℝ)^3275 := by
    have hnat : (2706407691 : ℕ)^4299*50000000000000^3275 ≤ 22337892028833^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706407691 5000000000 22337892028833 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622280099/5000000000 : ℝ)^4299 ≤ (42861761853119/100000000000000 : ℝ)^3275 := by
    have hnat : (2622280099 : ℕ)^4299*100000000000000^3275 ≤ 42861761853119^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622280099 5000000000 42861761853119 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-511642041/2500000000 : ℝ), (2706407691/5000000000 : ℝ), (2622280099/5000000000 : ℝ)] ![(6231227035007/50000000000000 : ℝ), (22337892028833/50000000000000 : ℝ), (42861761853119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-511642041/2500000000 : ℝ)|^4299 ≤ (6231227035007/50000000000000 : ℝ)^3275
        have hw : |(-511642041/2500000000 : ℝ)|=(511642041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706407691/5000000000 : ℝ)|^4299 ≤ (22337892028833/50000000000000 : ℝ)^3275
        have hw : |(2706407691/5000000000 : ℝ)|=(2706407691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622280099/5000000000 : ℝ)|^4299 ≤ (42861761853119/100000000000000 : ℝ)^3275
        have hw : |(2622280099/5000000000 : ℝ)|=(2622280099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s7_1 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349038607/10000000000 : ℝ)*x 0 + (-2132296371/10000000000 : ℝ)*x 1 + (2622280053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349038607/10000000000 : ℝ)^4299 ≤ (43986076847939/100000000000000 : ℝ)^3275 := by
    have hnat : (5349038607 : ℕ)^4299*100000000000000^3275 ≤ 43986076847939^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349038607 10000000000 43986076847939 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2132296371/10000000000 : ℝ)^4299 ≤ (13152162267749/100000000000000 : ℝ)^3275 := by
    have hnat : (2132296371 : ℕ)^4299*100000000000000^3275 ≤ 13152162267749^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132296371 10000000000 13152162267749 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622280053/5000000000 : ℝ)^4299 ≤ (42861760866147/100000000000000 : ℝ)^3275 := by
    have hnat : (2622280053 : ℕ)^4299*100000000000000^3275 ≤ 42861760866147^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622280053 5000000000 42861760866147 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349038607/10000000000 : ℝ), (-2132296371/10000000000 : ℝ), (2622280053/5000000000 : ℝ)] ![(43986076847939/100000000000000 : ℝ), (13152162267749/100000000000000 : ℝ), (42861760866147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349038607/10000000000 : ℝ)|^4299 ≤ (43986076847939/100000000000000 : ℝ)^3275
        have hw : |(5349038607/10000000000 : ℝ)|=(5349038607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2132296371/10000000000 : ℝ)|^4299 ≤ (13152162267749/100000000000000 : ℝ)^3275
        have hw : |(-2132296371/10000000000 : ℝ)|=(2132296371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622280053/5000000000 : ℝ)|^4299 ≤ (42861760866147/100000000000000 : ℝ)^3275
        have hw : |(2622280053/5000000000 : ℝ)|=(2622280053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s7_2 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349037981/10000000000 : ℝ)*x 0 + (5244560371/10000000000 : ℝ)*x 1 + (-426459371/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349037981/10000000000 : ℝ)^4299 ≤ (43986070090689/100000000000000 : ℝ)^3275 := by
    have hnat : (5349037981 : ℕ)^4299*100000000000000^3275 ≤ 43986070090689^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349037981 10000000000 43986070090689 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244560371/10000000000 : ℝ)^4299 ≤ (334857528977/781250000000 : ℝ)^3275 := by
    have hnat : (5244560371 : ℕ)^4299*781250000000^3275 ≤ 334857528977^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244560371 10000000000 334857528977 781250000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (426459371/2000000000 : ℝ)^4299 ≤ (13152166186531/100000000000000 : ℝ)^3275 := by
    have hnat : (426459371 : ℕ)^4299*100000000000000^3275 ≤ 13152166186531^3275*2000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426459371 2000000000 13152166186531 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349037981/10000000000 : ℝ), (5244560371/10000000000 : ℝ), (-426459371/2000000000 : ℝ)] ![(43986070090689/100000000000000 : ℝ), (334857528977/781250000000 : ℝ), (13152166186531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349037981/10000000000 : ℝ)|^4299 ≤ (43986070090689/100000000000000 : ℝ)^3275
        have hw : |(5349037981/10000000000 : ℝ)|=(5349037981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244560371/10000000000 : ℝ)|^4299 ≤ (334857528977/781250000000 : ℝ)^3275
        have hw : |(5244560371/10000000000 : ℝ)|=(5244560371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-426459371/2000000000 : ℝ)|^4299 ≤ (13152166186531/100000000000000 : ℝ)^3275
        have hw : |(-426459371/2000000000 : ℝ)|=(426459371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s7_3 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (865481351/2000000000 : ℝ)*x 0 + (2077372043/5000000000 : ℝ)*x 1 + (2253384821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865481351/2000000000 : ℝ)^4299 ≤ (6660646675661/20000000000000 : ℝ)^3275 := by
    have hnat : (865481351 : ℕ)^4299*20000000000000^3275 ≤ 6660646675661^3275*2000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865481351 2000000000 6660646675661 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077372043/5000000000 : ℝ)^4299 ≤ (31569946657161/100000000000000 : ℝ)^3275 := by
    have hnat : (2077372043 : ℕ)^4299*100000000000000^3275 ≤ 31569946657161^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077372043 5000000000 31569946657161 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253384821/5000000000 : ℝ)^4299 ≤ (17563409975427/50000000000000 : ℝ)^3275 := by
    have hnat : (2253384821 : ℕ)^4299*50000000000000^3275 ≤ 17563409975427^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253384821 5000000000 17563409975427 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865481351/2000000000 : ℝ), (2077372043/5000000000 : ℝ), (2253384821/5000000000 : ℝ)] ![(6660646675661/20000000000000 : ℝ), (31569946657161/100000000000000 : ℝ), (17563409975427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865481351/2000000000 : ℝ)|^4299 ≤ (6660646675661/20000000000000 : ℝ)^3275
        have hw : |(865481351/2000000000 : ℝ)|=(865481351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2077372043/5000000000 : ℝ)|^4299 ≤ (31569946657161/100000000000000 : ℝ)^3275
        have hw : |(2077372043/5000000000 : ℝ)|=(2077372043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253384821/5000000000 : ℝ)|^4299 ≤ (17563409975427/50000000000000 : ℝ)^3275
        have hw : |(2253384821/5000000000 : ℝ)|=(2253384821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s7_4 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1023290143/5000000000 : ℝ)*x 0 + (5245162119/10000000000 : ℝ)*x 1 + (5412210411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1023290143/5000000000 : ℝ)^4299 ≤ (6231275483267/50000000000000 : ℝ)^3275 := by
    have hnat : (1023290143 : ℕ)^4299*50000000000000^3275 ≤ 6231275483267^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023290143 5000000000 6231275483267 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245162119/10000000000 : ℝ)^4299 ≤ (42868219352491/100000000000000 : ℝ)^3275 := by
    have hnat : (5245162119 : ℕ)^4299*100000000000000^3275 ≤ 42868219352491^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245162119 10000000000 42868219352491 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412210411/10000000000 : ℝ)^4299 ≤ (22334614835357/50000000000000 : ℝ)^3275 := by
    have hnat : (5412210411 : ℕ)^4299*50000000000000^3275 ≤ 22334614835357^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412210411 10000000000 22334614835357 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1023290143/5000000000 : ℝ), (5245162119/10000000000 : ℝ), (5412210411/10000000000 : ℝ)] ![(6231275483267/50000000000000 : ℝ), (42868219352491/100000000000000 : ℝ), (22334614835357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1023290143/5000000000 : ℝ)|^4299 ≤ (6231275483267/50000000000000 : ℝ)^3275
        have hw : |(-1023290143/5000000000 : ℝ)|=(1023290143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245162119/10000000000 : ℝ)|^4299 ≤ (42868219352491/100000000000000 : ℝ)^3275
        have hw : |(5245162119/10000000000 : ℝ)|=(5245162119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412210411/10000000000 : ℝ)|^4299 ≤ (22334614835357/50000000000000 : ℝ)^3275
        have hw : |(5412210411/10000000000 : ℝ)|=(5412210411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s7_5 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305714411/10000000000 : ℝ)*x 0 + (-245580831/1250000000 : ℝ)*x 1 + (5412210411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305714411/10000000000 : ℝ)^4299 ≤ (21759507250417/50000000000000 : ℝ)^3275 := by
    have hnat : (5305714411 : ℕ)^4299*50000000000000^3275 ≤ 21759507250417^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305714411 10000000000 21759507250417 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245580831/1250000000 : ℝ)^4299 ≤ (11811755817241/100000000000000 : ℝ)^3275 := by
    have hnat : (245580831 : ℕ)^4299*100000000000000^3275 ≤ 11811755817241^3275*1250000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245580831 1250000000 11811755817241 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412210411/10000000000 : ℝ)^4299 ≤ (22334614835357/50000000000000 : ℝ)^3275 := by
    have hnat : (5412210411 : ℕ)^4299*50000000000000^3275 ≤ 22334614835357^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412210411 10000000000 22334614835357 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305714411/10000000000 : ℝ), (-245580831/1250000000 : ℝ), (5412210411/10000000000 : ℝ)] ![(21759507250417/50000000000000 : ℝ), (11811755817241/100000000000000 : ℝ), (22334614835357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305714411/10000000000 : ℝ)|^4299 ≤ (21759507250417/50000000000000 : ℝ)^3275
        have hw : |(5305714411/10000000000 : ℝ)|=(5305714411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-245580831/1250000000 : ℝ)|^4299 ≤ (11811755817241/100000000000000 : ℝ)^3275
        have hw : |(-245580831/1250000000 : ℝ)|=(245580831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412210411/10000000000 : ℝ)|^4299 ≤ (22334614835357/50000000000000 : ℝ)^3275
        have hw : |(5412210411/10000000000 : ℝ)|=(5412210411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s7_6 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305714413/10000000000 : ℝ)*x 0 + (5412210409/10000000000 : ℝ)*x 1 + (-245580831/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305714413/10000000000 : ℝ)^4299 ≤ (43519014522367/100000000000000 : ℝ)^3275 := by
    have hnat : (5305714413 : ℕ)^4299*100000000000000^3275 ≤ 43519014522367^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305714413 10000000000 43519014522367 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412210409/10000000000 : ℝ)^4299 ≤ (22334614824523/50000000000000 : ℝ)^3275 := by
    have hnat : (5412210409 : ℕ)^4299*50000000000000^3275 ≤ 22334614824523^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412210409 10000000000 22334614824523 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245580831/1250000000 : ℝ)^4299 ≤ (11811755817241/100000000000000 : ℝ)^3275 := by
    have hnat : (245580831 : ℕ)^4299*100000000000000^3275 ≤ 11811755817241^3275*1250000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245580831 1250000000 11811755817241 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305714413/10000000000 : ℝ), (5412210409/10000000000 : ℝ), (-245580831/1250000000 : ℝ)] ![(43519014522367/100000000000000 : ℝ), (22334614824523/50000000000000 : ℝ), (11811755817241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305714413/10000000000 : ℝ)|^4299 ≤ (43519014522367/100000000000000 : ℝ)^3275
        have hw : |(5305714413/10000000000 : ℝ)|=(5305714413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412210409/10000000000 : ℝ)|^4299 ≤ (22334614824523/50000000000000 : ℝ)^3275
        have hw : |(5412210409/10000000000 : ℝ)|=(5412210409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-245580831/1250000000 : ℝ)|^4299 ≤ (11811755817241/100000000000000 : ℝ)^3275
        have hw : |(-245580831/1250000000 : ℝ)|=(245580831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_s7_7 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2163716191/5000000000 : ℝ)*x 0 + (1126377493/2500000000 : ℝ)*x 1 + (4156010127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163716191/5000000000 : ℝ)^4299 ≤ (6660698453389/20000000000000 : ℝ)^3275 := by
    have hnat : (2163716191 : ℕ)^4299*20000000000000^3275 ≤ 6660698453389^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163716191 5000000000 6660698453389 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126377493/2500000000 : ℝ)^4299 ≤ (35113932488111/100000000000000 : ℝ)^3275 := by
    have hnat : (1126377493 : ℕ)^4299*100000000000000^3275 ≤ 35113932488111^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126377493 2500000000 35113932488111 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4156010127/10000000000 : ℝ)^4299 ≤ (31582575226939/100000000000000 : ℝ)^3275 := by
    have hnat : (4156010127 : ℕ)^4299*100000000000000^3275 ≤ 31582575226939^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4156010127 10000000000 31582575226939 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163716191/5000000000 : ℝ), (1126377493/2500000000 : ℝ), (4156010127/10000000000 : ℝ)] ![(6660698453389/20000000000000 : ℝ), (35113932488111/100000000000000 : ℝ), (31582575226939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163716191/5000000000 : ℝ)|^4299 ≤ (6660698453389/20000000000000 : ℝ)^3275
        have hw : |(2163716191/5000000000 : ℝ)|=(2163716191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126377493/2500000000 : ℝ)|^4299 ≤ (35113932488111/100000000000000 : ℝ)^3275
        have hw : |(1126377493/2500000000 : ℝ)|=(1126377493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4156010127/10000000000 : ℝ)|^4299 ≤ (31582575226939/100000000000000 : ℝ)^3275
        have hw : |(4156010127/10000000000 : ℝ)|=(4156010127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1339_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11141/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11143/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (919/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7353/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11141/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7353/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11141/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7353/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11141/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7353/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11141/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7353/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11141/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7353/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11141/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11141/100000 : ℝ) ^ (2149/512 : ℝ) ≤ (1998561855134481/20000000000000000000 : ℝ) := by
    have hpowers : (11141/100000 : ℝ)^2149 ≤ (1998561855134481/20000000000000000000 : ℝ)^512 := by
      have hnat : (11141 : ℕ)^2149*20000000000000000000^512 ≤ 1998561855134481^512*100000^2149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11141 100000 1998561855134481 20000000000000000000 2149 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11141/100000 : ℝ)) (X := (1998561855134481/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7353/50000 : ℝ) ^ (2149/512 : ℝ) ≤ (32044503053446333/100000000000000000000 : ℝ) := by
    have hpowers : (7353/50000 : ℝ)^2149 ≤ (32044503053446333/100000000000000000000 : ℝ)^512 := by
      have hnat : (7353 : ℕ)^2149*100000000000000000000^512 ≤ 32044503053446333^512*50000^2149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7353 50000 32044503053446333 100000000000000000000 2149 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7353/50000 : ℝ)) (X := (32044503053446333/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001998561855134481/10000000000000000000 : ℝ) ≤ (2000095224363699/2000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (10001998561855134481/10000000000000000000 : ℝ)^512 ≤ (2000095224363699/2000000000000000 : ℝ)^2149 := by
      have hnat : (10001998561855134481 : ℕ)^512*2000000000000000^2149 ≤ 2000095224363699^2149*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001998561855134481 10000000000000000000 2000095224363699 2000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000095224363699/2000000000000000 : ℝ)) (X := (10001998561855134481/10000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021018656164559369/50000000000000000000 : ℝ) ≤ (10001001380116739/10000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (50021018656164559369/50000000000000000000 : ℝ)^512 ≤ (10001001380116739/10000000000000000 : ℝ)^2149 := by
      have hnat : (50021018656164559369 : ℕ)^512*10000000000000000^2149 ≤ 10001001380116739^2149*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021018656164559369 50000000000000000000 10001001380116739 10000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001001380116739/10000000000000000 : ℝ)) (X := (50021018656164559369/50000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032044503053446333/50000000000000000000 : ℝ) ≤ (10001526638414983/10000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (50032044503053446333/50000000000000000000 : ℝ)^512 ≤ (10001526638414983/10000000000000000 : ℝ)^2149 := by
      have hnat : (50032044503053446333 : ℕ)^512*10000000000000000^2149 ≤ 10001526638414983^2149*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032044503053446333 50000000000000000000 10001526638414983 10000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001526638414983/10000000000000000 : ℝ)) (X := (50032044503053446333/50000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1998561855134481/20000000000000000000 : ℝ) ≤ ((35639993568881461867/35650000000000000000 : ℝ)+2*(131314574561/89125000000000 : ℝ)*(11141/100000 : ℝ))^(2149/512 : ℝ) := by
    rw [show (35639993568881461867/35650000000000000000 : ℝ)+2*(131314574561/89125000000000 : ℝ)*(11141/100000 : ℝ)=(2000095224363699/2000000000000000 : ℝ) by norm_num, show 1+2*(1998561855134481/20000000000000000000 : ℝ)=(10001998561855134481/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32044503053446333/100000000000000000000 : ℝ)+(1998561855134481/20000000000000000000 : ℝ) ≤ ((35639993568881461867/35650000000000000000 : ℝ)+(131314574561/89125000000000 : ℝ)*((7353/50000 : ℝ)+(11141/100000 : ℝ)))^(2149/512 : ℝ) := by
    rw [show (35639993568881461867/35650000000000000000 : ℝ)+(131314574561/89125000000000 : ℝ)*((7353/50000 : ℝ)+(11141/100000 : ℝ))=(10001001380116739/10000000000000000 : ℝ) by norm_num, show 1+(32044503053446333/100000000000000000000 : ℝ)+(1998561855134481/20000000000000000000 : ℝ)=(50021018656164559369/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32044503053446333/100000000000000000000 : ℝ) ≤ ((35639993568881461867/35650000000000000000 : ℝ)+2*(131314574561/89125000000000 : ℝ)*(7353/50000 : ℝ))^(2149/512 : ℝ) := by
    rw [show (35639993568881461867/35650000000000000000 : ℝ)+2*(131314574561/89125000000000 : ℝ)*(7353/50000 : ℝ)=(10001526638414983/10000000000000000 : ℝ) by norm_num, show 1+2*(32044503053446333/100000000000000000000 : ℝ)=(50032044503053446333/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35639993568881461867/35650000000000000000 : ℝ)*(X 1 0+X 2 0)+(131314574561/89125000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (11141/100000 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (35639993568881461867/35650000000000000000 : ℝ)) (alpha := (131314574561/89125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35639993568881461867/35650000000000000000 : ℝ)*(X 0 1+X 2 1)+(131314574561/89125000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (11141/100000 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (35639993568881461867/35650000000000000000 : ℝ)) (alpha := (131314574561/89125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35639993568881461867/35650000000000000000 : ℝ)*(X 0 2+X 1 2)+(131314574561/89125000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (11141/100000 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (35639993568881461867/35650000000000000000 : ℝ)) (alpha := (131314574561/89125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-511642041/2500000000 : ℝ)*X 0 0+(2706407691/5000000000 : ℝ)*X 0 1+(2622280099/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349038607/10000000000 : ℝ)*X 1 0+(-2132296371/10000000000 : ℝ)*X 1 1+(2622280053/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349037981/10000000000 : ℝ)*X 2 0+(5244560371/10000000000 : ℝ)*X 2 1+(-426459371/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((865481351/2000000000 : ℝ)*X 0 0+(2077372043/5000000000 : ℝ)*X 0 1+(2253384821/5000000000 : ℝ)*X 0 2+(865481351/2000000000 : ℝ)*X 1 0+(2077372043/5000000000 : ℝ)*X 1 1+(2253384821/5000000000 : ℝ)*X 1 2+(865481351/2000000000 : ℝ)*X 2 0+(2077372043/5000000000 : ℝ)*X 2 1+(2253384821/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1023290143/5000000000 : ℝ)*X 0 0+(5245162119/10000000000 : ℝ)*X 0 1+(5412210411/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305714411/10000000000 : ℝ)*X 1 0+(-245580831/1250000000 : ℝ)*X 1 1+(5412210411/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305714413/10000000000 : ℝ)*X 2 0+(5412210409/10000000000 : ℝ)*X 2 1+(-245580831/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2163716191/5000000000 : ℝ)*X 0 0+(1126377493/2500000000 : ℝ)*X 0 1+(4156010127/10000000000 : ℝ)*X 0 2+(2163716191/5000000000 : ℝ)*X 1 0+(1126377493/2500000000 : ℝ)*X 1 1+(4156010127/10000000000 : ℝ)*X 1 2+(2163716191/5000000000 : ℝ)*X 2 0+(1126377493/2500000000 : ℝ)*X 2 1+(4156010127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1497799494652984984628462409/891250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (146333341/12500000000000 : ℝ)*(base19) + (91916923/20000000000000 : ℝ)*(base23) + (16055079/25000000000000 : ℝ)*(upper2) + (79830467/100000000000000 : ℝ)*(upper3) + (4392075673142009/100000000000000 : ℝ)*(major0) + (4392075673142009/100000000000000 : ℝ)*(major1) + (4392075673142009/100000000000000 : ℝ)*(major2) + (1188677794347163/20000000000000 : ℝ)*(sp0) + (5943412984076131/100000000000000 : ℝ)*(sp1) + (1188679391053143/20000000000000 : ℝ)*(sp2) + (2840721054161473/100000000000000 : ℝ)*(sp3) + (6295751761/25000000000000 : ℝ)*(sp4) + (16739892529/100000000000000 : ℝ)*(sp6) + (16081361001/100000000000000 : ℝ)*(sp7) + (1420368567761237/50000000000000 : ℝ)*(f.failure) + (5943414154742859/100000000000000 : ℝ)*(f.sum) + (24332122877529/17825000000000000000000000000 : ℝ)*base66 + (3091720132811129197/3565000000000000000000000000000000 : ℝ)*base68 + (26833953588326129197/3565000000000000000000000000000000 : ℝ)*base70 + (47874539977681129197/3565000000000000000000000000000000 : ℝ)*base72 + (50158127958771/17825000000000000000000000000 : ℝ)*base73 + (4610468823406129197/3565000000000000000000000000000000 : ℝ)*base76 + (11234369694556129197/3565000000000000000000000000000000 : ℝ)*base78 + (6577122923288870803/3565000000000000000000000000000000 : ℝ)*base79 + (696712180703/557031250000000000000000000 : ℝ)*base81 + (1093993/2500000000000000000000 : ℝ)*base90 + (1093993/2500000000000000000000 : ℝ)*base92 + (1093993/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1106685334555378431886934061/445625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (433207549/100000000000000 : ℝ)*(base19) + (14751151/3125000000000 : ℝ)*(base23) + (36849123/25000000000000 : ℝ)*(lower1) + (5135003/10000000000000 : ℝ)*(upper3) + (8297081/50000000000000 : ℝ)*(lower4) + (52107911/100000000000000 : ℝ)*(upper5) + (2211877775202539/50000000000000 : ℝ)*(major0) + (2211877775202539/50000000000000 : ℝ)*(major1) + (2211877775202539/50000000000000 : ℝ)*(major2) + (648677889/100000000000000 : ℝ)*(sp2) + (748285468998449/12500000000000 : ℝ)*(sp4) + (5986283318780043/100000000000000 : ℝ)*(sp5) + (5986282631272871/100000000000000 : ℝ)*(sp6) + (357653408255127/12500000000000 : ℝ)*(sp7) + (357653408255127/12500000000000 : ℝ)*(f.failure) + (748285468998449/12500000000000 : ℝ)*(f.sum) + (8659702222121/2228125000000000000000000000 : ℝ)*base66 + (3011478225018319687/1782500000000000000000000000000000 : ℝ)*base68 + (39628149286801680313/1782500000000000000000000000000000 : ℝ)*base69 + (254644189575719180313/1782500000000000000000000000000000 : ℝ)*base71 + (539462896701/557031250000000000000000000 : ℝ)*base73 + (283512638165819180313/1782500000000000000000000000000000 : ℝ)*base75 + (3646457052301680313/1782500000000000000000000000000000 : ℝ)*base77 + (9426051690156680313/1782500000000000000000000000000000 : ℝ)*base79 + (26756802678607/17825000000000000000000000000 : ℝ)*base81 + (2933203/625000000000000000000 : ℝ)*base90 + (2933203/625000000000000000000 : ℝ)*base92 + (2933203/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1339_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11141/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (919/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1339_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1339_box_0 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1879078061/10000000000 : ℝ)*x 0 + (107801289/200000000 : ℝ)*x 1 + (2695032149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1879078061/10000000000 : ℝ)^4299 ≤ (11141094930501/100000000000000 : ℝ)^3275 := by
    have hnat : (1879078061 : ℕ)^4299*100000000000000^3275 ≤ 11141094930501^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879078061 10000000000 11141094930501 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107801289/200000000 : ℝ)^4299 ≤ (44429453349503/100000000000000 : ℝ)^3275 := by
    have hnat : (107801289 : ℕ)^4299*100000000000000^3275 ≤ 44429453349503^3275*200000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107801289 200000000 44429453349503 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695032149/5000000000 : ℝ)^4299 ≤ (1110736292621/2500000000000 : ℝ)^3275 := by
    have hnat : (2695032149 : ℕ)^4299*2500000000000^3275 ≤ 1110736292621^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695032149 5000000000 1110736292621 2500000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1879078061/10000000000 : ℝ), (107801289/200000000 : ℝ), (2695032149/5000000000 : ℝ)] ![(11141094930501/100000000000000 : ℝ), (44429453349503/100000000000000 : ℝ), (1110736292621/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1879078061/10000000000 : ℝ)|^4299 ≤ (11141094930501/100000000000000 : ℝ)^3275
        have hw : |(-1879078061/10000000000 : ℝ)|=(1879078061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107801289/200000000 : ℝ)|^4299 ≤ (44429453349503/100000000000000 : ℝ)^3275
        have hw : |(107801289/200000000 : ℝ)|=(107801289/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695032149/5000000000 : ℝ)|^4299 ≤ (1110736292621/2500000000000 : ℝ)^3275
        have hw : |(2695032149/5000000000 : ℝ)|=(2695032149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_box_1 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285123753/10000000000 : ℝ)*x 0 + (-505708969/2500000000 : ℝ)*x 1 + (134751609/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285123753/10000000000 : ℝ)^4299 ≤ (10824362810973/25000000000000 : ℝ)^3275 := by
    have hnat : (5285123753 : ℕ)^4299*25000000000000^3275 ≤ 10824362810973^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285123753 10000000000 10824362810973 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505708969/2500000000 : ℝ)^4299 ≤ (12273096375243/100000000000000 : ℝ)^3275 := by
    have hnat : (505708969 : ℕ)^4299*100000000000000^3275 ≤ 12273096375243^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505708969 2500000000 12273096375243 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134751609/250000000 : ℝ)^4299 ≤ (44429452375689/100000000000000 : ℝ)^3275 := by
    have hnat : (134751609 : ℕ)^4299*100000000000000^3275 ≤ 44429452375689^3275*250000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134751609 250000000 44429452375689 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285123753/10000000000 : ℝ), (-505708969/2500000000 : ℝ), (134751609/250000000 : ℝ)] ![(10824362810973/25000000000000 : ℝ), (12273096375243/100000000000000 : ℝ), (44429452375689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285123753/10000000000 : ℝ)|^4299 ≤ (10824362810973/25000000000000 : ℝ)^3275
        have hw : |(5285123753/10000000000 : ℝ)|=(5285123753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-505708969/2500000000 : ℝ)|^4299 ≤ (12273096375243/100000000000000 : ℝ)^3275
        have hw : |(-505708969/2500000000 : ℝ)|=(505708969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134751609/250000000 : ℝ)|^4299 ≤ (44429452375689/100000000000000 : ℝ)^3275
        have hw : |(134751609/250000000 : ℝ)|=(134751609/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_box_2 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642561779/5000000000 : ℝ)*x 0 + (2695032287/5000000000 : ℝ)*x 1 + (-252854481/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642561779/5000000000 : ℝ)^4299 ≤ (8659489829379/20000000000000 : ℝ)^3275 := by
    have hnat : (2642561779 : ℕ)^4299*20000000000000^3275 ≤ 8659489829379^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642561779 5000000000 8659489829379 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695032287/5000000000 : ℝ)^4299 ≤ (44429454691201/100000000000000 : ℝ)^3275 := by
    have hnat : (2695032287 : ℕ)^4299*100000000000000^3275 ≤ 44429454691201^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695032287 5000000000 44429454691201 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252854481/1250000000 : ℝ)^4299 ≤ (6136548076121/50000000000000 : ℝ)^3275 := by
    have hnat : (252854481 : ℕ)^4299*50000000000000^3275 ≤ 6136548076121^3275*1250000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252854481 1250000000 6136548076121 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642561779/5000000000 : ℝ), (2695032287/5000000000 : ℝ), (-252854481/1250000000 : ℝ)] ![(8659489829379/20000000000000 : ℝ), (44429454691201/100000000000000 : ℝ), (6136548076121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642561779/5000000000 : ℝ)|^4299 ≤ (8659489829379/20000000000000 : ℝ)^3275
        have hw : |(2642561779/5000000000 : ℝ)|=(2642561779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695032287/5000000000 : ℝ)|^4299 ≤ (44429454691201/100000000000000 : ℝ)^3275
        have hw : |(2695032287/5000000000 : ℝ)|=(2695032287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-252854481/1250000000 : ℝ)|^4299 ≤ (6136548076121/50000000000000 : ℝ)^3275
        have hw : |(-252854481/1250000000 : ℝ)|=(252854481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_box_3 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4475664541/10000000000 : ℝ)*x 0 + (2128587157/5000000000 : ℝ)*x 1 + (2128587197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4475664541/10000000000 : ℝ)^4299 ≤ (6961783829317/20000000000000 : ℝ)^3275 := by
    have hnat : (4475664541 : ℕ)^4299*20000000000000^3275 ≤ 6961783829317^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475664541 10000000000 6961783829317 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2128587157/5000000000 : ℝ)^4299 ≤ (32595540016473/100000000000000 : ℝ)^3275 := by
    have hnat : (2128587157 : ℕ)^4299*100000000000000^3275 ≤ 32595540016473^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128587157 5000000000 32595540016473 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2128587197/5000000000 : ℝ)^4299 ≤ (16297770410261/50000000000000 : ℝ)^3275 := by
    have hnat : (2128587197 : ℕ)^4299*50000000000000^3275 ≤ 16297770410261^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128587197 5000000000 16297770410261 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4475664541/10000000000 : ℝ), (2128587157/5000000000 : ℝ), (2128587197/5000000000 : ℝ)] ![(6961783829317/20000000000000 : ℝ), (32595540016473/100000000000000 : ℝ), (16297770410261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4475664541/10000000000 : ℝ)|^4299 ≤ (6961783829317/20000000000000 : ℝ)^3275
        have hw : |(4475664541/10000000000 : ℝ)|=(4475664541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2128587157/5000000000 : ℝ)|^4299 ≤ (32595540016473/100000000000000 : ℝ)^3275
        have hw : |(2128587157/5000000000 : ℝ)|=(2128587157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2128587197/5000000000 : ℝ)|^4299 ≤ (16297770410261/50000000000000 : ℝ)^3275
        have hw : |(2128587197/5000000000 : ℝ)|=(2128587197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_box_4 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-69275329/312500000 : ℝ)*x 0 + (5264861173/10000000000 : ℝ)*x 1 + (5264860267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69275329/312500000 : ℝ)^4299 ≤ (13840646616067/100000000000000 : ℝ)^3275 := by
    have hnat : (69275329 : ℕ)^4299*100000000000000^3275 ≤ 13840646616067^3275*312500000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69275329 312500000 13840646616067 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264861173/10000000000 : ℝ)^4299 ≤ (10769920387329/25000000000000 : ℝ)^3275 := by
    have hnat : (5264861173 : ℕ)^4299*25000000000000^3275 ≤ 10769920387329^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264861173 10000000000 10769920387329 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264860267/10000000000 : ℝ)^4299 ≤ (21539835909019/50000000000000 : ℝ)^3275 := by
    have hnat : (5264860267 : ℕ)^4299*50000000000000^3275 ≤ 21539835909019^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264860267 10000000000 21539835909019 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69275329/312500000 : ℝ), (5264861173/10000000000 : ℝ), (5264860267/10000000000 : ℝ)] ![(13840646616067/100000000000000 : ℝ), (10769920387329/25000000000000 : ℝ), (21539835909019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69275329/312500000 : ℝ)|^4299 ≤ (13840646616067/100000000000000 : ℝ)^3275
        have hw : |(-69275329/312500000 : ℝ)|=(69275329/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264861173/10000000000 : ℝ)|^4299 ≤ (10769920387329/25000000000000 : ℝ)^3275
        have hw : |(5264861173/10000000000 : ℝ)|=(5264861173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264860267/10000000000 : ℝ)|^4299 ≤ (21539835909019/50000000000000 : ℝ)^3275
        have hw : |(5264860267/10000000000 : ℝ)|=(5264860267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_box_5 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83954319/156250000 : ℝ)*x 0 + (-1036527431/5000000000 : ℝ)*x 1 + (2632429961/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83954319/156250000 : ℝ)^4299 ≤ (44245730963449/100000000000000 : ℝ)^3275 := by
    have hnat : (83954319 : ℕ)^4299*100000000000000^3275 ≤ 44245730963449^3275*156250000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83954319 156250000 44245730963449 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036527431/5000000000 : ℝ)^4299 ≤ (12674600902279/100000000000000 : ℝ)^3275 := by
    have hnat : (1036527431 : ℕ)^4299*100000000000000^3275 ≤ 12674600902279^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036527431 5000000000 12674600902279 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632429961/5000000000 : ℝ)^4299 ≤ (43079668112419/100000000000000 : ℝ)^3275 := by
    have hnat : (2632429961 : ℕ)^4299*100000000000000^3275 ≤ 43079668112419^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632429961 5000000000 43079668112419 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83954319/156250000 : ℝ), (-1036527431/5000000000 : ℝ), (2632429961/5000000000 : ℝ)] ![(44245730963449/100000000000000 : ℝ), (12674600902279/100000000000000 : ℝ), (43079668112419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83954319/156250000 : ℝ)|^4299 ≤ (44245730963449/100000000000000 : ℝ)^3275
        have hw : |(83954319/156250000 : ℝ)|=(83954319/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1036527431/5000000000 : ℝ)|^4299 ≤ (12674600902279/100000000000000 : ℝ)^3275
        have hw : |(-1036527431/5000000000 : ℝ)|=(1036527431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632429961/5000000000 : ℝ)|^4299 ≤ (43079668112419/100000000000000 : ℝ)^3275
        have hw : |(2632429961/5000000000 : ℝ)|=(2632429961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_box_6 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373075699/10000000000 : ℝ)*x 0 + (2632430143/5000000000 : ℝ)*x 1 + (-2073055341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373075699/10000000000 : ℝ)^4299 ≤ (22122861606529/50000000000000 : ℝ)^3275 := by
    have hnat : (5373075699 : ℕ)^4299*50000000000000^3275 ≤ 22122861606529^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373075699 10000000000 22122861606529 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632430143/5000000000 : ℝ)^4299 ≤ (10769918005529/25000000000000 : ℝ)^3275 := by
    have hnat : (2632430143 : ℕ)^4299*25000000000000^3275 ≤ 10769918005529^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632430143 5000000000 10769918005529 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2073055341/10000000000 : ℝ)^4299 ≤ (39608139833/312500000000 : ℝ)^3275 := by
    have hnat : (2073055341 : ℕ)^4299*312500000000^3275 ≤ 39608139833^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073055341 10000000000 39608139833 312500000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373075699/10000000000 : ℝ), (2632430143/5000000000 : ℝ), (-2073055341/10000000000 : ℝ)] ![(22122861606529/50000000000000 : ℝ), (10769918005529/25000000000000 : ℝ), (39608139833/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373075699/10000000000 : ℝ)|^4299 ≤ (22122861606529/50000000000000 : ℝ)^3275
        have hw : |(5373075699/10000000000 : ℝ)|=(5373075699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632430143/5000000000 : ℝ)|^4299 ≤ (10769918005529/25000000000000 : ℝ)^3275
        have hw : |(2632430143/5000000000 : ℝ)|=(2632430143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2073055341/10000000000 : ℝ)|^4299 ≤ (39608139833/312500000000 : ℝ)^3275
        have hw : |(-2073055341/10000000000 : ℝ)|=(2073055341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_box_7 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4178228209/10000000000 : ℝ)*x 0 + (4405838339/10000000000 : ℝ)*x 1 + (4405839307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4178228209/10000000000 : ℝ)^4299 ≤ (6360878567757/20000000000000 : ℝ)^3275 := by
    have hnat : (4178228209 : ℕ)^4299*20000000000000^3275 ≤ 6360878567757^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4178228209 10000000000 6360878567757 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4405838339/10000000000 : ℝ)^4299 ≤ (34097798654421/100000000000000 : ℝ)^3275 := by
    have hnat : (4405838339 : ℕ)^4299*100000000000000^3275 ≤ 34097798654421^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4405838339 10000000000 34097798654421 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4405839307/10000000000 : ℝ)^4299 ≤ (85244521221/250000000000 : ℝ)^3275 := by
    have hnat : (4405839307 : ℕ)^4299*250000000000^3275 ≤ 85244521221^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4405839307 10000000000 85244521221 250000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4178228209/10000000000 : ℝ), (4405838339/10000000000 : ℝ), (4405839307/10000000000 : ℝ)] ![(6360878567757/20000000000000 : ℝ), (34097798654421/100000000000000 : ℝ), (85244521221/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4178228209/10000000000 : ℝ)|^4299 ≤ (6360878567757/20000000000000 : ℝ)^3275
        have hw : |(4178228209/10000000000 : ℝ)|=(4178228209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4405838339/10000000000 : ℝ)|^4299 ≤ (34097798654421/100000000000000 : ℝ)^3275
        have hw : |(4405838339/10000000000 : ℝ)|=(4405838339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4405839307/10000000000 : ℝ)|^4299 ≤ (85244521221/250000000000 : ℝ)^3275
        have hw : |(4405839307/10000000000 : ℝ)|=(4405839307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_box_8 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2145895609/10000000000 : ℝ)*x 0 + (5178680633/10000000000 : ℝ)*x 1 + (5404084977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145895609/10000000000 : ℝ)^4299 ≤ (1657797532061/12500000000000 : ℝ)^3275 := by
    have hnat : (2145895609 : ℕ)^4299*12500000000000^3275 ≤ 1657797532061^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145895609 10000000000 1657797532061 12500000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178680633/10000000000 : ℝ)^4299 ≤ (42156400560897/100000000000000 : ℝ)^3275 := by
    have hnat : (5178680633 : ℕ)^4299*100000000000000^3275 ≤ 42156400560897^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178680633 10000000000 42156400560897 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404084977/10000000000 : ℝ)^4299 ≤ (44581219164603/100000000000000 : ℝ)^3275 := by
    have hnat : (5404084977 : ℕ)^4299*100000000000000^3275 ≤ 44581219164603^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404084977 10000000000 44581219164603 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2145895609/10000000000 : ℝ), (5178680633/10000000000 : ℝ), (5404084977/10000000000 : ℝ)] ![(1657797532061/12500000000000 : ℝ), (42156400560897/100000000000000 : ℝ), (44581219164603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2145895609/10000000000 : ℝ)|^4299 ≤ (1657797532061/12500000000000 : ℝ)^3275
        have hw : |(-2145895609/10000000000 : ℝ)|=(2145895609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178680633/10000000000 : ℝ)|^4299 ≤ (42156400560897/100000000000000 : ℝ)^3275
        have hw : |(5178680633/10000000000 : ℝ)|=(5178680633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404084977/10000000000 : ℝ)|^4299 ≤ (44581219164603/100000000000000 : ℝ)^3275
        have hw : |(5404084977/10000000000 : ℝ)|=(5404084977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_box_9 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263763469/500000000 : ℝ)*x 0 + (-2017079633/10000000000 : ℝ)*x 1 + (5404084869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263763469/500000000 : ℝ)^4299 ≤ (10797877465053/25000000000000 : ℝ)^3275 := by
    have hnat : (263763469 : ℕ)^4299*25000000000000^3275 ≤ 10797877465053^3275*500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263763469 500000000 10797877465053 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2017079633/10000000000 : ℝ)^4299 ≤ (6113636061771/50000000000000 : ℝ)^3275 := by
    have hnat : (2017079633 : ℕ)^4299*50000000000000^3275 ≤ 6113636061771^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017079633 10000000000 6113636061771 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404084869/10000000000 : ℝ)^4299 ≤ (44581217995077/100000000000000 : ℝ)^3275 := by
    have hnat : (5404084869 : ℕ)^4299*100000000000000^3275 ≤ 44581217995077^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404084869 10000000000 44581217995077 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263763469/500000000 : ℝ), (-2017079633/10000000000 : ℝ), (5404084869/10000000000 : ℝ)] ![(10797877465053/25000000000000 : ℝ), (6113636061771/50000000000000 : ℝ), (44581217995077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263763469/500000000 : ℝ)|^4299 ≤ (10797877465053/25000000000000 : ℝ)^3275
        have hw : |(263763469/500000000 : ℝ)|=(263763469/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2017079633/10000000000 : ℝ)|^4299 ≤ (6113636061771/50000000000000 : ℝ)^3275
        have hw : |(-2017079633/10000000000 : ℝ)|=(2017079633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404084869/10000000000 : ℝ)|^4299 ≤ (44581217995077/100000000000000 : ℝ)^3275
        have hw : |(5404084869/10000000000 : ℝ)|=(5404084869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_box_10 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1318817261/2500000000 : ℝ)*x 0 + (675510657/1250000000 : ℝ)*x 1 + (-2017079561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318817261/2500000000 : ℝ)^4299 ≤ (5398938281129/12500000000000 : ℝ)^3275 := by
    have hnat : (1318817261 : ℕ)^4299*12500000000000^3275 ≤ 5398938281129^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318817261 2500000000 5398938281129 12500000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675510657/1250000000 : ℝ)^4299 ≤ (44581222185877/100000000000000 : ℝ)^3275 := by
    have hnat : (675510657 : ℕ)^4299*100000000000000^3275 ≤ 44581222185877^3275*1250000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675510657 1250000000 44581222185877 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2017079561/10000000000 : ℝ)^4299 ≤ (12227271550621/100000000000000 : ℝ)^3275 := by
    have hnat : (2017079561 : ℕ)^4299*100000000000000^3275 ≤ 12227271550621^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017079561 10000000000 12227271550621 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318817261/2500000000 : ℝ), (675510657/1250000000 : ℝ), (-2017079561/10000000000 : ℝ)] ![(5398938281129/12500000000000 : ℝ), (44581222185877/100000000000000 : ℝ), (12227271550621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318817261/2500000000 : ℝ)|^4299 ≤ (5398938281129/12500000000000 : ℝ)^3275
        have hw : |(1318817261/2500000000 : ℝ)|=(1318817261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675510657/1250000000 : ℝ)|^4299 ≤ (44581222185877/100000000000000 : ℝ)^3275
        have hw : |(675510657/1250000000 : ℝ)|=(675510657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2017079561/10000000000 : ℝ)|^4299 ≤ (12227271550621/100000000000000 : ℝ)^3275
        have hw : |(-2017079561/10000000000 : ℝ)|=(2017079561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_box_11 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (563551673/1250000000 : ℝ)*x 0 + (848102453/2000000000 : ℝ)*x 1 + (848102537/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (563551673/1250000000 : ℝ)^4299 ≤ (4392954810077/12500000000000 : ℝ)^3275 := by
    have hnat : (563551673 : ℕ)^4299*12500000000000^3275 ≤ 4392954810077^3275*1250000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563551673 1250000000 4392954810077 12500000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (848102453/2000000000 : ℝ)^4299 ≤ (6485635727963/20000000000000 : ℝ)^3275 := by
    have hnat : (848102453 : ℕ)^4299*20000000000000^3275 ≤ 6485635727963^3275*2000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848102453 2000000000 6485635727963 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848102537/2000000000 : ℝ)^4299 ≤ (32428182855903/100000000000000 : ℝ)^3275 := by
    have hnat : (848102537 : ℕ)^4299*100000000000000^3275 ≤ 32428182855903^3275*2000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848102537 2000000000 32428182855903 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(563551673/1250000000 : ℝ), (848102453/2000000000 : ℝ), (848102537/2000000000 : ℝ)] ![(4392954810077/12500000000000 : ℝ), (6485635727963/20000000000000 : ℝ), (32428182855903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(563551673/1250000000 : ℝ)|^4299 ≤ (4392954810077/12500000000000 : ℝ)^3275
        have hw : |(563551673/1250000000 : ℝ)|=(563551673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(848102453/2000000000 : ℝ)|^4299 ≤ (6485635727963/20000000000000 : ℝ)^3275
        have hw : |(848102453/2000000000 : ℝ)|=(848102453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848102537/2000000000 : ℝ)|^4299 ≤ (32428182855903/100000000000000 : ℝ)^3275
        have hw : |(848102537/2000000000 : ℝ)|=(848102537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_box_12 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-390067357/2000000000 : ℝ)*x 0 + (5474032339/10000000000 : ℝ)*x 1 + (2626896837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (390067357/2000000000 : ℝ)^4299 ≤ (1462368928991/12500000000000 : ℝ)^3275 := by
    have hnat : (390067357 : ℕ)^4299*12500000000000^3275 ≤ 1462368928991^3275*2000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390067357 2000000000 1462368928991 12500000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5474032339/10000000000 : ℝ)^4299 ≤ (22670101548449/50000000000000 : ℝ)^3275 := by
    have hnat : (5474032339 : ℕ)^4299*50000000000000^3275 ≤ 22670101548449^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474032339 10000000000 22670101548449 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626896837/5000000000 : ℝ)^4299 ≤ (8592169090799/20000000000000 : ℝ)^3275 := by
    have hnat : (2626896837 : ℕ)^4299*20000000000000^3275 ≤ 8592169090799^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626896837 5000000000 8592169090799 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-390067357/2000000000 : ℝ), (5474032339/10000000000 : ℝ), (2626896837/5000000000 : ℝ)] ![(1462368928991/12500000000000 : ℝ), (22670101548449/50000000000000 : ℝ), (8592169090799/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-390067357/2000000000 : ℝ)|^4299 ≤ (1462368928991/12500000000000 : ℝ)^3275
        have hw : |(-390067357/2000000000 : ℝ)|=(390067357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5474032339/10000000000 : ℝ)|^4299 ≤ (22670101548449/50000000000000 : ℝ)^3275
        have hw : |(5474032339/10000000000 : ℝ)|=(5474032339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626896837/5000000000 : ℝ)|^4299 ≤ (8592169090799/20000000000000 : ℝ)^3275
        have hw : |(2626896837/5000000000 : ℝ)|=(2626896837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_box_13 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380847127/10000000000 : ℝ)*x 0 + (-103869509/500000000 : ℝ)*x 1 + (5253793797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380847127/10000000000 : ℝ)^4299 ≤ (44329747235029/100000000000000 : ℝ)^3275 := by
    have hnat : (5380847127 : ℕ)^4299*100000000000000^3275 ≤ 44329747235029^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380847127 10000000000 44329747235029 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103869509/500000000 : ℝ)^4299 ≤ (3177351492731/25000000000000 : ℝ)^3275 := by
    have hnat : (103869509 : ℕ)^4299*25000000000000^3275 ≤ 3177351492731^3275*500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103869509 500000000 3177351492731 25000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253793797/10000000000 : ℝ)^4299 ≤ (2148042338713/5000000000000 : ℝ)^3275 := by
    have hnat : (5253793797 : ℕ)^4299*5000000000000^3275 ≤ 2148042338713^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253793797 10000000000 2148042338713 5000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380847127/10000000000 : ℝ), (-103869509/500000000 : ℝ), (5253793797/10000000000 : ℝ)] ![(44329747235029/100000000000000 : ℝ), (3177351492731/25000000000000 : ℝ), (2148042338713/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380847127/10000000000 : ℝ)|^4299 ≤ (44329747235029/100000000000000 : ℝ)^3275
        have hw : |(5380847127/10000000000 : ℝ)|=(5380847127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103869509/500000000 : ℝ)|^4299 ≤ (3177351492731/25000000000000 : ℝ)^3275
        have hw : |(-103869509/500000000 : ℝ)|=(103869509/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253793797/10000000000 : ℝ)|^4299 ≤ (2148042338713/5000000000000 : ℝ)^3275
        have hw : |(5253793797/10000000000 : ℝ)|=(5253793797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_box_14 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380847387/10000000000 : ℝ)*x 0 + (5253793609/10000000000 : ℝ)*x 1 + (-1038695041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380847387/10000000000 : ℝ)^4299 ≤ (22164875023381/50000000000000 : ℝ)^3275 := by
    have hnat : (5380847387 : ℕ)^4299*50000000000000^3275 ≤ 22164875023381^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380847387 10000000000 22164875023381 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253793609/10000000000 : ℝ)^4299 ≤ (8592168951259/20000000000000 : ℝ)^3275 := by
    have hnat : (5253793609 : ℕ)^4299*20000000000000^3275 ≤ 8592168951259^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253793609 10000000000 8592168951259 20000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038695041/5000000000 : ℝ)^4299 ≤ (6354702591949/50000000000000 : ℝ)^3275 := by
    have hnat : (1038695041 : ℕ)^4299*50000000000000^3275 ≤ 6354702591949^3275*5000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038695041 5000000000 6354702591949 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380847387/10000000000 : ℝ), (5253793609/10000000000 : ℝ), (-1038695041/5000000000 : ℝ)] ![(22164875023381/50000000000000 : ℝ), (8592168951259/20000000000000 : ℝ), (6354702591949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380847387/10000000000 : ℝ)|^4299 ≤ (22164875023381/50000000000000 : ℝ)^3275
        have hw : |(5380847387/10000000000 : ℝ)|=(5380847387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253793609/10000000000 : ℝ)|^4299 ≤ (8592168951259/20000000000000 : ℝ)^3275
        have hw : |(5253793609/10000000000 : ℝ)|=(5253793609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1038695041/5000000000 : ℝ)|^4299 ≤ (6354702591949/50000000000000 : ℝ)^3275
        have hw : |(-1038695041/5000000000 : ℝ)|=(1038695041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1339_box_15 (p : ℝ) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1037872657/2500000000 : ℝ)*x 0 + (4418968381/10000000000 : ℝ)*x 1 + (4418968483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037872657/2500000000 : ℝ)^4299 ≤ (15768749709549/50000000000000 : ℝ)^3275 := by
    have hnat : (1037872657 : ℕ)^4299*50000000000000^3275 ≤ 15768749709549^3275*2500000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037872657 2500000000 15768749709549 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4418968381/10000000000 : ℝ)^4299 ≤ (17115624882857/50000000000000 : ℝ)^3275 := by
    have hnat : (4418968381 : ℕ)^4299*50000000000000^3275 ≤ 17115624882857^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418968381 10000000000 17115624882857 50000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4418968483/10000000000 : ℝ)^4299 ≤ (34231250802903/100000000000000 : ℝ)^3275 := by
    have hnat : (4418968483 : ℕ)^4299*100000000000000^3275 ≤ 34231250802903^3275*10000000000^4299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418968483 10000000000 34231250802903 100000000000000 4299 3275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4299/1024 : ℝ)) 4299 3275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037872657/2500000000 : ℝ), (4418968381/10000000000 : ℝ), (4418968483/10000000000 : ℝ)] ![(15768749709549/50000000000000 : ℝ), (17115624882857/50000000000000 : ℝ), (34231250802903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037872657/2500000000 : ℝ)|^4299 ≤ (15768749709549/50000000000000 : ℝ)^3275
        have hw : |(1037872657/2500000000 : ℝ)|=(1037872657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4418968381/10000000000 : ℝ)|^4299 ≤ (17115624882857/50000000000000 : ℝ)^3275
        have hw : |(4418968381/10000000000 : ℝ)|=(4418968381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4418968483/10000000000 : ℝ)|^4299 ≤ (34231250802903/100000000000000 : ℝ)^3275
        have hw : |(4418968483/10000000000 : ℝ)|=(4418968483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1339_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (919/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31427/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11787/20000 : ℝ) ∧ (79937/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (4217/5000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (919/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11143/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (919/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11143/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (919/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11143/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (919/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11143/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (919/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11143/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (919/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11143/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11143/100000 : ℝ) ^ (2149/512 : ℝ) ≤ (5000170414084729/50000000000000000000 : ℝ) := by
    have hpowers : (11143/100000 : ℝ)^2149 ≤ (5000170414084729/50000000000000000000 : ℝ)^512 := by
      have hnat : (11143 : ℕ)^2149*50000000000000000000^512 ≤ 5000170414084729^512*100000^2149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11143 100000 5000170414084729 50000000000000000000 2149 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11143/100000 : ℝ)) (X := (5000170414084729/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hpowhi : (919/6250 : ℝ) ^ (2149/512 : ℝ) ≤ (6405243054528633/20000000000000000000 : ℝ) := by
    have hpowers : (919/6250 : ℝ)^2149 ≤ (6405243054528633/20000000000000000000 : ℝ)^512 := by
      have hnat : (919 : ℕ)^2149*20000000000000000000^512 ≤ 6405243054528633^512*6250^2149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        919 6250 6405243054528633 20000000000000000000 2149 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (919/6250 : ℝ)) (X := (6405243054528633/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005000170414084729/25000000000000000000 : ℝ) ≤ (200009529612857/200000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (25005000170414084729/25000000000000000000 : ℝ)^512 ≤ (200009529612857/200000000000000 : ℝ)^2149 := by
      have hnat : (25005000170414084729 : ℕ)^512*200000000000000^2149 ≤ 200009529612857^2149*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005000170414084729 25000000000000000000 200009529612857 200000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200009529612857/200000000000000 : ℝ)) (X := (25005000170414084729/25000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042026556100812623/100000000000000000000 : ℝ) ≤ (2000200224786249/2000000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (100042026556100812623/100000000000000000000 : ℝ)^512 ≤ (2000200224786249/2000000000000000 : ℝ)^2149 := by
      have hnat : (100042026556100812623 : ℕ)^512*2000000000000000^2149 ≤ 2000200224786249^2149*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042026556100812623 100000000000000000000 2000200224786249 2000000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000200224786249/2000000000000000 : ℝ)) (X := (100042026556100812623/100000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006405243054528633/10000000000000000000 : ℝ) ≤ (250038144180491/250000000000000 : ℝ) ^ (2149/512 : ℝ) := by
    have hpowers : (10006405243054528633/10000000000000000000 : ℝ)^512 ≤ (250038144180491/250000000000000 : ℝ)^2149 := by
      have hnat : (10006405243054528633 : ℕ)^512*250000000000000^2149 ≤ 250038144180491^2149*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006405243054528633 10000000000000000000 250038144180491 250000000000000 512 2149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250038144180491/250000000000000 : ℝ)) (X := (10006405243054528633/10000000000000000000 : ℝ)) (by norm_num) 2149 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5000170414084729/50000000000000000000 : ℝ) ≤ ((890000113681100447/890250000000000000 : ℝ)+2*(104928657679/71220000000000 : ℝ)*(11143/100000 : ℝ))^(2149/512 : ℝ) := by
    rw [show (890000113681100447/890250000000000000 : ℝ)+2*(104928657679/71220000000000 : ℝ)*(11143/100000 : ℝ)=(200009529612857/200000000000000 : ℝ) by norm_num, show 1+2*(5000170414084729/50000000000000000000 : ℝ)=(25005000170414084729/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6405243054528633/20000000000000000000 : ℝ)+(5000170414084729/50000000000000000000 : ℝ) ≤ ((890000113681100447/890250000000000000 : ℝ)+(104928657679/71220000000000 : ℝ)*((919/6250 : ℝ)+(11143/100000 : ℝ)))^(2149/512 : ℝ) := by
    rw [show (890000113681100447/890250000000000000 : ℝ)+(104928657679/71220000000000 : ℝ)*((919/6250 : ℝ)+(11143/100000 : ℝ))=(2000200224786249/2000000000000000 : ℝ) by norm_num, show 1+(6405243054528633/20000000000000000000 : ℝ)+(5000170414084729/50000000000000000000 : ℝ)=(100042026556100812623/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6405243054528633/20000000000000000000 : ℝ) ≤ ((890000113681100447/890250000000000000 : ℝ)+2*(104928657679/71220000000000 : ℝ)*(919/6250 : ℝ))^(2149/512 : ℝ) := by
    rw [show (890000113681100447/890250000000000000 : ℝ)+2*(104928657679/71220000000000 : ℝ)*(919/6250 : ℝ)=(250038144180491/250000000000000 : ℝ) by norm_num, show 1+2*(6405243054528633/20000000000000000000 : ℝ)=(10006405243054528633/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (890000113681100447/890250000000000000 : ℝ)*(X 1 0+X 2 0)+(104928657679/71220000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (11143/100000 : ℝ)) (hi := (919/6250 : ℝ)) (c := (890000113681100447/890250000000000000 : ℝ)) (alpha := (104928657679/71220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (890000113681100447/890250000000000000 : ℝ)*(X 0 1+X 2 1)+(104928657679/71220000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (11143/100000 : ℝ)) (hi := (919/6250 : ℝ)) (c := (890000113681100447/890250000000000000 : ℝ)) (alpha := (104928657679/71220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (890000113681100447/890250000000000000 : ℝ)*(X 0 2+X 1 2)+(104928657679/71220000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2149/512 : ℝ)) (lo := (11143/100000 : ℝ)) (hi := (919/6250 : ℝ)) (c := (890000113681100447/890250000000000000 : ℝ)) (alpha := (104928657679/71220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1879078061/10000000000 : ℝ)*X 0 0+(107801289/200000000 : ℝ)*X 0 1+(2695032149/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285123753/10000000000 : ℝ)*X 1 0+(-505708969/2500000000 : ℝ)*X 1 1+(134751609/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642561779/5000000000 : ℝ)*X 2 0+(2695032287/5000000000 : ℝ)*X 2 1+(-252854481/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4475664541/10000000000 : ℝ)*X 0 0+(2128587157/5000000000 : ℝ)*X 0 1+(2128587197/5000000000 : ℝ)*X 0 2+(4475664541/10000000000 : ℝ)*X 1 0+(2128587157/5000000000 : ℝ)*X 1 1+(2128587197/5000000000 : ℝ)*X 1 2+(4475664541/10000000000 : ℝ)*X 2 0+(2128587157/5000000000 : ℝ)*X 2 1+(2128587197/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-69275329/312500000 : ℝ)*X 0 0+(5264861173/10000000000 : ℝ)*X 0 1+(5264860267/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((83954319/156250000 : ℝ)*X 1 0+(-1036527431/5000000000 : ℝ)*X 1 1+(2632429961/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5373075699/10000000000 : ℝ)*X 2 0+(2632430143/5000000000 : ℝ)*X 2 1+(-2073055341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4178228209/10000000000 : ℝ)*X 0 0+(4405838339/10000000000 : ℝ)*X 0 1+(4405839307/10000000000 : ℝ)*X 0 2+(4178228209/10000000000 : ℝ)*X 1 0+(4405838339/10000000000 : ℝ)*X 1 1+(4405839307/10000000000 : ℝ)*X 1 2+(4178228209/10000000000 : ℝ)*X 2 0+(4405838339/10000000000 : ℝ)*X 2 1+(4405839307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2145895609/10000000000 : ℝ)*X 0 0+(5178680633/10000000000 : ℝ)*X 0 1+(5404084977/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((263763469/500000000 : ℝ)*X 1 0+(-2017079633/10000000000 : ℝ)*X 1 1+(5404084869/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1318817261/2500000000 : ℝ)*X 2 0+(675510657/1250000000 : ℝ)*X 2 1+(-2017079561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((563551673/1250000000 : ℝ)*X 0 0+(848102453/2000000000 : ℝ)*X 0 1+(848102537/2000000000 : ℝ)*X 0 2+(563551673/1250000000 : ℝ)*X 1 0+(848102453/2000000000 : ℝ)*X 1 1+(848102537/2000000000 : ℝ)*X 1 2+(563551673/1250000000 : ℝ)*X 2 0+(848102453/2000000000 : ℝ)*X 2 1+(848102537/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-390067357/2000000000 : ℝ)*X 0 0+(5474032339/10000000000 : ℝ)*X 0 1+(2626896837/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5380847127/10000000000 : ℝ)*X 1 0+(-103869509/500000000 : ℝ)*X 1 1+(5253793797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5380847387/10000000000 : ℝ)*X 2 0+(5253793609/10000000000 : ℝ)*X 2 1+(-1038695041/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1037872657/2500000000 : ℝ)*X 0 0+(4418968381/10000000000 : ℝ)*X 0 1+(4418968483/10000000000 : ℝ)*X 0 2+(1037872657/2500000000 : ℝ)*X 1 0+(4418968381/10000000000 : ℝ)*X 1 1+(4418968483/10000000000 : ℝ)*X 1 2+(1037872657/2500000000 : ℝ)*X 2 0+(4418968381/10000000000 : ℝ)*X 2 1+(4418968483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1339_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31427/50000 : ℝ) ≤ (-2331401522669708858737666007919/3709375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17486319/50000000000000 : ℝ)*(lower3) + (167983107/50000000000000 : ℝ)*(lower4) + (13068589/100000000000000 : ℝ)*(lower5) + (91166438719377/3125000000000 : ℝ)*(major0) + (91166438719377/3125000000000 : ℝ)*(major1) + (91166438719377/3125000000000 : ℝ)*(major2) + (4056084369/25000000000000 : ℝ)*(sp1) + (689674689/3125000000000 : ℝ)*(sp2) + (4026763091/50000000000000 : ℝ)*(sp3) + (1984353497154427/50000000000000 : ℝ)*(sp4) + (124021813685221/3125000000000 : ℝ)*(sp5) + (7937384385349/200000000000 : ℝ)*(sp6) + (943440147724727/50000000000000 : ℝ)*(sp7) + (7267955693/100000000000000 : ℝ)*(sp8) + (1886888348975637/100000000000000 : ℝ)*(f.failure) + (992178565566137/25000000000000 : ℝ)*(f.sum) + (1975595092539/1187000000000000000000000000 : ℝ)*base65 + (18049000899835683/3709375000000000000000000000000 : ℝ)*base68 + (14690438927648183/3709375000000000000000000000000 : ℝ)*base70 + (7711341587600327/927343750000000000000000000000 : ℝ)*base72 + (1682964324767/593500000000000000000000000 : ℝ)*base73 + (1294738580003779/1854687500000000000000000000000 : ℝ)*base76 + (12039556166544077/927343750000000000000000000000 : ℝ)*base78 + (7850014287991279/1854687500000000000000000000000 : ℝ)*base80 + (4641957174109/593500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (52144407/5000000000000000000000 : ℝ)*base89 + (52144407/5000000000000000000000 : ℝ)*base91 + (52144407/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (11787/20000 : ℝ) ≤ (87449087584593786352661503/148375000000000000000000000 : ℝ) := by norm_num
    linear_combination (3400981/20000000000000 : ℝ)*(lower1) + (1050933/5000000000000 : ℝ)*(upper2) + (53799/781250000000 : ℝ)*(upper3) + (8089309/50000000000000 : ℝ)*(lower5) + (373239408040043/12500000000000 : ℝ)*(major0) + (373239408040043/12500000000000 : ℝ)*(major1) + (373239408040043/12500000000000 : ℝ)*(major2) + (2010466431344133/50000000000000 : ℝ)*(sp0) + (2010466801729707/50000000000000 : ℝ)*(sp1) + (4020927078371553/100000000000000 : ℝ)*(sp2) + (965625184891011/50000000000000 : ℝ)*(sp3) + (6525087861/100000000000000 : ℝ)*(sp6) + (296785879/50000000000000 : ℝ)*(sp7) + (185192787/25000000000000 : ℝ)*(sp8) + (1931250963353779/100000000000000 : ℝ)*(f.failure) + (2010466801729707/50000000000000 : ℝ)*(f.sum) + (126173049187/71220000000000000000000000 : ℝ)*base66 + (35799767183507029/11128125000000000000000000000000 : ℝ)*base68 + (78256013888292971/11128125000000000000000000000000 : ℝ)*base69 + (45261241938294529/11128125000000000000000000000000 : ℝ)*base72 + (574143595201/356100000000000000000000000 : ℝ)*base73 + (90097293948492971/11128125000000000000000000000000 : ℝ)*base75 + (2835561934620899/2782031250000000000000000000000 : ℝ)*base77 + (34049661253269529/11128125000000000000000000000000 : ℝ)*base80 + (38157174001507/3561000000000000000000000000 : ℝ)*base81 + (46757631/5000000000000000000000 : ℝ)*base90 + (46757631/5000000000000000000000 : ℝ)*base92 + (46757631/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (79937/100000 : ℝ) ≤ (593050146703803609541769143529/741875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6527009/12500000000000 : ℝ)*(upper0) + (59478491/100000000000000 : ℝ)*(upper2) + (16989891/100000000000000 : ℝ)*(lower3) + (41227072448861/1250000000000 : ℝ)*(major0) + (41227072448861/1250000000000 : ℝ)*(major1) + (41227072448861/1250000000000 : ℝ)*(major2) + (2867726183/100000000000000 : ℝ)*(sp0) + (90909663563/100000000000000 : ℝ)*(sp2) + (18898762481/50000000000000 : ℝ)*(sp3) + (2218234977056231/50000000000000 : ℝ)*(sp8) + (4436474611914827/100000000000000 : ℝ)*(sp9) + (17329623836919/390625000000 : ℝ)*(sp10) + (533293182039829/25000000000000 : ℝ)*(sp11) + (895038091/50000000000000 : ℝ)*(sp12) + (1066605262842139/50000000000000 : ℝ)*(f.failure) + (4436474611914827/100000000000000 : ℝ)*(f.sum) + (506497472437/142440000000000000000000000 : ℝ)*base65 + (1769591659538377/278203125000000000000000000000 : ℝ)*base68 + (9734636457054133/1112812500000000000000000000000 : ℝ)*base70 + (2165231485662127/278203125000000000000000000000 : ℝ)*base72 + (7317856737317/3561000000000000000000000000 : ℝ)*base74 + (24025087421487641/2225625000000000000000000000000 : ℝ)*base76 + (552408213620383/1112812500000000000000000000000 : ℝ)*base78 + (8239251657416129/556406250000000000000000000000 : ℝ)*base80 + (35623036337/44512500000000000000000000 : ℝ)*base81 + (15086329/2500000000000000000000 : ℝ)*base89 + (15086329/2500000000000000000000 : ℝ)*base91 + (15086329/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-4217/5000 : ℝ) ≤ (-1001089774897725035163875813/1187000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6752063/20000000000000 : ℝ)*(lower1) + (78157077/100000000000000 : ℝ)*(lower2) + (54982483/100000000000000 : ℝ)*(upper5) + (208412309500147/6250000000000 : ℝ)*(major0) + (208412309500147/6250000000000 : ℝ)*(major1) + (208412309500147/6250000000000 : ℝ)*(major2) + (781416309/12500000000000 : ℝ)*(sp0) + (57019988683/100000000000000 : ℝ)*(sp5) + (108348868331/100000000000000 : ℝ)*(sp6) + (410009831/100000000000000 : ℝ)*(sp7) + (181621061357017/4000000000000 : ℝ)*(sp12) + (2270237882633607/50000000000000 : ℝ)*(sp13) + (2270212218193783/50000000000000 : ℝ)*(sp14) + (1078386655617699/50000000000000 : ℝ)*(sp15) + (2156773721245229/100000000000000 : ℝ)*(f.failure) + (4540532785255897/100000000000000 : ℝ)*(f.sum) + (13434807425779/1780500000000000000000000000 : ℝ)*base66 + (8504709471134417/2782031250000000000000000000000 : ℝ)*base67 + (51861772797446707/11128125000000000000000000000000 : ℝ)*base70 + (12683260987578293/11128125000000000000000000000000 : ℝ)*base71 + (16756777036567/3561000000000000000000000000 : ℝ)*base73 + (58555163915752957/11128125000000000000000000000000 : ℝ)*base76 + (4509697594117177/695507812500000000000000000000 : ℝ)*base78 + (24786623948647043/11128125000000000000000000000000 : ℝ)*base79 + (257415423157/178050000000000000000000000 : ℝ)*base82 + (10588319/5000000000000000000000 : ℝ)*base89 + (10588319/5000000000000000000000 : ℝ)*base91 + (10588319/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1339_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (919/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31427/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11787/20000 : ℝ) else (79937/100000 : ℝ) ≤ X j i ∧ X j i ≤ (4217/5000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1339_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1339_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5567/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31427/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11787/20000 : ℝ) else (79937/100000 : ℝ) ≤ X j i ∧ X j i ≤ (4217/5000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1339_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1339_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1339_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2149/512 : ℝ) ≤ p) (hpb : p ≤ (4299/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77305211/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5567/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31427/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11787/20000 : ℝ) else (79937/100000 : ℝ) ≤ X j i ∧ X j i ≤ (4217/5000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1339_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
