-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1476_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:12:24.214185+00:00
-- url     : https://prove2.me/submissions/e91943c7-3215-48cc-971a-c4c517112cc2

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
theorem support_rectangle_w1476_s3_0 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-240222273/1250000000 : ℝ)*x 0 + (5442886247/10000000000 : ℝ)*x 1 + (1042234967/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (240222273/1250000000 : ℝ)^4449 ≤ (2347341161757/20000000000000 : ℝ)^3425 := by
    have hnat : (240222273 : ℕ)^4449*20000000000000^3425 ≤ 2347341161757^3425*1250000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240222273 1250000000 2347341161757 20000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442886247/10000000000 : ℝ)^4449 ≤ (2268913792403/5000000000000 : ℝ)^3425 := by
    have hnat : (5442886247 : ℕ)^4449*5000000000000^3425 ≤ 2268913792403^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442886247 10000000000 2268913792403 5000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042234967/2000000000 : ℝ)^4449 ≤ (42885018330231/100000000000000 : ℝ)^3425 := by
    have hnat : (1042234967 : ℕ)^4449*100000000000000^3425 ≤ 42885018330231^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042234967 2000000000 42885018330231 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-240222273/1250000000 : ℝ), (5442886247/10000000000 : ℝ), (1042234967/2000000000 : ℝ)] ![(2347341161757/20000000000000 : ℝ), (2268913792403/5000000000000 : ℝ), (42885018330231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-240222273/1250000000 : ℝ)|^4449 ≤ (2347341161757/20000000000000 : ℝ)^3425
        have hw : |(-240222273/1250000000 : ℝ)|=(240222273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442886247/10000000000 : ℝ)|^4449 ≤ (2268913792403/5000000000000 : ℝ)^3425
        have hw : |(5442886247/10000000000 : ℝ)|=(5442886247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042234967/2000000000 : ℝ)|^4449 ≤ (42885018330231/100000000000000 : ℝ)^3425
        have hw : |(1042234967/2000000000 : ℝ)|=(1042234967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s3_1 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677396627/5000000000 : ℝ)*x 0 + (-2040661113/10000000000 : ℝ)*x 1 + (2605587413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677396627/5000000000 : ℝ)^4449 ≤ (44426563118183/100000000000000 : ℝ)^3425 := by
    have hnat : (2677396627 : ℕ)^4449*100000000000000^3425 ≤ 44426563118183^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677396627 5000000000 44426563118183 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2040661113/10000000000 : ℝ)^4449 ≤ (1268841862671/10000000000000 : ℝ)^3425 := by
    have hnat : (2040661113 : ℕ)^4449*10000000000000^3425 ≤ 1268841862671^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040661113 10000000000 1268841862671 10000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2605587413/5000000000 : ℝ)^4449 ≤ (21442509117011/50000000000000 : ℝ)^3425 := by
    have hnat : (2605587413 : ℕ)^4449*50000000000000^3425 ≤ 21442509117011^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605587413 5000000000 21442509117011 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677396627/5000000000 : ℝ), (-2040661113/10000000000 : ℝ), (2605587413/5000000000 : ℝ)] ![(44426563118183/100000000000000 : ℝ), (1268841862671/10000000000000 : ℝ), (21442509117011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677396627/5000000000 : ℝ)|^4449 ≤ (44426563118183/100000000000000 : ℝ)^3425
        have hw : |(2677396627/5000000000 : ℝ)|=(2677396627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2040661113/10000000000 : ℝ)|^4449 ≤ (1268841862671/10000000000000 : ℝ)^3425
        have hw : |(-2040661113/10000000000 : ℝ)|=(2040661113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2605587413/5000000000 : ℝ)|^4449 ≤ (21442509117011/50000000000000 : ℝ)^3425
        have hw : |(2605587413/5000000000 : ℝ)|=(2605587413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s3_2 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677396651/5000000000 : ℝ)*x 0 + (208446987/400000000 : ℝ)*x 1 + (-1632529/8000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677396651/5000000000 : ℝ)^4449 ≤ (11106640908871/25000000000000 : ℝ)^3425 := by
    have hnat : (2677396651 : ℕ)^4449*25000000000000^3425 ≤ 11106640908871^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677396651 5000000000 11106640908871 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208446987/400000000 : ℝ)^4449 ≤ (21442508309927/50000000000000 : ℝ)^3425 := by
    have hnat : (208446987 : ℕ)^4449*50000000000000^3425 ≤ 21442508309927^3425*400000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208446987 400000000 21442508309927 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1632529/8000000 : ℝ)^4449 ≤ (12688419733229/100000000000000 : ℝ)^3425 := by
    have hnat : (1632529 : ℕ)^4449*100000000000000^3425 ≤ 12688419733229^3425*8000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1632529 8000000 12688419733229 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677396651/5000000000 : ℝ), (208446987/400000000 : ℝ), (-1632529/8000000 : ℝ)] ![(11106640908871/25000000000000 : ℝ), (21442508309927/50000000000000 : ℝ), (12688419733229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677396651/5000000000 : ℝ)|^4449 ≤ (11106640908871/25000000000000 : ℝ)^3425
        have hw : |(2677396651/5000000000 : ℝ)|=(2677396651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208446987/400000000 : ℝ)|^4449 ≤ (21442508309927/50000000000000 : ℝ)^3425
        have hw : |(208446987/400000000 : ℝ)|=(208446987/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1632529/8000000 : ℝ)|^4449 ≤ (12688419733229/100000000000000 : ℝ)^3425
        have hw : |(-1632529/8000000 : ℝ)|=(1632529/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s3_3 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (857272751/2000000000 : ℝ)*x 0 + (807398683/2000000000 : ℝ)*x 1 + (2274558649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (857272751/2000000000 : ℝ)^4449 ≤ (8318244991833/25000000000000 : ℝ)^3425 := by
    have hnat : (857272751 : ℕ)^4449*25000000000000^3425 ≤ 8318244991833^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857272751 2000000000 8318244991833 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (807398683/2000000000 : ℝ)^4449 ≤ (3847583332597/12500000000000 : ℝ)^3425 := by
    have hnat : (807398683 : ℕ)^4449*12500000000000^3425 ≤ 3847583332597^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807398683 2000000000 3847583332597 12500000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2274558649/5000000000 : ℝ)^4449 ≤ (3594635336207/10000000000000 : ℝ)^3425 := by
    have hnat : (2274558649 : ℕ)^4449*10000000000000^3425 ≤ 3594635336207^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274558649 5000000000 3594635336207 10000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(857272751/2000000000 : ℝ), (807398683/2000000000 : ℝ), (2274558649/5000000000 : ℝ)] ![(8318244991833/25000000000000 : ℝ), (3847583332597/12500000000000 : ℝ), (3594635336207/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(857272751/2000000000 : ℝ)|^4449 ≤ (8318244991833/25000000000000 : ℝ)^3425
        have hw : |(857272751/2000000000 : ℝ)|=(857272751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(807398683/2000000000 : ℝ)|^4449 ≤ (3847583332597/12500000000000 : ℝ)^3425
        have hw : |(807398683/2000000000 : ℝ)|=(807398683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2274558649/5000000000 : ℝ)|^4449 ≤ (3594635336207/10000000000000 : ℝ)^3425
        have hw : |(2274558649/5000000000 : ℝ)|=(2274558649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s3_4 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-192181267/1000000000 : ℝ)*x 0 + (5212408973/10000000000 : ℝ)*x 1 + (5441642709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (192181267/1000000000 : ℝ)^4449 ≤ (5868489695789/50000000000000 : ℝ)^3425 := by
    have hnat : (192181267 : ℕ)^4449*50000000000000^3425 ≤ 5868489695789^3425*1000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192181267 1000000000 5868489695789 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5212408973/10000000000 : ℝ)^4449 ≤ (1340569111021/3125000000000 : ℝ)^3425 := by
    have hnat : (5212408973 : ℕ)^4449*3125000000000^3425 ≤ 1340569111021^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212408973 10000000000 1340569111021 3125000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5441642709/10000000000 : ℝ)^4449 ≤ (45364809036289/100000000000000 : ℝ)^3425 := by
    have hnat : (5441642709 : ℕ)^4449*100000000000000^3425 ≤ 45364809036289^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441642709 10000000000 45364809036289 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-192181267/1000000000 : ℝ), (5212408973/10000000000 : ℝ), (5441642709/10000000000 : ℝ)] ![(5868489695789/50000000000000 : ℝ), (1340569111021/3125000000000 : ℝ), (45364809036289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-192181267/1000000000 : ℝ)|^4449 ≤ (5868489695789/50000000000000 : ℝ)^3425
        have hw : |(-192181267/1000000000 : ℝ)|=(192181267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5212408973/10000000000 : ℝ)|^4449 ≤ (1340569111021/3125000000000 : ℝ)^3425
        have hw : |(5212408973/10000000000 : ℝ)|=(5212408973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5441642709/10000000000 : ℝ)|^4449 ≤ (45364809036289/100000000000000 : ℝ)^3425
        have hw : |(5441642709/10000000000 : ℝ)|=(5441642709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s3_5 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294317109/10000000000 : ℝ)*x 0 + (-905096849/5000000000 : ℝ)*x 1 + (5441642743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294317109/10000000000 : ℝ)^4449 ≤ (21887954524329/50000000000000 : ℝ)^3425 := by
    have hnat : (5294317109 : ℕ)^4449*50000000000000^3425 ≤ 21887954524329^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294317109 10000000000 21887954524329 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (905096849/5000000000 : ℝ)^4449 ≤ (2171856305289/20000000000000 : ℝ)^3425 := by
    have hnat : (905096849 : ℕ)^4449*20000000000000^3425 ≤ 2171856305289^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905096849 5000000000 2171856305289 20000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5441642743/10000000000 : ℝ)^4449 ≤ (45364809404477/100000000000000 : ℝ)^3425 := by
    have hnat : (5441642743 : ℕ)^4449*100000000000000^3425 ≤ 45364809404477^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441642743 10000000000 45364809404477 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294317109/10000000000 : ℝ), (-905096849/5000000000 : ℝ), (5441642743/10000000000 : ℝ)] ![(21887954524329/50000000000000 : ℝ), (2171856305289/20000000000000 : ℝ), (45364809404477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294317109/10000000000 : ℝ)|^4449 ≤ (21887954524329/50000000000000 : ℝ)^3425
        have hw : |(5294317109/10000000000 : ℝ)|=(5294317109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-905096849/5000000000 : ℝ)|^4449 ≤ (2171856305289/20000000000000 : ℝ)^3425
        have hw : |(-905096849/5000000000 : ℝ)|=(905096849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5441642743/10000000000 : ℝ)|^4449 ≤ (45364809404477/100000000000000 : ℝ)^3425
        have hw : |(5441642743/10000000000 : ℝ)|=(5441642743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s3_6 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058863427/2000000000 : ℝ)*x 0 + (2720821379/5000000000 : ℝ)*x 1 + (-905096821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058863427/2000000000 : ℝ)^4449 ≤ (43775909327913/100000000000000 : ℝ)^3425 := by
    have hnat : (1058863427 : ℕ)^4449*100000000000000^3425 ≤ 43775909327913^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058863427 2000000000 43775909327913 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720821379/5000000000 : ℝ)^4449 ≤ (45364809566913/100000000000000 : ℝ)^3425 := by
    have hnat : (2720821379 : ℕ)^4449*100000000000000^3425 ≤ 45364809566913^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720821379 5000000000 45364809566913 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (905096821/5000000000 : ℝ)^4449 ≤ (678705068129/6250000000000 : ℝ)^3425 := by
    have hnat : (905096821 : ℕ)^4449*6250000000000^3425 ≤ 678705068129^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905096821 5000000000 678705068129 6250000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058863427/2000000000 : ℝ), (2720821379/5000000000 : ℝ), (-905096821/5000000000 : ℝ)] ![(43775909327913/100000000000000 : ℝ), (45364809566913/100000000000000 : ℝ), (678705068129/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058863427/2000000000 : ℝ)|^4449 ≤ (43775909327913/100000000000000 : ℝ)^3425
        have hw : |(1058863427/2000000000 : ℝ)|=(1058863427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720821379/5000000000 : ℝ)|^4449 ≤ (45364809566913/100000000000000 : ℝ)^3425
        have hw : |(2720821379/5000000000 : ℝ)|=(2720821379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-905096821/5000000000 : ℝ)|^4449 ≤ (678705068129/6250000000000 : ℝ)^3425
        have hw : |(-905096821/5000000000 : ℝ)|=(905096821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s3_7 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2143220017/5000000000 : ℝ)*x 0 + (4546390251/10000000000 : ℝ)*x 1 + (4039741407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143220017/5000000000 : ℝ)^4449 ≤ (6654749823327/20000000000000 : ℝ)^3425 := by
    have hnat : (2143220017 : ℕ)^4449*20000000000000^3425 ≤ 6654749823327^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143220017 5000000000 6654749823327 20000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4546390251/10000000000 : ℝ)^4449 ≤ (35918364629599/100000000000000 : ℝ)^3425 := by
    have hnat : (4546390251 : ℕ)^4449*100000000000000^3425 ≤ 35918364629599^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4546390251 10000000000 35918364629599 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4039741407/10000000000 : ℝ)^4449 ≤ (30807886243187/100000000000000 : ℝ)^3425 := by
    have hnat : (4039741407 : ℕ)^4449*100000000000000^3425 ≤ 30807886243187^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4039741407 10000000000 30807886243187 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2143220017/5000000000 : ℝ), (4546390251/10000000000 : ℝ), (4039741407/10000000000 : ℝ)] ![(6654749823327/20000000000000 : ℝ), (35918364629599/100000000000000 : ℝ), (30807886243187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2143220017/5000000000 : ℝ)|^4449 ≤ (6654749823327/20000000000000 : ℝ)^3425
        have hw : |(2143220017/5000000000 : ℝ)|=(2143220017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4546390251/10000000000 : ℝ)|^4449 ≤ (35918364629599/100000000000000 : ℝ)^3425
        have hw : |(4546390251/10000000000 : ℝ)|=(4546390251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4039741407/10000000000 : ℝ)|^4449 ≤ (30807886243187/100000000000000 : ℝ)^3425
        have hw : |(4039741407/10000000000 : ℝ)|=(4039741407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1476_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (323/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10149/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5337/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15577/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (323/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10149/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (323/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10149/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (323/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10149/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (323/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10149/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (323/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10149/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (323/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10149/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10149/100000 : ℝ) ^ (4447/1024 : ℝ) ≤ (968615219188991/20000000000000000000 : ℝ) := by
    have hpowers : (10149/100000 : ℝ)^4447 ≤ (968615219188991/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10149 : ℕ)^4447*20000000000000000000^1024 ≤ 968615219188991^1024*100000^4447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10149 100000 968615219188991 20000000000000000000 4447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10149/100000 : ℝ)) (X := (968615219188991/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (323/2000 : ℝ) ^ (4447/1024 : ℝ) ≤ (18207180012810643/50000000000000000000 : ℝ) := by
    have hpowers : (323/2000 : ℝ)^4447 ≤ (18207180012810643/50000000000000000000 : ℝ)^1024 := by
      have hnat : (323 : ℕ)^4447*50000000000000000000^1024 ≤ 18207180012810643^1024*2000^4447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        323 2000 18207180012810643 50000000000000000000 4447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (323/2000 : ℝ)) (X := (18207180012810643/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000968615219188991/10000000000000000000 : ℝ) ≤ (5000111516191951/5000000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (10000968615219188991/10000000000000000000 : ℝ)^1024 ≤ (5000111516191951/5000000000000000 : ℝ)^4447 := by
      have hnat : (10000968615219188991 : ℕ)^1024*5000000000000000^4447 ≤ 5000111516191951^4447*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000968615219188991 10000000000000000000 5000111516191951 5000000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000111516191951/5000000000000000 : ℝ)) (X := (10000968615219188991/10000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041257436121566241/100000000000000000000 : ℝ) ≤ (10000949874249923/10000000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (100041257436121566241/100000000000000000000 : ℝ)^1024 ≤ (10000949874249923/10000000000000000 : ℝ)^4447 := by
      have hnat : (100041257436121566241 : ℕ)^1024*10000000000000000^4447 ≤ 10000949874249923^4447*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041257436121566241 100000000000000000000 10000949874249923 10000000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000949874249923/10000000000000000 : ℝ)) (X := (100041257436121566241/100000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018207180012810643/25000000000000000000 : ℝ) ≤ (1250209589514493/1250000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (25018207180012810643/25000000000000000000 : ℝ)^1024 ≤ (1250209589514493/1250000000000000 : ℝ)^4447 := by
      have hnat : (25018207180012810643 : ℕ)^1024*1250000000000000^4447 ≤ 1250209589514493^4447*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018207180012810643 25000000000000000000 1250209589514493 1250000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250209589514493/1250000000000000 : ℝ)) (X := (25018207180012810643/25000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(968615219188991/20000000000000000000 : ℝ) ≤ ((882302720310872083/882500000000000000 : ℝ)+2*(726841866021/600100000000000 : ℝ)*(10149/100000 : ℝ))^(4447/1024 : ℝ) := by
    rw [show (882302720310872083/882500000000000000 : ℝ)+2*(726841866021/600100000000000 : ℝ)*(10149/100000 : ℝ)=(5000111516191951/5000000000000000 : ℝ) by norm_num, show 1+2*(968615219188991/20000000000000000000 : ℝ)=(10000968615219188991/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18207180012810643/50000000000000000000 : ℝ)+(968615219188991/20000000000000000000 : ℝ) ≤ ((882302720310872083/882500000000000000 : ℝ)+(726841866021/600100000000000 : ℝ)*((323/2000 : ℝ)+(10149/100000 : ℝ)))^(4447/1024 : ℝ) := by
    rw [show (882302720310872083/882500000000000000 : ℝ)+(726841866021/600100000000000 : ℝ)*((323/2000 : ℝ)+(10149/100000 : ℝ))=(10000949874249923/10000000000000000 : ℝ) by norm_num, show 1+(18207180012810643/50000000000000000000 : ℝ)+(968615219188991/20000000000000000000 : ℝ)=(100041257436121566241/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18207180012810643/50000000000000000000 : ℝ) ≤ ((882302720310872083/882500000000000000 : ℝ)+2*(726841866021/600100000000000 : ℝ)*(323/2000 : ℝ))^(4447/1024 : ℝ) := by
    rw [show (882302720310872083/882500000000000000 : ℝ)+2*(726841866021/600100000000000 : ℝ)*(323/2000 : ℝ)=(1250209589514493/1250000000000000 : ℝ) by norm_num, show 1+2*(18207180012810643/50000000000000000000 : ℝ)=(25018207180012810643/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (882302720310872083/882500000000000000 : ℝ)*(X 1 0+X 2 0)+(726841866021/600100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (10149/100000 : ℝ)) (hi := (323/2000 : ℝ)) (c := (882302720310872083/882500000000000000 : ℝ)) (alpha := (726841866021/600100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (882302720310872083/882500000000000000 : ℝ)*(X 0 1+X 2 1)+(726841866021/600100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (10149/100000 : ℝ)) (hi := (323/2000 : ℝ)) (c := (882302720310872083/882500000000000000 : ℝ)) (alpha := (726841866021/600100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (882302720310872083/882500000000000000 : ℝ)*(X 0 2+X 1 2)+(726841866021/600100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (10149/100000 : ℝ)) (hi := (323/2000 : ℝ)) (c := (882302720310872083/882500000000000000 : ℝ)) (alpha := (726841866021/600100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-240222273/1250000000 : ℝ)*X 0 0+(5442886247/10000000000 : ℝ)*X 0 1+(1042234967/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677396627/5000000000 : ℝ)*X 1 0+(-2040661113/10000000000 : ℝ)*X 1 1+(2605587413/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677396651/5000000000 : ℝ)*X 2 0+(208446987/400000000 : ℝ)*X 2 1+(-1632529/8000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((857272751/2000000000 : ℝ)*X 0 0+(807398683/2000000000 : ℝ)*X 0 1+(2274558649/5000000000 : ℝ)*X 0 2+(857272751/2000000000 : ℝ)*X 1 0+(807398683/2000000000 : ℝ)*X 1 1+(2274558649/5000000000 : ℝ)*X 1 2+(857272751/2000000000 : ℝ)*X 2 0+(807398683/2000000000 : ℝ)*X 2 1+(2274558649/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-192181267/1000000000 : ℝ)*X 0 0+(5212408973/10000000000 : ℝ)*X 0 1+(5441642709/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294317109/10000000000 : ℝ)*X 1 0+(-905096849/5000000000 : ℝ)*X 1 1+(5441642743/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058863427/2000000000 : ℝ)*X 2 0+(2720821379/5000000000 : ℝ)*X 2 1+(-905096821/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2143220017/5000000000 : ℝ)*X 0 0+(4546390251/10000000000 : ℝ)*X 0 1+(4039741407/10000000000 : ℝ)*X 0 2+(2143220017/5000000000 : ℝ)*X 1 0+(4546390251/10000000000 : ℝ)*X 1 1+(4039741407/10000000000 : ℝ)*X 1 2+(2143220017/5000000000 : ℝ)*X 2 0+(4546390251/10000000000 : ℝ)*X 2 1+(4039741407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27519054558826369395366537/4412500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1858732961/100000000000000 : ℝ)*(base19) + (177912351/10000000000000 : ℝ)*(base23) + (31672461/50000000000000 : ℝ)*(lower2) + (231169331/100000000000000 : ℝ)*(upper3) + (25761421/100000000000000 : ℝ)*(upper5) + (313422578394713/10000000000000 : ℝ)*(major0) + (313422578394713/10000000000000 : ℝ)*(major1) + (313422578394713/10000000000000 : ℝ)*(major2) + (4315745728983029/100000000000000 : ℝ)*(sp0) + (2157886146676073/50000000000000 : ℝ)*(sp1) + (2157886186480799/50000000000000 : ℝ)*(sp2) + (976331765179101/50000000000000 : ℝ)*(sp3) + (28423102079/100000000000000 : ℝ)*(sp4) + (3419390961/25000000000000 : ℝ)*(sp7) + (1952677207922047/100000000000000 : ℝ)*(f.failure) + (1078943538021277/25000000000000 : ℝ)*(f.sum) + (2194340232497/3000500000000000000000000000 : ℝ)*base66 + (2215530217617822957/150025000000000000000000000000000 : ℝ)*base68 + (18724262176527043/150025000000000000000000000000000 : ℝ)*base69 + (839767825967527043/150025000000000000000000000000000 : ℝ)*base71 + (82434481177/600100000000000000000000000 : ℝ)*base73 + (606626351057722957/150025000000000000000000000000000 : ℝ)*base76 + (724451860670272957/150025000000000000000000000000000 : ℝ)*base78 + (614774512458322957/150025000000000000000000000000000 : ℝ)*base80 + (23003047840371/3000500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2736263/250000000000000000000 : ℝ)*base89 + (2736263/250000000000000000000 : ℝ)*base91 + (2736263/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21955938999562618001601/3750625000000000000000000000 : ℝ) := by norm_num
    linear_combination (791715611/100000000000000 : ℝ)*(base19) + (9987891/1000000000000 : ℝ)*(base23) + (61709289/50000000000000 : ℝ)*(upper3) + (36355463/50000000000000 : ℝ)*(lower4) + (76331503/100000000000000 : ℝ)*(upper5) + (1584027876499557/50000000000000 : ℝ)*(major0) + (1584027876499557/50000000000000 : ℝ)*(major1) + (1584027876499557/50000000000000 : ℝ)*(major2) + (10947540993/100000000000000 : ℝ)*(sp1) + (237140749/1562500000000 : ℝ)*(sp2) + (872471488697373/20000000000000 : ℝ)*(sp4) + (4362345704230261/100000000000000 : ℝ)*(sp5) + (4362341267689829/100000000000000 : ℝ)*(sp6) + (246719233422497/12500000000000 : ℝ)*(sp7) + (246719233422497/12500000000000 : ℝ)*(f.failure) + (872471488697373/20000000000000 : ℝ)*(f.sum) + (11723109151597/3750625000000000000000000000 : ℝ)*base66 + (3596786357428642927/750125000000000000000000000000000 : ℝ)*base67 + (818225919191642927/750125000000000000000000000000000 : ℝ)*base69 + (638721118350607073/750125000000000000000000000000000 : ℝ)*base72 + (136454474967449/30005000000000000000000000000 : ℝ)*base73 + (2956231194165357073/750125000000000000000000000000000 : ℝ)*base76 + (2094614663840107073/750125000000000000000000000000000 : ℝ)*base78 + (10954245243486517927/750125000000000000000000000000000 : ℝ)*base79 + (39957801922581/7501250000000000000000000000 : ℝ)*base81 + (160687/31250000000000000000 : ℝ)*base90 + (160687/31250000000000000000 : ℝ)*base92 + (160687/31250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1476_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (323/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10149/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5337/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15577/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1476_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1476_s4_0 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-480609583/2500000000 : ℝ)*x 0 + (5438628747/10000000000 : ℝ)*x 1 + (162968663/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (480609583/2500000000 : ℝ)^4449 ≤ (11741943120229/100000000000000 : ℝ)^3425 := by
    have hnat : (480609583 : ℕ)^4449*100000000000000^3425 ≤ 11741943120229^3425*2500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480609583 2500000000 11741943120229 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438628747/10000000000 : ℝ)^4449 ≤ (362657386829/800000000000 : ℝ)^3425 := by
    have hnat : (5438628747 : ℕ)^4449*800000000000^3425 ≤ 362657386829^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438628747 10000000000 362657386829 800000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (162968663/312500000 : ℝ)^4449 ≤ (21462941752901/50000000000000 : ℝ)^3425 := by
    have hnat : (162968663 : ℕ)^4449*50000000000000^3425 ≤ 21462941752901^3425*312500000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162968663 312500000 21462941752901 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-480609583/2500000000 : ℝ), (5438628747/10000000000 : ℝ), (162968663/312500000 : ℝ)] ![(11741943120229/100000000000000 : ℝ), (362657386829/800000000000 : ℝ), (21462941752901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-480609583/2500000000 : ℝ)|^4449 ≤ (11741943120229/100000000000000 : ℝ)^3425
        have hw : |(-480609583/2500000000 : ℝ)|=(480609583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438628747/10000000000 : ℝ)|^4449 ≤ (362657386829/800000000000 : ℝ)^3425
        have hw : |(5438628747/10000000000 : ℝ)|=(5438628747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(162968663/312500000 : ℝ)|^4449 ≤ (21462941752901/50000000000000 : ℝ)^3425
        have hw : |(162968663/312500000 : ℝ)|=(162968663/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s4_1 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353688967/10000000000 : ℝ)*x 0 + (-2037075133/10000000000 : ℝ)*x 1 + (521499637/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353688967/10000000000 : ℝ)^4449 ≤ (44414662475667/100000000000000 : ℝ)^3425 := by
    have hnat : (5353688967 : ℕ)^4449*100000000000000^3425 ≤ 44414662475667^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353688967 10000000000 44414662475667 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2037075133/10000000000 : ℝ)^4449 ≤ (12659463054233/100000000000000 : ℝ)^3425 := by
    have hnat : (2037075133 : ℕ)^4449*100000000000000^3425 ≤ 12659463054233^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037075133 10000000000 12659463054233 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521499637/1000000000 : ℝ)^4449 ≤ (21462937230101/50000000000000 : ℝ)^3425 := by
    have hnat : (521499637 : ℕ)^4449*50000000000000^3425 ≤ 21462937230101^3425*1000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521499637 1000000000 21462937230101 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353688967/10000000000 : ℝ), (-2037075133/10000000000 : ℝ), (521499637/1000000000 : ℝ)] ![(44414662475667/100000000000000 : ℝ), (12659463054233/100000000000000 : ℝ), (21462937230101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353688967/10000000000 : ℝ)|^4449 ≤ (44414662475667/100000000000000 : ℝ)^3425
        have hw : |(5353688967/10000000000 : ℝ)|=(5353688967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2037075133/10000000000 : ℝ)|^4449 ≤ (12659463054233/100000000000000 : ℝ)^3425
        have hw : |(-2037075133/10000000000 : ℝ)|=(2037075133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521499637/1000000000 : ℝ)|^4449 ≤ (21462937230101/50000000000000 : ℝ)^3425
        have hw : |(521499637/1000000000 : ℝ)|=(521499637/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s4_2 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353688549/10000000000 : ℝ)*x 0 + (5214997093/10000000000 : ℝ)*x 1 + (-2037074733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353688549/10000000000 : ℝ)^4449 ≤ (22207328985559/50000000000000 : ℝ)^3425 := by
    have hnat : (5353688549 : ℕ)^4449*50000000000000^3425 ≤ 22207328985559^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353688549 10000000000 22207328985559 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214997093/10000000000 : ℝ)^4449 ≤ (42925882190661/100000000000000 : ℝ)^3425 := by
    have hnat : (5214997093 : ℕ)^4449*100000000000000^3425 ≤ 42925882190661^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214997093 10000000000 42925882190661 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2037074733/10000000000 : ℝ)^4449 ≤ (6329729912609/50000000000000 : ℝ)^3425 := by
    have hnat : (2037074733 : ℕ)^4449*50000000000000^3425 ≤ 6329729912609^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037074733 10000000000 6329729912609 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353688549/10000000000 : ℝ), (5214997093/10000000000 : ℝ), (-2037074733/10000000000 : ℝ)] ![(22207328985559/50000000000000 : ℝ), (42925882190661/100000000000000 : ℝ), (6329729912609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353688549/10000000000 : ℝ)|^4449 ≤ (22207328985559/50000000000000 : ℝ)^3425
        have hw : |(5353688549/10000000000 : ℝ)|=(5353688549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214997093/10000000000 : ℝ)|^4449 ≤ (42925882190661/100000000000000 : ℝ)^3425
        have hw : |(5214997093/10000000000 : ℝ)|=(5214997093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2037074733/10000000000 : ℝ)|^4449 ≤ (6329729912609/50000000000000 : ℝ)^3425
        have hw : |(-2037074733/10000000000 : ℝ)|=(2037074733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s4_3 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4286772777/10000000000 : ℝ)*x 0 + (4045873243/10000000000 : ℝ)*x 1 + (4540141673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4286772777/10000000000 : ℝ)^4449 ≤ (33277104334941/100000000000000 : ℝ)^3425 := by
    have hnat : (4286772777 : ℕ)^4449*100000000000000^3425 ≤ 33277104334941^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4286772777 10000000000 33277104334941 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4045873243/10000000000 : ℝ)^4449 ≤ (30868643645171/100000000000000 : ℝ)^3425 := by
    have hnat : (4045873243 : ℕ)^4449*100000000000000^3425 ≤ 30868643645171^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4045873243 10000000000 30868643645171 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4540141673/10000000000 : ℝ)^4449 ≤ (35854251998339/100000000000000 : ℝ)^3425 := by
    have hnat : (4540141673 : ℕ)^4449*100000000000000^3425 ≤ 35854251998339^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540141673 10000000000 35854251998339 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4286772777/10000000000 : ℝ), (4045873243/10000000000 : ℝ), (4540141673/10000000000 : ℝ)] ![(33277104334941/100000000000000 : ℝ), (30868643645171/100000000000000 : ℝ), (35854251998339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4286772777/10000000000 : ℝ)|^4449 ≤ (33277104334941/100000000000000 : ℝ)^3425
        have hw : |(4286772777/10000000000 : ℝ)|=(4286772777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4045873243/10000000000 : ℝ)|^4449 ≤ (30868643645171/100000000000000 : ℝ)^3425
        have hw : |(4045873243/10000000000 : ℝ)|=(4045873243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4540141673/10000000000 : ℝ)|^4449 ≤ (35854251998339/100000000000000 : ℝ)^3425
        have hw : |(4540141673/10000000000 : ℝ)|=(4540141673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s4_4 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1922469577/10000000000 : ℝ)*x 0 + (10432293/20000000 : ℝ)*x 1 + (5437470831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1922469577/10000000000 : ℝ)^4449 ≤ (366943469283/3125000000000 : ℝ)^3425 := by
    have hnat : (1922469577 : ℕ)^4449*3125000000000^3425 ≤ 366943469283^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922469577 10000000000 366943469283 3125000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10432293/20000000 : ℝ)^4449 ≤ (10734543070669/25000000000000 : ℝ)^3425 := by
    have hnat : (10432293 : ℕ)^4449*25000000000000^3425 ≤ 10734543070669^3425*20000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10432293 20000000 10734543070669 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437470831/10000000000 : ℝ)^4449 ≤ (5664954585473/12500000000000 : ℝ)^3425 := by
    have hnat : (5437470831 : ℕ)^4449*12500000000000^3425 ≤ 5664954585473^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437470831 10000000000 5664954585473 12500000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1922469577/10000000000 : ℝ), (10432293/20000000 : ℝ), (5437470831/10000000000 : ℝ)] ![(366943469283/3125000000000 : ℝ), (10734543070669/25000000000000 : ℝ), (5664954585473/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1922469577/10000000000 : ℝ)|^4449 ≤ (366943469283/3125000000000 : ℝ)^3425
        have hw : |(-1922469577/10000000000 : ℝ)|=(1922469577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10432293/20000000 : ℝ)|^4449 ≤ (10734543070669/25000000000000 : ℝ)^3425
        have hw : |(10432293/20000000 : ℝ)|=(10432293/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437470831/10000000000 : ℝ)|^4449 ≤ (5664954585473/12500000000000 : ℝ)^3425
        have hw : |(5437470831/10000000000 : ℝ)|=(5437470831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s4_5 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295324119/10000000000 : ℝ)*x 0 + (-181460101/1000000000 : ℝ)*x 1 + (339841927/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295324119/10000000000 : ℝ)^4449 ≤ (43786725210679/100000000000000 : ℝ)^3425 := by
    have hnat : (5295324119 : ℕ)^4449*100000000000000^3425 ≤ 43786725210679^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295324119 10000000000 43786725210679 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (181460101/1000000000 : ℝ)^4449 ≤ (10893638082133/100000000000000 : ℝ)^3425 := by
    have hnat : (181460101 : ℕ)^4449*100000000000000^3425 ≤ 10893638082133^3425*1000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181460101 1000000000 10893638082133 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339841927/625000000 : ℝ)^4449 ≤ (4531963669461/10000000000000 : ℝ)^3425 := by
    have hnat : (339841927 : ℕ)^4449*10000000000000^3425 ≤ 4531963669461^3425*625000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339841927 625000000 4531963669461 10000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295324119/10000000000 : ℝ), (-181460101/1000000000 : ℝ), (339841927/625000000 : ℝ)] ![(43786725210679/100000000000000 : ℝ), (10893638082133/100000000000000 : ℝ), (4531963669461/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295324119/10000000000 : ℝ)|^4449 ≤ (43786725210679/100000000000000 : ℝ)^3425
        have hw : |(5295324119/10000000000 : ℝ)|=(5295324119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-181460101/1000000000 : ℝ)|^4449 ≤ (10893638082133/100000000000000 : ℝ)^3425
        have hw : |(-181460101/1000000000 : ℝ)|=(181460101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339841927/625000000 : ℝ)|^4449 ≤ (4531963669461/10000000000000 : ℝ)^3425
        have hw : |(339841927/625000000 : ℝ)|=(339841927/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s4_6 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295324121/10000000000 : ℝ)*x 0 + (339841927/625000000 : ℝ)*x 1 + (-113412563/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295324121/10000000000 : ℝ)^4449 ≤ (43786725232161/100000000000000 : ℝ)^3425 := by
    have hnat : (5295324121 : ℕ)^4449*100000000000000^3425 ≤ 43786725232161^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295324121 10000000000 43786725232161 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339841927/625000000 : ℝ)^4449 ≤ (4531963669461/10000000000000 : ℝ)^3425 := by
    have hnat : (339841927 : ℕ)^4449*10000000000000^3425 ≤ 4531963669461^3425*625000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339841927 625000000 4531963669461 10000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113412563/625000000 : ℝ)^4449 ≤ (10893638066537/100000000000000 : ℝ)^3425 := by
    have hnat : (113412563 : ℕ)^4449*100000000000000^3425 ≤ 10893638066537^3425*625000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113412563 625000000 10893638066537 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295324121/10000000000 : ℝ), (339841927/625000000 : ℝ), (-113412563/625000000 : ℝ)] ![(43786725232161/100000000000000 : ℝ), (4531963669461/10000000000000 : ℝ), (10893638066537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295324121/10000000000 : ℝ)|^4449 ≤ (43786725232161/100000000000000 : ℝ)^3425
        have hw : |(5295324121/10000000000 : ℝ)|=(5295324121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339841927/625000000 : ℝ)|^4449 ≤ (4531963669461/10000000000000 : ℝ)^3425
        have hw : |(339841927/625000000 : ℝ)|=(339841927/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-113412563/625000000 : ℝ)|^4449 ≤ (10893638066537/100000000000000 : ℝ)^3425
        have hw : |(-113412563/625000000 : ℝ)|=(113412563/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s4_7 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4286842133/10000000000 : ℝ)*x 0 + (28360001/62500000 : ℝ)*x 1 + (4048432837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4286842133/10000000000 : ℝ)^4449 ≤ (33277803696863/100000000000000 : ℝ)^3425 := by
    have hnat : (4286842133 : ℕ)^4449*100000000000000^3425 ≤ 33277803696863^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4286842133 10000000000 33277803696863 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28360001/62500000 : ℝ)^4449 ≤ (17914091357929/50000000000000 : ℝ)^3425 := by
    have hnat : (28360001 : ℕ)^4449*50000000000000^3425 ≤ 17914091357929^3425*62500000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28360001 62500000 17914091357929 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4048432837/10000000000 : ℝ)^4449 ≤ (15447006787119/50000000000000 : ℝ)^3425 := by
    have hnat : (4048432837 : ℕ)^4449*50000000000000^3425 ≤ 15447006787119^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4048432837 10000000000 15447006787119 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4286842133/10000000000 : ℝ), (28360001/62500000 : ℝ), (4048432837/10000000000 : ℝ)] ![(33277803696863/100000000000000 : ℝ), (17914091357929/50000000000000 : ℝ), (15447006787119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4286842133/10000000000 : ℝ)|^4449 ≤ (33277803696863/100000000000000 : ℝ)^3425
        have hw : |(4286842133/10000000000 : ℝ)|=(4286842133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(28360001/62500000 : ℝ)|^4449 ≤ (17914091357929/50000000000000 : ℝ)^3425
        have hw : |(28360001/62500000 : ℝ)|=(28360001/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4048432837/10000000000 : ℝ)|^4449 ≤ (15447006787119/50000000000000 : ℝ)^3425
        have hw : |(4048432837/10000000000 : ℝ)|=(4048432837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1476_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15577/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5337/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2689/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15577/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5337/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15577/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5337/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15577/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5337/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15577/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5337/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15577/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5337/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15577/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5337/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5337/50000 : ℝ) ^ (4447/1024 : ℝ) ≤ (3014499192734067/50000000000000000000 : ℝ) := by
    have hpowers : (5337/50000 : ℝ)^4447 ≤ (3014499192734067/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5337 : ℕ)^4447*50000000000000000000^1024 ≤ 3014499192734067^1024*50000^4447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5337 50000 3014499192734067 50000000000000000000 4447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5337/50000 : ℝ)) (X := (3014499192734067/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15577/100000 : ℝ) ^ (4447/1024 : ℝ) ≤ (7781802268144297/25000000000000000000 : ℝ) := by
    have hpowers : (15577/100000 : ℝ)^4447 ≤ (7781802268144297/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15577 : ℕ)^4447*25000000000000000000^1024 ≤ 7781802268144297^1024*100000^4447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15577 100000 7781802268144297 25000000000000000000 4447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15577/100000 : ℝ)) (X := (7781802268144297/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003014499192734067/25000000000000000000 : ℝ) ≤ (5000138821854363/5000000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (25003014499192734067/25000000000000000000 : ℝ)^1024 ≤ (5000138821854363/5000000000000000 : ℝ)^4447 := by
      have hnat : (25003014499192734067 : ℕ)^1024*5000000000000000^4447 ≤ 5000138821854363^4447*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003014499192734067 25000000000000000000 5000138821854363 5000000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000138821854363/5000000000000000 : ℝ)) (X := (25003014499192734067/25000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018578103729022661/50000000000000000000 : ℝ) ≤ (9766460414779/9765625000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (50018578103729022661/50000000000000000000 : ℝ)^1024 ≤ (9766460414779/9765625000000 : ℝ)^4447 := by
      have hnat : (50018578103729022661 : ℕ)^1024*9765625000000^4447 ≤ 9766460414779^4447*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018578103729022661 50000000000000000000 9766460414779 9765625000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (9766460414779/9765625000000 : ℝ)) (X := (50018578103729022661/50000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507781802268144297/12500000000000000000 : ℝ) ≤ (5000716642879333/5000000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (12507781802268144297/12500000000000000000 : ℝ)^1024 ≤ (5000716642879333/5000000000000000 : ℝ)^4447 := by
      have hnat : (12507781802268144297 : ℕ)^1024*5000000000000000^4447 ≤ 5000716642879333^4447*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507781802268144297 12500000000000000000 5000716642879333 5000000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000716642879333/5000000000000000 : ℝ)) (X := (12507781802268144297/12500000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3014499192734067/50000000000000000000 : ℝ) ≤ ((24509512981931412009/24515000000000000000 : ℝ)+2*(57782102497/49030000000000 : ℝ)*(5337/50000 : ℝ))^(4447/1024 : ℝ) := by
    rw [show (24509512981931412009/24515000000000000000 : ℝ)+2*(57782102497/49030000000000 : ℝ)*(5337/50000 : ℝ)=(5000138821854363/5000000000000000 : ℝ) by norm_num, show 1+2*(3014499192734067/50000000000000000000 : ℝ)=(25003014499192734067/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7781802268144297/25000000000000000000 : ℝ)+(3014499192734067/50000000000000000000 : ℝ) ≤ ((24509512981931412009/24515000000000000000 : ℝ)+(57782102497/49030000000000 : ℝ)*((15577/100000 : ℝ)+(5337/50000 : ℝ)))^(4447/1024 : ℝ) := by
    rw [show (24509512981931412009/24515000000000000000 : ℝ)+(57782102497/49030000000000 : ℝ)*((15577/100000 : ℝ)+(5337/50000 : ℝ))=(9766460414779/9765625000000 : ℝ) by norm_num, show 1+(7781802268144297/25000000000000000000 : ℝ)+(3014499192734067/50000000000000000000 : ℝ)=(50018578103729022661/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7781802268144297/25000000000000000000 : ℝ) ≤ ((24509512981931412009/24515000000000000000 : ℝ)+2*(57782102497/49030000000000 : ℝ)*(15577/100000 : ℝ))^(4447/1024 : ℝ) := by
    rw [show (24509512981931412009/24515000000000000000 : ℝ)+2*(57782102497/49030000000000 : ℝ)*(15577/100000 : ℝ)=(5000716642879333/5000000000000000 : ℝ) by norm_num, show 1+2*(7781802268144297/25000000000000000000 : ℝ)=(12507781802268144297/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24509512981931412009/24515000000000000000 : ℝ)*(X 1 0+X 2 0)+(57782102497/49030000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (5337/50000 : ℝ)) (hi := (15577/100000 : ℝ)) (c := (24509512981931412009/24515000000000000000 : ℝ)) (alpha := (57782102497/49030000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24509512981931412009/24515000000000000000 : ℝ)*(X 0 1+X 2 1)+(57782102497/49030000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (5337/50000 : ℝ)) (hi := (15577/100000 : ℝ)) (c := (24509512981931412009/24515000000000000000 : ℝ)) (alpha := (57782102497/49030000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24509512981931412009/24515000000000000000 : ℝ)*(X 0 2+X 1 2)+(57782102497/49030000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (5337/50000 : ℝ)) (hi := (15577/100000 : ℝ)) (c := (24509512981931412009/24515000000000000000 : ℝ)) (alpha := (57782102497/49030000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-480609583/2500000000 : ℝ)*X 0 0+(5438628747/10000000000 : ℝ)*X 0 1+(162968663/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353688967/10000000000 : ℝ)*X 1 0+(-2037075133/10000000000 : ℝ)*X 1 1+(521499637/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353688549/10000000000 : ℝ)*X 2 0+(5214997093/10000000000 : ℝ)*X 2 1+(-2037074733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4286772777/10000000000 : ℝ)*X 0 0+(4045873243/10000000000 : ℝ)*X 0 1+(4540141673/10000000000 : ℝ)*X 0 2+(4286772777/10000000000 : ℝ)*X 1 0+(4045873243/10000000000 : ℝ)*X 1 1+(4540141673/10000000000 : ℝ)*X 1 2+(4286772777/10000000000 : ℝ)*X 2 0+(4045873243/10000000000 : ℝ)*X 2 1+(4540141673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1922469577/10000000000 : ℝ)*X 0 0+(10432293/20000000 : ℝ)*X 0 1+(5437470831/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295324119/10000000000 : ℝ)*X 1 0+(-181460101/1000000000 : ℝ)*X 1 1+(339841927/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295324121/10000000000 : ℝ)*X 2 0+(339841927/625000000 : ℝ)*X 2 1+(-113412563/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4286842133/10000000000 : ℝ)*X 0 0+(28360001/62500000 : ℝ)*X 0 1+(4048432837/10000000000 : ℝ)*X 0 2+(4286842133/10000000000 : ℝ)*X 1 0+(28360001/62500000 : ℝ)*X 1 1+(4048432837/10000000000 : ℝ)*X 1 2+(4286842133/10000000000 : ℝ)*X 2 0+(28360001/62500000 : ℝ)*X 2 1+(4048432837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (812765576870201202706826283/122575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (566422083/50000000000000 : ℝ)*(base19) + (16221229/2000000000000 : ℝ)*(base23) + (17876029/100000000000000 : ℝ)*(upper4) + (44439733/100000000000000 : ℝ)*(upper5) + (324743925509529/10000000000000 : ℝ)*(major0) + (324743925509529/10000000000000 : ℝ)*(major1) + (324743925509529/10000000000000 : ℝ)*(major2) + (2235827092861043/50000000000000 : ℝ)*(sp0) + (4471660413920629/100000000000000 : ℝ)*(sp1) + (1117916576854277/25000000000000 : ℝ)*(sp2) + (252900270422773/12500000000000 : ℝ)*(sp3) + (1616594559/12500000000000 : ℝ)*(sp4) + (5571713763/100000000000000 : ℝ)*(sp5) + (4503652227/50000000000000 : ℝ)*(sp7) + (2023211170686639/100000000000000 : ℝ)*(f.failure) + (2235833559239279/50000000000000 : ℝ)*(f.sum) + (2177343658149/2451500000000000000000000000 : ℝ)*base65 + (285125596741933761/245150000000000000000000000000000 : ℝ)*base67 + (111458717194666239/245150000000000000000000000000000 : ℝ)*base70 + (680212785147466239/245150000000000000000000000000000 : ℝ)*base72 + (148447454313/980600000000000000000000000 : ℝ)*base73 + (577831277515366239/245150000000000000000000000000000 : ℝ)*base76 + (104966811174733761/245150000000000000000000000000000 : ℝ)*base77 + (2634834676668366239/245150000000000000000000000000000 : ℝ)*base80 + (2062453590931/2451500000000000000000000000 : ℝ)*base81 + (1227831/250000000000000000000 : ℝ)*base89 + (1227831/250000000000000000000 : ℝ)*base91 + (1227831/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6384864777273137795181/2451500000000000000000000000 : ℝ) := by norm_num
    linear_combination (437554587/100000000000000 : ℝ)*(base19) + (477152877/100000000000000 : ℝ)*(base23) + (54829361/100000000000000 : ℝ)*(upper3) + (16760729/100000000000000 : ℝ)*(lower4) + (53852959/100000000000000 : ℝ)*(upper5) + (3281273028405981/100000000000000 : ℝ)*(major0) + (3281273028405981/100000000000000 : ℝ)*(major1) + (3281273028405981/100000000000000 : ℝ)*(major2) + (32645999/500000000000 : ℝ)*(sp1) + (7095378917/100000000000000 : ℝ)*(sp2) + (2259127884866127/50000000000000 : ℝ)*(sp4) + (4518248802977867/100000000000000 : ℝ)*(sp5) + (225912409860023/5000000000000 : ℝ)*(sp6) + (511072550065987/25000000000000 : ℝ)*(sp7) + (511072550065987/25000000000000 : ℝ)*(f.failure) + (2259127884866127/50000000000000 : ℝ)*(f.sum) + (73398070233/612875000000000000000000000 : ℝ)*base66 + (4191434972910674171/2451500000000000000000000000000000 : ℝ)*base68 + (7185729244284325829/2451500000000000000000000000000000 : ℝ)*base69 + (7274586445326174171/2451500000000000000000000000000000 : ℝ)*base72 + (1329095010571/1225750000000000000000000000 : ℝ)*base73 + (10240498605379325829/2451500000000000000000000000000000 : ℝ)*base75 + (3652093933806174171/2451500000000000000000000000000000 : ℝ)*base78 + (23862893634637825829/2451500000000000000000000000000000 : ℝ)*base79 + (6678531379709/4903000000000000000000000000 : ℝ)*base81 + (176477/62500000000000000000 : ℝ)*base90 + (176477/62500000000000000000 : ℝ)*base92 + (176477/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1476_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15577/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5337/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2689/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1476_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1476_s5_0 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-240316229/1250000000 : ℝ)*x 0 + (2719018021/5000000000 : ℝ)*x 1 + (2607764747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (240316229/1250000000 : ℝ)^4449 ≤ (2348533816339/20000000000000 : ℝ)^3425 := by
    have hnat : (240316229 : ℕ)^4449*20000000000000^3425 ≤ 2348533816339^3425*1250000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240316229 1250000000 2348533816339 20000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719018021/5000000000 : ℝ)^4449 ≤ (45325756081259/100000000000000 : ℝ)^3425 := by
    have hnat : (2719018021 : ℕ)^4449*100000000000000^3425 ≤ 45325756081259^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719018021 5000000000 45325756081259 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607764747/5000000000 : ℝ)^4449 ≤ (42931574814391/100000000000000 : ℝ)^3425 := by
    have hnat : (2607764747 : ℕ)^4449*100000000000000^3425 ≤ 42931574814391^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607764747 5000000000 42931574814391 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-240316229/1250000000 : ℝ), (2719018021/5000000000 : ℝ), (2607764747/5000000000 : ℝ)] ![(2348533816339/20000000000000 : ℝ), (45325756081259/100000000000000 : ℝ), (42931574814391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-240316229/1250000000 : ℝ)|^4449 ≤ (2348533816339/20000000000000 : ℝ)^3425
        have hw : |(-240316229/1250000000 : ℝ)|=(240316229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719018021/5000000000 : ℝ)|^4449 ≤ (45325756081259/100000000000000 : ℝ)^3425
        have hw : |(2719018021/5000000000 : ℝ)|=(2719018021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607764747/5000000000 : ℝ)|^4449 ≤ (42931574814391/100000000000000 : ℝ)^3425
        have hw : |(2607764747/5000000000 : ℝ)|=(2607764747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s5_1 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353534467/10000000000 : ℝ)*x 0 + (-1018287601/5000000000 : ℝ)*x 1 + (5215529509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353534467/10000000000 : ℝ)^4449 ≤ (888259950477/2000000000000 : ℝ)^3425 := by
    have hnat : (5353534467 : ℕ)^4449*2000000000000^3425 ≤ 888259950477^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353534467 10000000000 888259950477 2000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1018287601/5000000000 : ℝ)^4449 ≤ (6327713745291/50000000000000 : ℝ)^3425 := by
    have hnat : (1018287601 : ℕ)^4449*50000000000000^3425 ≤ 6327713745291^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018287601 5000000000 6327713745291 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215529509/10000000000 : ℝ)^4449 ≤ (42931574974779/100000000000000 : ℝ)^3425 := by
    have hnat : (5215529509 : ℕ)^4449*100000000000000^3425 ≤ 42931574974779^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215529509 10000000000 42931574974779 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353534467/10000000000 : ℝ), (-1018287601/5000000000 : ℝ), (5215529509/10000000000 : ℝ)] ![(888259950477/2000000000000 : ℝ), (6327713745291/50000000000000 : ℝ), (42931574974779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353534467/10000000000 : ℝ)|^4449 ≤ (888259950477/2000000000000 : ℝ)^3425
        have hw : |(5353534467/10000000000 : ℝ)|=(5353534467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1018287601/5000000000 : ℝ)|^4449 ≤ (6327713745291/50000000000000 : ℝ)^3425
        have hw : |(-1018287601/5000000000 : ℝ)|=(1018287601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215529509/10000000000 : ℝ)|^4449 ≤ (42931574974779/100000000000000 : ℝ)^3425
        have hw : |(5215529509/10000000000 : ℝ)|=(5215529509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s5_2 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070706891/2000000000 : ℝ)*x 0 + (65194119/125000000 : ℝ)*x 1 + (-1018287601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070706891/2000000000 : ℝ)^4449 ≤ (22206498697267/50000000000000 : ℝ)^3425 := by
    have hnat : (1070706891 : ℕ)^4449*50000000000000^3425 ≤ 22206498697267^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070706891 2000000000 22206498697267 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65194119/125000000 : ℝ)^4449 ≤ (42931575092397/100000000000000 : ℝ)^3425 := by
    have hnat : (65194119 : ℕ)^4449*100000000000000^3425 ≤ 42931575092397^3425*125000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65194119 125000000 42931575092397 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1018287601/5000000000 : ℝ)^4449 ≤ (6327713745291/50000000000000 : ℝ)^3425 := by
    have hnat : (1018287601 : ℕ)^4449*50000000000000^3425 ≤ 6327713745291^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018287601 5000000000 6327713745291 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070706891/2000000000 : ℝ), (65194119/125000000 : ℝ), (-1018287601/5000000000 : ℝ)] ![(22206498697267/50000000000000 : ℝ), (42931575092397/100000000000000 : ℝ), (6327713745291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070706891/2000000000 : ℝ)|^4449 ≤ (22206498697267/50000000000000 : ℝ)^3425
        have hw : |(1070706891/2000000000 : ℝ)|=(1070706891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65194119/125000000 : ℝ)|^4449 ≤ (42931575092397/100000000000000 : ℝ)^3425
        have hw : |(65194119/125000000 : ℝ)|=(65194119/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1018287601/5000000000 : ℝ)|^4449 ≤ (6327713745291/50000000000000 : ℝ)^3425
        have hw : |(-1018287601/5000000000 : ℝ)|=(1018287601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s5_3 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4286829413/10000000000 : ℝ)*x 0 + (505888809/1250000000 : ℝ)*x 1 + (181555623/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4286829413/10000000000 : ℝ)^4449 ≤ (2079854714533/6250000000000 : ℝ)^3425 := by
    have hnat : (4286829413 : ℕ)^4449*6250000000000^3425 ≤ 2079854714533^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4286829413 10000000000 2079854714533 6250000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505888809/1250000000 : ℝ)^4449 ≤ (15440453044731/50000000000000 : ℝ)^3425 := by
    have hnat : (505888809 : ℕ)^4449*50000000000000^3425 ≤ 15440453044731^3425*1250000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505888809 1250000000 15440453044731 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181555623/400000000 : ℝ)^4449 ≤ (35841418456537/100000000000000 : ℝ)^3425 := by
    have hnat : (181555623 : ℕ)^4449*100000000000000^3425 ≤ 35841418456537^3425*400000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181555623 400000000 35841418456537 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4286829413/10000000000 : ℝ), (505888809/1250000000 : ℝ), (181555623/400000000 : ℝ)] ![(2079854714533/6250000000000 : ℝ), (15440453044731/50000000000000 : ℝ), (35841418456537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4286829413/10000000000 : ℝ)|^4449 ≤ (2079854714533/6250000000000 : ℝ)^3425
        have hw : |(4286829413/10000000000 : ℝ)|=(4286829413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(505888809/1250000000 : ℝ)|^4449 ≤ (15440453044731/50000000000000 : ℝ)^3425
        have hw : |(505888809/1250000000 : ℝ)|=(505888809/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(181555623/400000000 : ℝ)|^4449 ≤ (35841418456537/100000000000000 : ℝ)^3425
        have hw : |(181555623/400000000 : ℝ)|=(181555623/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s5_4 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-384512083/2000000000 : ℝ)*x 0 + (5216667691/10000000000 : ℝ)*x 1 + (543688949/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (384512083/2000000000 : ℝ)^4449 ≤ (2935727932419/25000000000000 : ℝ)^3425 := by
    have hnat : (384512083 : ℕ)^4449*25000000000000^3425 ≤ 2935727932419^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384512083 2000000000 2935727932419 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216667691/10000000000 : ℝ)^4449 ≤ (5367968176303/12500000000000 : ℝ)^3425 := by
    have hnat : (5216667691 : ℕ)^4449*12500000000000^3425 ≤ 5367968176303^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216667691 10000000000 5367968176303 12500000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543688949/1000000000 : ℝ)^4449 ≤ (22656671424623/50000000000000 : ℝ)^3425 := by
    have hnat : (543688949 : ℕ)^4449*50000000000000^3425 ≤ 22656671424623^3425*1000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543688949 1000000000 22656671424623 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-384512083/2000000000 : ℝ), (5216667691/10000000000 : ℝ), (543688949/1000000000 : ℝ)] ![(2935727932419/25000000000000 : ℝ), (5367968176303/12500000000000 : ℝ), (22656671424623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-384512083/2000000000 : ℝ)|^4449 ≤ (2935727932419/25000000000000 : ℝ)^3425
        have hw : |(-384512083/2000000000 : ℝ)|=(384512083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216667691/10000000000 : ℝ)|^4449 ≤ (5367968176303/12500000000000 : ℝ)^3425
        have hw : |(5216667691/10000000000 : ℝ)|=(5216667691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543688949/1000000000 : ℝ)|^4449 ≤ (22656671424623/50000000000000 : ℝ)^3425
        have hw : |(543688949/1000000000 : ℝ)|=(543688949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s5_5 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42363713/80000000 : ℝ)*x 0 + (-226901903/1250000000 : ℝ)*x 1 + (543688949/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42363713/80000000 : ℝ)^4449 ≤ (5473528630677/12500000000000 : ℝ)^3425 := by
    have hnat : (42363713 : ℕ)^4449*12500000000000^3425 ≤ 5473528630677^3425*80000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42363713 80000000 5473528630677 12500000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226901903/1250000000 : ℝ)^4449 ≤ (10898428079873/100000000000000 : ℝ)^3425 := by
    have hnat : (226901903 : ℕ)^4449*100000000000000^3425 ≤ 10898428079873^3425*1250000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226901903 1250000000 10898428079873 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543688949/1000000000 : ℝ)^4449 ≤ (22656671424623/50000000000000 : ℝ)^3425 := by
    have hnat : (543688949 : ℕ)^4449*50000000000000^3425 ≤ 22656671424623^3425*1000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543688949 1000000000 22656671424623 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42363713/80000000 : ℝ), (-226901903/1250000000 : ℝ), (543688949/1000000000 : ℝ)] ![(5473528630677/12500000000000 : ℝ), (10898428079873/100000000000000 : ℝ), (22656671424623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42363713/80000000 : ℝ)|^4449 ≤ (5473528630677/12500000000000 : ℝ)^3425
        have hw : |(42363713/80000000 : ℝ)|=(42363713/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-226901903/1250000000 : ℝ)|^4449 ≤ (10898428079873/100000000000000 : ℝ)^3425
        have hw : |(-226901903/1250000000 : ℝ)|=(226901903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543688949/1000000000 : ℝ)|^4449 ≤ (22656671424623/50000000000000 : ℝ)^3425
        have hw : |(543688949/1000000000 : ℝ)|=(543688949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s5_6 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295464127/10000000000 : ℝ)*x 0 + (5436889489/10000000000 : ℝ)*x 1 + (-1815215223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295464127/10000000000 : ℝ)^4449 ≤ (21894114533449/50000000000000 : ℝ)^3425 := by
    have hnat : (5295464127 : ℕ)^4449*50000000000000^3425 ≤ 21894114533449^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295464127 10000000000 21894114533449 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436889489/10000000000 : ℝ)^4449 ≤ (2265667141921/5000000000000 : ℝ)^3425 := by
    have hnat : (5436889489 : ℕ)^4449*5000000000000^3425 ≤ 2265667141921^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436889489 10000000000 2265667141921 5000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1815215223/10000000000 : ℝ)^4449 ≤ (5449214036037/50000000000000 : ℝ)^3425 := by
    have hnat : (1815215223 : ℕ)^4449*50000000000000^3425 ≤ 5449214036037^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1815215223 10000000000 5449214036037 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295464127/10000000000 : ℝ), (5436889489/10000000000 : ℝ), (-1815215223/10000000000 : ℝ)] ![(21894114533449/50000000000000 : ℝ), (2265667141921/5000000000000 : ℝ), (5449214036037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295464127/10000000000 : ℝ)|^4449 ≤ (21894114533449/50000000000000 : ℝ)^3425
        have hw : |(5295464127/10000000000 : ℝ)|=(5295464127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436889489/10000000000 : ℝ)|^4449 ≤ (2265667141921/5000000000000 : ℝ)^3425
        have hw : |(5436889489/10000000000 : ℝ)|=(5436889489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1815215223/10000000000 : ℝ)|^4449 ≤ (5449214036037/50000000000000 : ℝ)^3425
        have hw : |(-1815215223/10000000000 : ℝ)|=(1815215223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s5_7 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071724261/2500000000 : ℝ)*x 0 + (1134093757/2500000000 : ℝ)*x 1 + (4049644507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071724261/2500000000 : ℝ)^4449 ≤ (33278357402799/100000000000000 : ℝ)^3425 := by
    have hnat : (1071724261 : ℕ)^4449*100000000000000^3425 ≤ 33278357402799^3425*2500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071724261 2500000000 33278357402799 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134093757/2500000000 : ℝ)^4449 ≤ (2238476101371/6250000000000 : ℝ)^3425 := by
    have hnat : (1134093757 : ℕ)^4449*6250000000000^3425 ≤ 2238476101371^3425*2500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134093757 2500000000 2238476101371 6250000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4049644507/10000000000 : ℝ)^4449 ≤ (30906024957049/100000000000000 : ℝ)^3425 := by
    have hnat : (4049644507 : ℕ)^4449*100000000000000^3425 ≤ 30906024957049^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4049644507 10000000000 30906024957049 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071724261/2500000000 : ℝ), (1134093757/2500000000 : ℝ), (4049644507/10000000000 : ℝ)] ![(33278357402799/100000000000000 : ℝ), (2238476101371/6250000000000 : ℝ), (30906024957049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071724261/2500000000 : ℝ)|^4449 ≤ (33278357402799/100000000000000 : ℝ)^3425
        have hw : |(1071724261/2500000000 : ℝ)|=(1071724261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1134093757/2500000000 : ℝ)|^4449 ≤ (2238476101371/6250000000000 : ℝ)^3425
        have hw : |(1134093757/2500000000 : ℝ)|=(1134093757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4049644507/10000000000 : ℝ)|^4449 ≤ (30906024957049/100000000000000 : ℝ)^3425
        have hw : |(4049644507/10000000000 : ℝ)|=(4049644507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1476_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2689/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10767/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3869/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2689/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2689/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2689/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2689/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2689/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2689/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2689/25000 : ℝ) ^ (4447/1024 : ℝ) ≤ (249309472227579/4000000000000000000 : ℝ) := by
    have hpowers : (2689/25000 : ℝ)^4447 ≤ (249309472227579/4000000000000000000 : ℝ)^1024 := by
      have hnat : (2689 : ℕ)^4447*4000000000000000000^1024 ≤ 249309472227579^1024*25000^4447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2689 25000 249309472227579 4000000000000000000 4447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2689/25000 : ℝ)) (X := (249309472227579/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4447/1024 : ℝ) ≤ (15181101448844759/50000000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4447 ≤ (15181101448844759/50000000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4447*50000000000000000000^1024 ≤ 15181101448844759^1024*3125^4447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 15181101448844759 50000000000000000000 4447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (15181101448844759/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000249309472227579/2000000000000000000 : ℝ) ≤ (312508969552953/312500000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (2000249309472227579/2000000000000000000 : ℝ)^1024 ≤ (312508969552953/312500000000000 : ℝ)^4447 := by
      have hnat : (2000249309472227579 : ℕ)^1024*312500000000000^4447 ≤ 312508969552953^4447*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000249309472227579 2000000000000000000 312508969552953 312500000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312508969552953/312500000000000 : ℝ)) (X := (2000249309472227579/2000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036594939703378993/100000000000000000000 : ℝ) ≤ (400033701768931/400000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (100036594939703378993/100000000000000000000 : ℝ)^1024 ≤ (400033701768931/400000000000000 : ℝ)^4447 := by
      have hnat : (100036594939703378993 : ℕ)^1024*400000000000000^4447 ≤ 400033701768931^4447*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036594939703378993 100000000000000000000 400033701768931 400000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400033701768931/400000000000000 : ℝ)) (X := (100036594939703378993/100000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015181101448844759/25000000000000000000 : ℝ) ≤ (5000699031376027/5000000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (25015181101448844759/25000000000000000000 : ℝ)^1024 ≤ (5000699031376027/5000000000000000 : ℝ)^4447 := by
      have hnat : (25015181101448844759 : ℕ)^1024*5000000000000000^4447 ≤ 5000699031376027^4447*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015181101448844759 25000000000000000000 5000699031376027 5000000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000699031376027/5000000000000000 : ℝ)) (X := (25015181101448844759/25000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(249309472227579/4000000000000000000 : ℝ) ≤ ((5913675986374407653/5915000000000000000 : ℝ)+2*(555518528779/473200000000000 : ℝ)*(2689/25000 : ℝ))^(4447/1024 : ℝ) := by
    rw [show (5913675986374407653/5915000000000000000 : ℝ)+2*(555518528779/473200000000000 : ℝ)*(2689/25000 : ℝ)=(312508969552953/312500000000000 : ℝ) by norm_num, show 1+2*(249309472227579/4000000000000000000 : ℝ)=(2000249309472227579/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15181101448844759/50000000000000000000 : ℝ)+(249309472227579/4000000000000000000 : ℝ) ≤ ((5913675986374407653/5915000000000000000 : ℝ)+(555518528779/473200000000000 : ℝ)*((484/3125 : ℝ)+(2689/25000 : ℝ)))^(4447/1024 : ℝ) := by
    rw [show (5913675986374407653/5915000000000000000 : ℝ)+(555518528779/473200000000000 : ℝ)*((484/3125 : ℝ)+(2689/25000 : ℝ))=(400033701768931/400000000000000 : ℝ) by norm_num, show 1+(15181101448844759/50000000000000000000 : ℝ)+(249309472227579/4000000000000000000 : ℝ)=(100036594939703378993/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15181101448844759/50000000000000000000 : ℝ) ≤ ((5913675986374407653/5915000000000000000 : ℝ)+2*(555518528779/473200000000000 : ℝ)*(484/3125 : ℝ))^(4447/1024 : ℝ) := by
    rw [show (5913675986374407653/5915000000000000000 : ℝ)+2*(555518528779/473200000000000 : ℝ)*(484/3125 : ℝ)=(5000699031376027/5000000000000000 : ℝ) by norm_num, show 1+2*(15181101448844759/50000000000000000000 : ℝ)=(25015181101448844759/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5913675986374407653/5915000000000000000 : ℝ)*(X 1 0+X 2 0)+(555518528779/473200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (2689/25000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (5913675986374407653/5915000000000000000 : ℝ)) (alpha := (555518528779/473200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5913675986374407653/5915000000000000000 : ℝ)*(X 0 1+X 2 1)+(555518528779/473200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (2689/25000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (5913675986374407653/5915000000000000000 : ℝ)) (alpha := (555518528779/473200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5913675986374407653/5915000000000000000 : ℝ)*(X 0 2+X 1 2)+(555518528779/473200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (2689/25000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (5913675986374407653/5915000000000000000 : ℝ)) (alpha := (555518528779/473200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-240316229/1250000000 : ℝ)*X 0 0+(2719018021/5000000000 : ℝ)*X 0 1+(2607764747/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353534467/10000000000 : ℝ)*X 1 0+(-1018287601/5000000000 : ℝ)*X 1 1+(5215529509/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070706891/2000000000 : ℝ)*X 2 0+(65194119/125000000 : ℝ)*X 2 1+(-1018287601/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4286829413/10000000000 : ℝ)*X 0 0+(505888809/1250000000 : ℝ)*X 0 1+(181555623/400000000 : ℝ)*X 0 2+(4286829413/10000000000 : ℝ)*X 1 0+(505888809/1250000000 : ℝ)*X 1 1+(181555623/400000000 : ℝ)*X 1 2+(4286829413/10000000000 : ℝ)*X 2 0+(505888809/1250000000 : ℝ)*X 2 1+(181555623/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-384512083/2000000000 : ℝ)*X 0 0+(5216667691/10000000000 : ℝ)*X 0 1+(543688949/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((42363713/80000000 : ℝ)*X 1 0+(-226901903/1250000000 : ℝ)*X 1 1+(543688949/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295464127/10000000000 : ℝ)*X 2 0+(5436889489/10000000000 : ℝ)*X 2 1+(-1815215223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1071724261/2500000000 : ℝ)*X 0 0+(1134093757/2500000000 : ℝ)*X 0 1+(4049644507/10000000000 : ℝ)*X 0 2+(1071724261/2500000000 : ℝ)*X 1 0+(1134093757/2500000000 : ℝ)*X 1 1+(4049644507/10000000000 : ℝ)*X 1 2+(1071724261/2500000000 : ℝ)*X 2 0+(1134093757/2500000000 : ℝ)*X 2 1+(4049644507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (377565501527797325263470549/36968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (921388911/50000000000000 : ℝ)*(base19) + (861759441/50000000000000 : ℝ)*(base23) + (58452517/100000000000000 : ℝ)*(lower2) + (255018629/100000000000000 : ℝ)*(upper3) + (43013171/25000000000000 : ℝ)*(upper5) + (407985223476413/12500000000000 : ℝ)*(major0) + (407985223476413/12500000000000 : ℝ)*(major1) + (407985223476413/12500000000000 : ℝ)*(major2) + (1123569866674511/25000000000000 : ℝ)*(sp0) + (2247153118846089/50000000000000 : ℝ)*(sp1) + (2247153178475559/50000000000000 : ℝ)*(sp2) + (2033441488832919/100000000000000 : ℝ)*(sp3) + (7153442989/25000000000000 : ℝ)*(sp4) + (13665883051/100000000000000 : ℝ)*(sp7) + (203345515471597/10000000000000 : ℝ)*(f.failure) + (449430808047/10000000000 : ℝ)*(f.sum) + (39521830695891/5915000000000000000000000000 : ℝ)*base66 + (914461588656276189/73937500000000000000000000000000 : ℝ)*base67 + (851955726862901189/73937500000000000000000000000000 : ℝ)*base69 + (191005829488088689/73937500000000000000000000000000 : ℝ)*base71 + (5025209569927/2957500000000000000000000000 : ℝ)*base73 + (1124768212615526189/73937500000000000000000000000000 : ℝ)*base75 + (227643963224838689/73937500000000000000000000000000 : ℝ)*base77 + (129539024617026189/73937500000000000000000000000000 : ℝ)*base79 + (3848647711591/1478750000000000000000000000 : ℝ)*base81 + (41787/25000000000000000000 : ℝ)*base90 + (41787/25000000000000000000 : ℝ)*base92 + (41787/25000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (929415547486485719678946489/147875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1047468511/100000000000000 : ℝ)*(base19) + (45591561/4000000000000 : ℝ)*(base23) + (6482293/5000000000000 : ℝ)*(upper3) + (10199663/25000000000000 : ℝ)*(lower4) + (129348101/100000000000000 : ℝ)*(upper5) + (1648850208091557/50000000000000 : ℝ)*(major0) + (1648850208091557/50000000000000 : ℝ)*(major1) + (1648850208091557/50000000000000 : ℝ)*(major2) + (245870433/1562500000000 : ℝ)*(sp1) + (8486172381/50000000000000 : ℝ)*(sp2) + (90817517482573/2000000000000 : ℝ)*(sp4) + (1135214772738107/25000000000000 : ℝ)*(sp5) + (4540857761994863/100000000000000 : ℝ)*(sp6) + (256815593591599/12500000000000 : ℝ)*(sp7) + (256815593591599/12500000000000 : ℝ)*(f.failure) + (90817517482573/2000000000000 : ℝ)*(f.sum) + (41390596650437/11830000000000000000000000000 : ℝ)*base66 + (6174218278962726779/295750000000000000000000000000000 : ℝ)*base68 + (3852845983311226779/295750000000000000000000000000000 : ℝ)*base70 + (5174008496527226779/295750000000000000000000000000000 : ℝ)*base72 + (23237690939497/11830000000000000000000000000 : ℝ)*base74 + (8799314013542226779/295750000000000000000000000000000 : ℝ)*base76 + (3131913691572476779/295750000000000000000000000000000 : ℝ)*base78 + (4078126264150476779/295750000000000000000000000000000 : ℝ)*base80 + (24607730335973/11830000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (338671/31250000000000000000 : ℝ)*base89 + (338671/31250000000000000000 : ℝ)*base91 + (338671/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1476_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2689/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10767/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1476_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1476_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (323/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10149/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10767/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1476_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1476_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1476_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (323/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10149/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10767/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1476_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
