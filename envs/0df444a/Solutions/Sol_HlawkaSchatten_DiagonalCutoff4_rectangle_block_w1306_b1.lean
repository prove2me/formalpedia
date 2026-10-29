-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1306_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:38:02.841158+00:00
-- url     : https://prove2.me/submissions/6408b28e-6346-46a0-adae-8136590540d7

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
theorem support_rectangle_w1306_s3_0 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2073316553/10000000000 : ℝ)*x 0 + (2716015797/5000000000 : ℝ)*x 1 + (522738821/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2073316553/10000000000 : ℝ)^2133 ≤ (12613378711853/100000000000000 : ℝ)^1621 := by
    have hnat : (2073316553 : ℕ)^2133*100000000000000^1621 ≤ 12613378711853^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073316553 10000000000 12613378711853 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716015797/5000000000 : ℝ)^2133 ≤ (44797002663057/100000000000000 : ℝ)^1621 := by
    have hnat : (2716015797 : ℕ)^2133*100000000000000^1621 ≤ 44797002663057^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716015797 5000000000 44797002663057 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522738821/1000000000 : ℝ)^2133 ≤ (1330925581483/3125000000000 : ℝ)^1621 := by
    have hnat : (522738821 : ℕ)^2133*3125000000000^1621 ≤ 1330925581483^1621*1000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522738821 1000000000 1330925581483 3125000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2073316553/10000000000 : ℝ), (2716015797/5000000000 : ℝ), (522738821/1000000000 : ℝ)] ![(12613378711853/100000000000000 : ℝ), (44797002663057/100000000000000 : ℝ), (1330925581483/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2073316553/10000000000 : ℝ)|^2133 ≤ (12613378711853/100000000000000 : ℝ)^1621
        have hw : |(-2073316553/10000000000 : ℝ)|=(2073316553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716015797/5000000000 : ℝ)|^2133 ≤ (44797002663057/100000000000000 : ℝ)^1621
        have hw : |(2716015797/5000000000 : ℝ)|=(2716015797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522738821/1000000000 : ℝ)|^2133 ≤ (1330925581483/3125000000000 : ℝ)^1621
        have hw : |(522738821/1000000000 : ℝ)|=(522738821/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s3_1 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1338503819/2500000000 : ℝ)*x 0 + (-2178006849/10000000000 : ℝ)*x 1 + (5227388153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338503819/2500000000 : ℝ)^2133 ≤ (43952325945487/100000000000000 : ℝ)^1621 := by
    have hnat : (1338503819 : ℕ)^2133*100000000000000^1621 ≤ 43952325945487^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338503819 2500000000 43952325945487 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2178006849/10000000000 : ℝ)^2133 ≤ (6729028024609/50000000000000 : ℝ)^1621 := by
    have hnat : (2178006849 : ℕ)^2133*50000000000000^1621 ≤ 6729028024609^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178006849 10000000000 6729028024609 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227388153/10000000000 : ℝ)^2133 ≤ (42589617996371/100000000000000 : ℝ)^1621 := by
    have hnat : (5227388153 : ℕ)^2133*100000000000000^1621 ≤ 42589617996371^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227388153 10000000000 42589617996371 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338503819/2500000000 : ℝ), (-2178006849/10000000000 : ℝ), (5227388153/10000000000 : ℝ)] ![(43952325945487/100000000000000 : ℝ), (6729028024609/50000000000000 : ℝ), (42589617996371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338503819/2500000000 : ℝ)|^2133 ≤ (43952325945487/100000000000000 : ℝ)^1621
        have hw : |(1338503819/2500000000 : ℝ)|=(1338503819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2178006849/10000000000 : ℝ)|^2133 ≤ (6729028024609/50000000000000 : ℝ)^1621
        have hw : |(-2178006849/10000000000 : ℝ)|=(2178006849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227388153/10000000000 : ℝ)|^2133 ≤ (42589617996371/100000000000000 : ℝ)^1621
        have hw : |(5227388153/10000000000 : ℝ)|=(5227388153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s3_2 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1070803039/2000000000 : ℝ)*x 0 + (1306847087/2500000000 : ℝ)*x 1 + (-1089003349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070803039/2000000000 : ℝ)^2133 ≤ (43952325070513/100000000000000 : ℝ)^1621 := by
    have hnat : (1070803039 : ℕ)^2133*100000000000000^1621 ≤ 43952325070513^1621*2000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070803039 2000000000 43952325070513 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1306847087/2500000000 : ℝ)^2133 ≤ (21294810043463/50000000000000 : ℝ)^1621 := by
    have hnat : (1306847087 : ℕ)^2133*50000000000000^1621 ≤ 21294810043463^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306847087 2500000000 21294810043463 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089003349/5000000000 : ℝ)^2133 ≤ (6729027410737/50000000000000 : ℝ)^1621 := by
    have hnat : (1089003349 : ℕ)^2133*50000000000000^1621 ≤ 6729027410737^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089003349 5000000000 6729027410737 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070803039/2000000000 : ℝ), (1306847087/2500000000 : ℝ), (-1089003349/5000000000 : ℝ)] ![(43952325070513/100000000000000 : ℝ), (21294810043463/50000000000000 : ℝ), (6729027410737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070803039/2000000000 : ℝ)|^2133 ≤ (43952325070513/100000000000000 : ℝ)^1621
        have hw : |(1070803039/2000000000 : ℝ)|=(1070803039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1306847087/2500000000 : ℝ)|^2133 ≤ (21294810043463/50000000000000 : ℝ)^1621
        have hw : |(1306847087/2500000000 : ℝ)|=(1306847087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1089003349/5000000000 : ℝ)|^2133 ≤ (6729027410737/50000000000000 : ℝ)^1621
        have hw : |(-1089003349/5000000000 : ℝ)|=(1089003349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s3_3 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1083703247/2500000000 : ℝ)*x 0 + (2064143239/5000000000 : ℝ)*x 1 + (4551127973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083703247/2500000000 : ℝ)^2133 ≤ (16644695674267/50000000000000 : ℝ)^1621 := by
    have hnat : (1083703247 : ℕ)^2133*50000000000000^1621 ≤ 16644695674267^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083703247 2500000000 16644695674267 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064143239/5000000000 : ℝ)^2133 ≤ (15609142179027/50000000000000 : ℝ)^1621 := by
    have hnat : (2064143239 : ℕ)^2133*50000000000000^1621 ≤ 15609142179027^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064143239 5000000000 15609142179027 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4551127973/10000000000 : ℝ)^2133 ≤ (17746162137189/50000000000000 : ℝ)^1621 := by
    have hnat : (4551127973 : ℕ)^2133*50000000000000^1621 ≤ 17746162137189^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4551127973 10000000000 17746162137189 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083703247/2500000000 : ℝ), (2064143239/5000000000 : ℝ), (4551127973/10000000000 : ℝ)] ![(16644695674267/50000000000000 : ℝ), (15609142179027/50000000000000 : ℝ), (17746162137189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083703247/2500000000 : ℝ)|^2133 ≤ (16644695674267/50000000000000 : ℝ)^1621
        have hw : |(1083703247/2500000000 : ℝ)|=(1083703247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2064143239/5000000000 : ℝ)|^2133 ≤ (15609142179027/50000000000000 : ℝ)^1621
        have hw : |(2064143239/5000000000 : ℝ)|=(2064143239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4551127973/10000000000 : ℝ)|^2133 ≤ (17746162137189/50000000000000 : ℝ)^1621
        have hw : |(4551127973/10000000000 : ℝ)|=(4551127973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s3_4 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-518334523/2500000000 : ℝ)*x 0 + (2614130413/5000000000 : ℝ)*x 1 + (1357788391/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518334523/2500000000 : ℝ)^2133 ≤ (3153387784181/25000000000000 : ℝ)^1621 := by
    have hnat : (518334523 : ℕ)^2133*25000000000000^1621 ≤ 3153387784181^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518334523 2500000000 3153387784181 25000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614130413/5000000000 : ℝ)^2133 ≤ (42598973988007/100000000000000 : ℝ)^1621 := by
    have hnat : (2614130413 : ℕ)^2133*100000000000000^1621 ≤ 42598973988007^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614130413 5000000000 42598973988007 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357788391/2500000000 : ℝ)^2133 ≤ (2239373742993/5000000000000 : ℝ)^1621 := by
    have hnat : (1357788391 : ℕ)^2133*5000000000000^1621 ≤ 2239373742993^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357788391 2500000000 2239373742993 5000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-518334523/2500000000 : ℝ), (2614130413/5000000000 : ℝ), (1357788391/2500000000 : ℝ)] ![(3153387784181/25000000000000 : ℝ), (42598973988007/100000000000000 : ℝ), (2239373742993/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-518334523/2500000000 : ℝ)|^2133 ≤ (3153387784181/25000000000000 : ℝ)^1621
        have hw : |(-518334523/2500000000 : ℝ)|=(518334523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614130413/5000000000 : ℝ)|^2133 ≤ (42598973988007/100000000000000 : ℝ)^1621
        have hw : |(2614130413/5000000000 : ℝ)|=(2614130413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357788391/2500000000 : ℝ)|^2133 ≤ (2239373742993/5000000000000 : ℝ)^1621
        have hw : |(1357788391/2500000000 : ℝ)|=(1357788391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s3_5 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2650763257/5000000000 : ℝ)*x 0 + (-987120667/5000000000 : ℝ)*x 1 + (5431153529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650763257/5000000000 : ℝ)^2133 ≤ (43386214424103/100000000000000 : ℝ)^1621 := by
    have hnat : (2650763257 : ℕ)^2133*100000000000000^1621 ≤ 43386214424103^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650763257 5000000000 43386214424103 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (987120667/5000000000 : ℝ)^2133 ≤ (5913155537809/50000000000000 : ℝ)^1621 := by
    have hnat : (987120667 : ℕ)^2133*50000000000000^1621 ≤ 5913155537809^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987120667 5000000000 5913155537809 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431153529/10000000000 : ℝ)^2133 ≤ (5598434310009/12500000000000 : ℝ)^1621 := by
    have hnat : (5431153529 : ℕ)^2133*12500000000000^1621 ≤ 5598434310009^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431153529 10000000000 5598434310009 12500000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650763257/5000000000 : ℝ), (-987120667/5000000000 : ℝ), (5431153529/10000000000 : ℝ)] ![(43386214424103/100000000000000 : ℝ), (5913155537809/50000000000000 : ℝ), (5598434310009/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650763257/5000000000 : ℝ)|^2133 ≤ (43386214424103/100000000000000 : ℝ)^1621
        have hw : |(2650763257/5000000000 : ℝ)|=(2650763257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-987120667/5000000000 : ℝ)|^2133 ≤ (5913155537809/50000000000000 : ℝ)^1621
        have hw : |(-987120667/5000000000 : ℝ)|=(987120667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431153529/10000000000 : ℝ)|^2133 ≤ (5598434310009/12500000000000 : ℝ)^1621
        have hw : |(5431153529/10000000000 : ℝ)|=(5431153529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s3_6 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5301526629/10000000000 : ℝ)*x 0 + (5431153413/10000000000 : ℝ)*x 1 + (-1974241337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301526629/10000000000 : ℝ)^2133 ≤ (43386215662491/100000000000000 : ℝ)^1621 := by
    have hnat : (5301526629 : ℕ)^2133*100000000000000^1621 ≤ 43386215662491^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301526629 10000000000 43386215662491 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431153413/10000000000 : ℝ)^2133 ≤ (44787473221349/100000000000000 : ℝ)^1621 := by
    have hnat : (5431153413 : ℕ)^2133*100000000000000^1621 ≤ 44787473221349^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431153413 10000000000 44787473221349 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1974241337/10000000000 : ℝ)^2133 ≤ (2365262219853/20000000000000 : ℝ)^1621 := by
    have hnat : (1974241337 : ℕ)^2133*20000000000000^1621 ≤ 2365262219853^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1974241337 10000000000 2365262219853 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301526629/10000000000 : ℝ), (5431153413/10000000000 : ℝ), (-1974241337/10000000000 : ℝ)] ![(43386215662491/100000000000000 : ℝ), (44787473221349/100000000000000 : ℝ), (2365262219853/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301526629/10000000000 : ℝ)|^2133 ≤ (43386215662491/100000000000000 : ℝ)^1621
        have hw : |(5301526629/10000000000 : ℝ)|=(5301526629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431153413/10000000000 : ℝ)|^2133 ≤ (44787473221349/100000000000000 : ℝ)^1621
        have hw : |(5431153413/10000000000 : ℝ)|=(5431153413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1974241337/10000000000 : ℝ)|^2133 ≤ (2365262219853/20000000000000 : ℝ)^1621
        have hw : |(-1974241337/10000000000 : ℝ)|=(1974241337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s3_7 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4334857663/10000000000 : ℝ)*x 0 + (4549324853/10000000000 : ℝ)*x 1 + (4130100387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334857663/10000000000 : ℝ)^2133 ≤ (4161230349679/12500000000000 : ℝ)^1621 := by
    have hnat : (4334857663 : ℕ)^2133*12500000000000^1621 ≤ 4161230349679^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334857663 10000000000 4161230349679 12500000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4549324853/10000000000 : ℝ)^2133 ≤ (4434227773589/12500000000000 : ℝ)^1621 := by
    have hnat : (4549324853 : ℕ)^2133*12500000000000^1621 ≤ 4434227773589^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4549324853 10000000000 4434227773589 12500000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4130100387/10000000000 : ℝ)^2133 ≤ (3904541875113/12500000000000 : ℝ)^1621 := by
    have hnat : (4130100387 : ℕ)^2133*12500000000000^1621 ≤ 3904541875113^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130100387 10000000000 3904541875113 12500000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334857663/10000000000 : ℝ), (4549324853/10000000000 : ℝ), (4130100387/10000000000 : ℝ)] ![(4161230349679/12500000000000 : ℝ), (4434227773589/12500000000000 : ℝ), (3904541875113/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334857663/10000000000 : ℝ)|^2133 ≤ (4161230349679/12500000000000 : ℝ)^1621
        have hw : |(4334857663/10000000000 : ℝ)|=(4334857663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4549324853/10000000000 : ℝ)|^2133 ≤ (4434227773589/12500000000000 : ℝ)^1621
        have hw : |(4549324853/10000000000 : ℝ)|=(4549324853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4130100387/10000000000 : ℝ)|^2133 ≤ (3904541875113/12500000000000 : ℝ)^1621
        have hw : |(4130100387/10000000000 : ℝ)|=(4130100387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1306_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8127/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4803/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10719/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1881/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8127/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4803/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8127/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4803/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8127/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4803/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8127/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4803/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8127/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4803/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8127/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4803/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4803/50000 : ℝ) ^ (4265/1024 : ℝ) ≤ (1446072674237729/25000000000000000000 : ℝ) := by
    have hpowers : (4803/50000 : ℝ)^4265 ≤ (1446072674237729/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4803 : ℕ)^4265*25000000000000000000^1024 ≤ 1446072674237729^1024*50000^4265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4803 50000 1446072674237729 25000000000000000000 4265 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4803/50000 : ℝ)) (X := (1446072674237729/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8127/50000 : ℝ) ^ (4265/1024 : ℝ) ≤ (51715251604005501/100000000000000000000 : ℝ) := by
    have hpowers : (8127/50000 : ℝ)^4265 ≤ (51715251604005501/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8127 : ℕ)^4265*100000000000000000000^1024 ≤ 51715251604005501^1024*50000^4265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8127 50000 51715251604005501 100000000000000000000 4265 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8127/50000 : ℝ)) (X := (51715251604005501/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501446072674237729/12500000000000000000 : ℝ) ≤ (10000277742243367/10000000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (12501446072674237729/12500000000000000000 : ℝ)^1024 ≤ (10000277742243367/10000000000000000 : ℝ)^4265 := by
      have hnat : (12501446072674237729 : ℕ)^1024*10000000000000000^4265 ≤ 10000277742243367^4265*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501446072674237729 12500000000000000000 10000277742243367 10000000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000277742243367/10000000000000000 : ℝ)) (X := (12501446072674237729/12500000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100057499542300956417/100000000000000000000 : ℝ) ≤ (5000690113389987/5000000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (100057499542300956417/100000000000000000000 : ℝ)^1024 ≤ (5000690113389987/5000000000000000 : ℝ)^4265 := by
      have hnat : (100057499542300956417 : ℕ)^1024*5000000000000000^4265 ≤ 5000690113389987^4265*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100057499542300956417 100000000000000000000 5000690113389987 5000000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000690113389987/5000000000000000 : ℝ)) (X := (100057499542300956417/100000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50051715251604005501/50000000000000000000 : ℝ) ≤ (10002482711316581/10000000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (50051715251604005501/50000000000000000000 : ℝ)^1024 ≤ (10002482711316581/10000000000000000 : ℝ)^4265 := by
      have hnat : (50051715251604005501 : ℕ)^1024*10000000000000000^4265 ≤ 10002482711316581^4265*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50051715251604005501 50000000000000000000 10002482711316581 10000000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002482711316581/10000000000000000 : ℝ)) (X := (50051715251604005501/50000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1446072674237729/25000000000000000000 : ℝ) ≤ ((5538388791459717511/5540000000000000000 : ℝ)+2*(1102484536607/664800000000000 : ℝ)*(4803/50000 : ℝ))^(4265/1024 : ℝ) := by
    rw [show (5538388791459717511/5540000000000000000 : ℝ)+2*(1102484536607/664800000000000 : ℝ)*(4803/50000 : ℝ)=(10000277742243367/10000000000000000 : ℝ) by norm_num, show 1+2*(1446072674237729/25000000000000000000 : ℝ)=(12501446072674237729/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(51715251604005501/100000000000000000000 : ℝ)+(1446072674237729/25000000000000000000 : ℝ) ≤ ((5538388791459717511/5540000000000000000 : ℝ)+(1102484536607/664800000000000 : ℝ)*((8127/50000 : ℝ)+(4803/50000 : ℝ)))^(4265/1024 : ℝ) := by
    rw [show (5538388791459717511/5540000000000000000 : ℝ)+(1102484536607/664800000000000 : ℝ)*((8127/50000 : ℝ)+(4803/50000 : ℝ))=(5000690113389987/5000000000000000 : ℝ) by norm_num, show 1+(51715251604005501/100000000000000000000 : ℝ)+(1446072674237729/25000000000000000000 : ℝ)=(100057499542300956417/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(51715251604005501/100000000000000000000 : ℝ) ≤ ((5538388791459717511/5540000000000000000 : ℝ)+2*(1102484536607/664800000000000 : ℝ)*(8127/50000 : ℝ))^(4265/1024 : ℝ) := by
    rw [show (5538388791459717511/5540000000000000000 : ℝ)+2*(1102484536607/664800000000000 : ℝ)*(8127/50000 : ℝ)=(10002482711316581/10000000000000000 : ℝ) by norm_num, show 1+2*(51715251604005501/100000000000000000000 : ℝ)=(50051715251604005501/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5538388791459717511/5540000000000000000 : ℝ)*(X 1 0+X 2 0)+(1102484536607/664800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (4803/50000 : ℝ)) (hi := (8127/50000 : ℝ)) (c := (5538388791459717511/5540000000000000000 : ℝ)) (alpha := (1102484536607/664800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5538388791459717511/5540000000000000000 : ℝ)*(X 0 1+X 2 1)+(1102484536607/664800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (4803/50000 : ℝ)) (hi := (8127/50000 : ℝ)) (c := (5538388791459717511/5540000000000000000 : ℝ)) (alpha := (1102484536607/664800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5538388791459717511/5540000000000000000 : ℝ)*(X 0 2+X 1 2)+(1102484536607/664800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (4803/50000 : ℝ)) (hi := (8127/50000 : ℝ)) (c := (5538388791459717511/5540000000000000000 : ℝ)) (alpha := (1102484536607/664800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2073316553/10000000000 : ℝ)*X 0 0+(2716015797/5000000000 : ℝ)*X 0 1+(522738821/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338503819/2500000000 : ℝ)*X 1 0+(-2178006849/10000000000 : ℝ)*X 1 1+(5227388153/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070803039/2000000000 : ℝ)*X 2 0+(1306847087/2500000000 : ℝ)*X 2 1+(-1089003349/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1083703247/2500000000 : ℝ)*X 0 0+(2064143239/5000000000 : ℝ)*X 0 1+(4551127973/10000000000 : ℝ)*X 0 2+(1083703247/2500000000 : ℝ)*X 1 0+(2064143239/5000000000 : ℝ)*X 1 1+(4551127973/10000000000 : ℝ)*X 1 2+(1083703247/2500000000 : ℝ)*X 2 0+(2064143239/5000000000 : ℝ)*X 2 1+(4551127973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-518334523/2500000000 : ℝ)*X 0 0+(2614130413/5000000000 : ℝ)*X 0 1+(1357788391/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2650763257/5000000000 : ℝ)*X 1 0+(-987120667/5000000000 : ℝ)*X 1 1+(5431153529/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301526629/10000000000 : ℝ)*X 2 0+(5431153413/10000000000 : ℝ)*X 2 1+(-1974241337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4334857663/10000000000 : ℝ)*X 0 0+(4549324853/10000000000 : ℝ)*X 0 1+(4130100387/10000000000 : ℝ)*X 0 2+(4334857663/10000000000 : ℝ)*X 1 0+(4549324853/10000000000 : ℝ)*X 1 1+(4130100387/10000000000 : ℝ)*X 1 2+(4334857663/10000000000 : ℝ)*X 2 0+(4549324853/10000000000 : ℝ)*X 2 1+(4130100387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30840588951428915581083/5540000000000000000000000000 : ℝ) := by norm_num
    linear_combination (182845001/20000000000000 : ℝ)*(base19) + (402829537/50000000000000 : ℝ)*(base23) + (9503631/25000000000000 : ℝ)*(upper3) + (9272529/50000000000000 : ℝ)*(upper4) + (153399123/100000000000000 : ℝ)*(upper5) + (1812887264530143/50000000000000 : ℝ)*(major0) + (1812887264530143/50000000000000 : ℝ)*(major1) + (1812887264530143/50000000000000 : ℝ)*(major2) + (4886563885155297/100000000000000 : ℝ)*(sp0) + (305411321965821/6250000000000 : ℝ)*(sp1) + (4886581260019067/100000000000000 : ℝ)*(sp2) + (59124008432377/2500000000000 : ℝ)*(sp3) + (4545130711/25000000000000 : ℝ)*(sp4) + (3234792119/50000000000000 : ℝ)*(sp7) + (1182483403439659/50000000000000 : ℝ)*(f.failure) + (4886582065678141/100000000000000 : ℝ)*(f.sum) + (5828906947033/5540000000000000000000000000 : ℝ)*base66 + (999900852400890927/277000000000000000000000000000000 : ℝ)*base68 + (461252121667109073/277000000000000000000000000000000 : ℝ)*base69 + (553477279858890927/277000000000000000000000000000000 : ℝ)*base72 + (22206015868333/5540000000000000000000000000 : ℝ)*base74 + (812977463773109073/277000000000000000000000000000000 : ℝ)*base75 + (1949046664608109073/277000000000000000000000000000000 : ℝ)*base77 + (88534497258890927/277000000000000000000000000000000 : ℝ)*base80 + (8037994328933/5540000000000000000000000000 : ℝ)*base82 + (8736763/5000000000000000000000 : ℝ)*base89 + (8736763/5000000000000000000000 : ℝ)*base91 + (8736763/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (361847820860753316095481201/138500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35730061/4000000000000 : ℝ)*(base19) + (50208823/5000000000000 : ℝ)*(base23) + (83709417/100000000000000 : ℝ)*(upper3) + (1183709/100000000000000 : ℝ)*(lower4) + (45728717/50000000000000 : ℝ)*(upper5) + (1828517694543597/50000000000000 : ℝ)*(major0) + (1828517694543597/50000000000000 : ℝ)*(major1) + (1828517694543597/50000000000000 : ℝ)*(major2) + (7536927999/50000000000000 : ℝ)*(sp1) + (7626808663/50000000000000 : ℝ)*(sp2) + (246435675543057/5000000000000 : ℝ)*(sp4) + (4928697543753617/100000000000000 : ℝ)*(sp5) + (4928697253067353/100000000000000 : ℝ)*(sp6) + (3727120594103/156250000000 : ℝ)*(sp7) + (3727120594103/156250000000 : ℝ)*(f.failure) + (246435675543057/5000000000000 : ℝ)*(f.sum) + (19203052991407/5540000000000000000000000000 : ℝ)*base66 + (1053913616188652067/277000000000000000000000000000000 : ℝ)*base67 + (717402384011347933/277000000000000000000000000000000 : ℝ)*base70 + (2575246244253347933/277000000000000000000000000000000 : ℝ)*base72 + (7195189386593/5540000000000000000000000000 : ℝ)*base73 + (614677800190347933/277000000000000000000000000000000 : ℝ)*base76 + (2257855495070347933/277000000000000000000000000000000 : ℝ)*base78 + (3834871293819652067/277000000000000000000000000000000 : ℝ)*base79 + (15443384310053/5540000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (116771/15625000000000000000 : ℝ)*base89 + (116771/15625000000000000000 : ℝ)*base91 + (116771/15625000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1306_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8127/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4803/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1881/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1306_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1306_s4_0 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1037547809/5000000000 : ℝ)*x 0 + (677232869/1250000000 : ℝ)*x 1 + (5240390129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037547809/5000000000 : ℝ)^2133 ≤ (6313811230461/50000000000000 : ℝ)^1621 := by
    have hnat : (1037547809 : ℕ)^2133*50000000000000^1621 ≤ 6313811230461^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037547809 5000000000 6313811230461 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677232869/1250000000 : ℝ)^2133 ≤ (44643313340979/100000000000000 : ℝ)^1621 := by
    have hnat : (677232869 : ℕ)^2133*100000000000000^1621 ≤ 44643313340979^1621*1250000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677232869 1250000000 44643313340979 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240390129/10000000000 : ℝ)^2133 ≤ (42729064188941/100000000000000 : ℝ)^1621 := by
    have hnat : (5240390129 : ℕ)^2133*100000000000000^1621 ≤ 42729064188941^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240390129 10000000000 42729064188941 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1037547809/5000000000 : ℝ), (677232869/1250000000 : ℝ), (5240390129/10000000000 : ℝ)] ![(6313811230461/50000000000000 : ℝ), (44643313340979/100000000000000 : ℝ), (42729064188941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1037547809/5000000000 : ℝ)|^2133 ≤ (6313811230461/50000000000000 : ℝ)^1621
        have hw : |(-1037547809/5000000000 : ℝ)|=(1037547809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677232869/1250000000 : ℝ)|^2133 ≤ (44643313340979/100000000000000 : ℝ)^1621
        have hw : |(677232869/1250000000 : ℝ)|=(677232869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240390129/10000000000 : ℝ)|^2133 ≤ (42729064188941/100000000000000 : ℝ)^1621
        have hw : |(5240390129/10000000000 : ℝ)|=(5240390129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s4_1 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2675212769/5000000000 : ℝ)*x 0 + (-216561391/1000000000 : ℝ)*x 1 + (5240390117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675212769/5000000000 : ℝ)^2133 ≤ (43913553173209/100000000000000 : ℝ)^1621 := by
    have hnat : (2675212769 : ℕ)^2133*100000000000000^1621 ≤ 43913553173209^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675212769 5000000000 43913553173209 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216561391/1000000000 : ℝ)^2133 ≤ (1335738275063/10000000000000 : ℝ)^1621 := by
    have hnat : (216561391 : ℕ)^2133*10000000000000^1621 ≤ 1335738275063^1621*1000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216561391 1000000000 1335738275063 10000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240390117/10000000000 : ℝ)^2133 ≤ (42729064060191/100000000000000 : ℝ)^1621 := by
    have hnat : (5240390117 : ℕ)^2133*100000000000000^1621 ≤ 42729064060191^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240390117 10000000000 42729064060191 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675212769/5000000000 : ℝ), (-216561391/1000000000 : ℝ), (5240390117/10000000000 : ℝ)] ![(43913553173209/100000000000000 : ℝ), (1335738275063/10000000000000 : ℝ), (42729064060191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675212769/5000000000 : ℝ)|^2133 ≤ (43913553173209/100000000000000 : ℝ)^1621
        have hw : |(2675212769/5000000000 : ℝ)|=(2675212769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-216561391/1000000000 : ℝ)|^2133 ≤ (1335738275063/10000000000000 : ℝ)^1621
        have hw : |(-216561391/1000000000 : ℝ)|=(216561391/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240390117/10000000000 : ℝ)|^2133 ≤ (42729064060191/100000000000000 : ℝ)^1621
        have hw : |(5240390117/10000000000 : ℝ)|=(5240390117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s4_2 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (107008511/200000000 : ℝ)*x 0 + (5240390111/10000000000 : ℝ)*x 1 + (-1082806951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107008511/200000000 : ℝ)^2133 ≤ (5489194162851/12500000000000 : ℝ)^1621 := by
    have hnat : (107008511 : ℕ)^2133*12500000000000^1621 ≤ 5489194162851^1621*200000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107008511 200000000 5489194162851 12500000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240390111/10000000000 : ℝ)^2133 ≤ (5341132999477/12500000000000 : ℝ)^1621 := by
    have hnat : (5240390111 : ℕ)^2133*12500000000000^1621 ≤ 5341132999477^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240390111 10000000000 5341132999477 12500000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082806951/5000000000 : ℝ)^2133 ≤ (13357382685701/100000000000000 : ℝ)^1621 := by
    have hnat : (1082806951 : ℕ)^2133*100000000000000^1621 ≤ 13357382685701^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082806951 5000000000 13357382685701 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107008511/200000000 : ℝ), (5240390111/10000000000 : ℝ), (-1082806951/5000000000 : ℝ)] ![(5489194162851/12500000000000 : ℝ), (5341132999477/12500000000000 : ℝ), (13357382685701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107008511/200000000 : ℝ)|^2133 ≤ (5489194162851/12500000000000 : ℝ)^1621
        have hw : |(107008511/200000000 : ℝ)|=(107008511/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240390111/10000000000 : ℝ)|^2133 ≤ (5341132999477/12500000000000 : ℝ)^1621
        have hw : |(5240390111/10000000000 : ℝ)|=(5240390111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1082806951/5000000000 : ℝ)|^2133 ≤ (13357382685701/100000000000000 : ℝ)^1621
        have hw : |(-1082806951/5000000000 : ℝ)|=(1082806951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s4_3 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4335890369/10000000000 : ℝ)*x 0 + (259763851/625000000 : ℝ)*x 1 + (4522922591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4335890369/10000000000 : ℝ)^2133 ≤ (16650139443309/50000000000000 : ℝ)^1621 := by
    have hnat : (4335890369 : ℕ)^2133*50000000000000^1621 ≤ 16650139443309^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335890369 10000000000 16650139443309 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259763851/625000000 : ℝ)^2133 ≤ (3937068864583/12500000000000 : ℝ)^1621 := by
    have hnat : (259763851 : ℕ)^2133*12500000000000^1621 ≤ 3937068864583^1621*625000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259763851 625000000 3937068864583 12500000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4522922591/10000000000 : ℝ)^2133 ≤ (35203170180933/100000000000000 : ℝ)^1621 := by
    have hnat : (4522922591 : ℕ)^2133*100000000000000^1621 ≤ 35203170180933^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522922591 10000000000 35203170180933 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4335890369/10000000000 : ℝ), (259763851/625000000 : ℝ), (4522922591/10000000000 : ℝ)] ![(16650139443309/50000000000000 : ℝ), (3937068864583/12500000000000 : ℝ), (35203170180933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4335890369/10000000000 : ℝ)|^2133 ≤ (16650139443309/50000000000000 : ℝ)^1621
        have hw : |(4335890369/10000000000 : ℝ)|=(4335890369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259763851/625000000 : ℝ)|^2133 ≤ (3937068864583/12500000000000 : ℝ)^1621
        have hw : |(259763851/625000000 : ℝ)|=(259763851/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4522922591/10000000000 : ℝ)|^2133 ≤ (35203170180933/100000000000000 : ℝ)^1621
        have hw : |(4522922591/10000000000 : ℝ)|=(4522922591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s4_4 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1037554817/5000000000 : ℝ)*x 0 + (5241047141/10000000000 : ℝ)*x 1 + (5417202439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037554817/5000000000 : ℝ)^2133 ≤ (6313867346353/50000000000000 : ℝ)^1621 := by
    have hnat : (1037554817 : ℕ)^2133*50000000000000^1621 ≤ 6313867346353^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037554817 5000000000 6313867346353 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241047141/10000000000 : ℝ)^2133 ≤ (21368056772951/50000000000000 : ℝ)^1621 := by
    have hnat : (5241047141 : ℕ)^2133*50000000000000^1621 ≤ 21368056772951^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241047141 10000000000 21368056772951 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417202439/10000000000 : ℝ)^2133 ≤ (44636151754299/100000000000000 : ℝ)^1621 := by
    have hnat : (5417202439 : ℕ)^2133*100000000000000^1621 ≤ 44636151754299^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417202439 10000000000 44636151754299 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1037554817/5000000000 : ℝ), (5241047141/10000000000 : ℝ), (5417202439/10000000000 : ℝ)] ![(6313867346353/50000000000000 : ℝ), (21368056772951/50000000000000 : ℝ), (44636151754299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1037554817/5000000000 : ℝ)|^2133 ≤ (6313867346353/50000000000000 : ℝ)^1621
        have hw : |(-1037554817/5000000000 : ℝ)|=(1037554817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241047141/10000000000 : ℝ)|^2133 ≤ (21368056772951/50000000000000 : ℝ)^1621
        have hw : |(5241047141/10000000000 : ℝ)|=(5241047141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417202439/10000000000 : ℝ)|^2133 ≤ (44636151754299/100000000000000 : ℝ)^1621
        have hw : |(5417202439/10000000000 : ℝ)|=(5417202439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s4_5 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5304908423/10000000000 : ℝ)*x 0 + (-994400731/5000000000 : ℝ)*x 1 + (2708601169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304908423/10000000000 : ℝ)^2133 ≤ (43422636468759/100000000000000 : ℝ)^1621 := by
    have hnat : (5304908423 : ℕ)^2133*100000000000000^1621 ≤ 43422636468759^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304908423 10000000000 43422636468759 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994400731/5000000000 : ℝ)^2133 ≤ (11941212862331/100000000000000 : ℝ)^1621 := by
    have hnat : (994400731 : ℕ)^2133*100000000000000^1621 ≤ 11941212862331^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994400731 5000000000 11941212862331 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708601169/5000000000 : ℝ)^2133 ≤ (44636150659231/100000000000000 : ℝ)^1621 := by
    have hnat : (2708601169 : ℕ)^2133*100000000000000^1621 ≤ 44636150659231^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708601169 5000000000 44636150659231 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304908423/10000000000 : ℝ), (-994400731/5000000000 : ℝ), (2708601169/5000000000 : ℝ)] ![(43422636468759/100000000000000 : ℝ), (11941212862331/100000000000000 : ℝ), (44636150659231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304908423/10000000000 : ℝ)|^2133 ≤ (43422636468759/100000000000000 : ℝ)^1621
        have hw : |(5304908423/10000000000 : ℝ)|=(5304908423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-994400731/5000000000 : ℝ)|^2133 ≤ (11941212862331/100000000000000 : ℝ)^1621
        have hw : |(-994400731/5000000000 : ℝ)|=(994400731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708601169/5000000000 : ℝ)|^2133 ≤ (44636150659231/100000000000000 : ℝ)^1621
        have hw : |(2708601169/5000000000 : ℝ)|=(2708601169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s4_6 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652454079/5000000000 : ℝ)*x 0 + (5417202637/10000000000 : ℝ)*x 1 + (-497200353/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652454079/5000000000 : ℝ)^2133 ≤ (43422633614509/100000000000000 : ℝ)^1621 := by
    have hnat : (2652454079 : ℕ)^2133*100000000000000^1621 ≤ 43422633614509^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652454079 5000000000 43422633614509 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417202637/10000000000 : ℝ)^2133 ≤ (8927230780213/20000000000000 : ℝ)^1621 := by
    have hnat : (5417202637 : ℕ)^2133*20000000000000^1621 ≤ 8927230780213^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417202637 10000000000 8927230780213 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497200353/2500000000 : ℝ)^2133 ≤ (373162889603/3125000000000 : ℝ)^1621 := by
    have hnat : (497200353 : ℕ)^2133*3125000000000^1621 ≤ 373162889603^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497200353 2500000000 373162889603 3125000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652454079/5000000000 : ℝ), (5417202637/10000000000 : ℝ), (-497200353/2500000000 : ℝ)] ![(43422633614509/100000000000000 : ℝ), (8927230780213/20000000000000 : ℝ), (373162889603/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652454079/5000000000 : ℝ)|^2133 ≤ (43422633614509/100000000000000 : ℝ)^1621
        have hw : |(2652454079/5000000000 : ℝ)|=(2652454079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417202637/10000000000 : ℝ)|^2133 ≤ (8927230780213/20000000000000 : ℝ)^1621
        have hw : |(5417202637/10000000000 : ℝ)|=(5417202637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-497200353/2500000000 : ℝ)|^2133 ≤ (373162889603/3125000000000 : ℝ)^1621
        have hw : |(-497200353/2500000000 : ℝ)|=(497200353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s4_7 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4335919267/10000000000 : ℝ)*x 0 + (4521565277/10000000000 : ℝ)*x 1 + (4157586243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4335919267/10000000000 : ℝ)^2133 ≤ (8325142732213/25000000000000 : ℝ)^1621 := by
    have hnat : (4335919267 : ℕ)^2133*25000000000000^1621 ≤ 8325142732213^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335919267 10000000000 8325142732213 25000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4521565277/10000000000 : ℝ)^2133 ≤ (35189269687887/100000000000000 : ℝ)^1621 := by
    have hnat : (4521565277 : ℕ)^2133*100000000000000^1621 ≤ 35189269687887^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521565277 10000000000 35189269687887 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4157586243/10000000000 : ℝ)^2133 ≤ (31510159365319/100000000000000 : ℝ)^1621 := by
    have hnat : (4157586243 : ℕ)^2133*100000000000000^1621 ≤ 31510159365319^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4157586243 10000000000 31510159365319 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4335919267/10000000000 : ℝ), (4521565277/10000000000 : ℝ), (4157586243/10000000000 : ℝ)] ![(8325142732213/25000000000000 : ℝ), (35189269687887/100000000000000 : ℝ), (31510159365319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4335919267/10000000000 : ℝ)|^2133 ≤ (8325142732213/25000000000000 : ℝ)^1621
        have hw : |(4335919267/10000000000 : ℝ)|=(4335919267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4521565277/10000000000 : ℝ)|^2133 ≤ (35189269687887/100000000000000 : ℝ)^1621
        have hw : |(4521565277/10000000000 : ℝ)|=(4521565277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4157586243/10000000000 : ℝ)|^2133 ≤ (31510159365319/100000000000000 : ℝ)^1621
        have hw : |(4157586243/10000000000 : ℝ)|=(4157586243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1306_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1881/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10997/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14753/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1881/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10719/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1881/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10719/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1881/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10719/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1881/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10719/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1881/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10719/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1881/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10719/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10719/100000 : ℝ) ^ (4265/1024 : ℝ) ≤ (9131763467455187/100000000000000000000 : ℝ) := by
    have hpowers : (10719/100000 : ℝ)^4265 ≤ (9131763467455187/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10719 : ℕ)^4265*100000000000000000000^1024 ≤ 9131763467455187^1024*100000^4265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10719 100000 9131763467455187 100000000000000000000 4265 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10719/100000 : ℝ)) (X := (9131763467455187/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1881/12500 : ℝ) ^ (4265/1024 : ℝ) ≤ (37511721859614369/100000000000000000000 : ℝ) := by
    have hpowers : (1881/12500 : ℝ)^4265 ≤ (37511721859614369/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1881 : ℕ)^4265*100000000000000000000^1024 ≤ 37511721859614369^1024*12500^4265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1881 12500 37511721859614369 100000000000000000000 4265 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1881/12500 : ℝ)) (X := (37511721859614369/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009131763467455187/50000000000000000000 : ℝ) ≤ (2000087693101739/2000000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (50009131763467455187/50000000000000000000 : ℝ)^1024 ≤ (2000087693101739/2000000000000000 : ℝ)^4265 := by
      have hnat : (50009131763467455187 : ℕ)^1024*2000000000000000^4265 ≤ 2000087693101739^4265*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009131763467455187 50000000000000000000 2000087693101739 2000000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000087693101739/2000000000000000 : ℝ)) (X := (50009131763467455187/50000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011660871331767389/25000000000000000000 : ℝ) ≤ (1000111968268659/1000000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (25011660871331767389/25000000000000000000 : ℝ)^1024 ≤ (1000111968268659/1000000000000000 : ℝ)^4265 := by
      have hnat : (25011660871331767389 : ℕ)^1024*1000000000000000^4265 ≤ 1000111968268659^4265*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011660871331767389 25000000000000000000 1000111968268659 1000000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000111968268659/1000000000000000 : ℝ)) (X := (25011660871331767389/25000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037511721859614369/50000000000000000000 : ℝ) ≤ (2000360179972897/2000000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (50037511721859614369/50000000000000000000 : ℝ)^1024 ≤ (2000360179972897/2000000000000000 : ℝ)^4265 := by
      have hnat : (50037511721859614369 : ℕ)^1024*2000000000000000^4265 ≤ 2000360179972897^4265*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037511721859614369 50000000000000000000 2000360179972897 2000000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000360179972897/2000000000000000 : ℝ)) (X := (50037511721859614369/50000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9131763467455187/100000000000000000000 : ℝ) ≤ ((961717648518387281/962000000000000000 : ℝ)+2*(136243435579/86580000000000 : ℝ)*(10719/100000 : ℝ))^(4265/1024 : ℝ) := by
    rw [show (961717648518387281/962000000000000000 : ℝ)+2*(136243435579/86580000000000 : ℝ)*(10719/100000 : ℝ)=(2000087693101739/2000000000000000 : ℝ) by norm_num, show 1+2*(9131763467455187/100000000000000000000 : ℝ)=(50009131763467455187/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37511721859614369/100000000000000000000 : ℝ)+(9131763467455187/100000000000000000000 : ℝ) ≤ ((961717648518387281/962000000000000000 : ℝ)+(136243435579/86580000000000 : ℝ)*((1881/12500 : ℝ)+(10719/100000 : ℝ)))^(4265/1024 : ℝ) := by
    rw [show (961717648518387281/962000000000000000 : ℝ)+(136243435579/86580000000000 : ℝ)*((1881/12500 : ℝ)+(10719/100000 : ℝ))=(1000111968268659/1000000000000000 : ℝ) by norm_num, show 1+(37511721859614369/100000000000000000000 : ℝ)+(9131763467455187/100000000000000000000 : ℝ)=(25011660871331767389/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37511721859614369/100000000000000000000 : ℝ) ≤ ((961717648518387281/962000000000000000 : ℝ)+2*(136243435579/86580000000000 : ℝ)*(1881/12500 : ℝ))^(4265/1024 : ℝ) := by
    rw [show (961717648518387281/962000000000000000 : ℝ)+2*(136243435579/86580000000000 : ℝ)*(1881/12500 : ℝ)=(2000360179972897/2000000000000000 : ℝ) by norm_num, show 1+2*(37511721859614369/100000000000000000000 : ℝ)=(50037511721859614369/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (961717648518387281/962000000000000000 : ℝ)*(X 1 0+X 2 0)+(136243435579/86580000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (10719/100000 : ℝ)) (hi := (1881/12500 : ℝ)) (c := (961717648518387281/962000000000000000 : ℝ)) (alpha := (136243435579/86580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (961717648518387281/962000000000000000 : ℝ)*(X 0 1+X 2 1)+(136243435579/86580000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (10719/100000 : ℝ)) (hi := (1881/12500 : ℝ)) (c := (961717648518387281/962000000000000000 : ℝ)) (alpha := (136243435579/86580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (961717648518387281/962000000000000000 : ℝ)*(X 0 2+X 1 2)+(136243435579/86580000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (10719/100000 : ℝ)) (hi := (1881/12500 : ℝ)) (c := (961717648518387281/962000000000000000 : ℝ)) (alpha := (136243435579/86580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1037547809/5000000000 : ℝ)*X 0 0+(677232869/1250000000 : ℝ)*X 0 1+(5240390129/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675212769/5000000000 : ℝ)*X 1 0+(-216561391/1000000000 : ℝ)*X 1 1+(5240390117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((107008511/200000000 : ℝ)*X 2 0+(5240390111/10000000000 : ℝ)*X 2 1+(-1082806951/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4335890369/10000000000 : ℝ)*X 0 0+(259763851/625000000 : ℝ)*X 0 1+(4522922591/10000000000 : ℝ)*X 0 2+(4335890369/10000000000 : ℝ)*X 1 0+(259763851/625000000 : ℝ)*X 1 1+(4522922591/10000000000 : ℝ)*X 1 2+(4335890369/10000000000 : ℝ)*X 2 0+(259763851/625000000 : ℝ)*X 2 1+(4522922591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1037554817/5000000000 : ℝ)*X 0 0+(5241047141/10000000000 : ℝ)*X 0 1+(5417202439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304908423/10000000000 : ℝ)*X 1 0+(-994400731/5000000000 : ℝ)*X 1 1+(2708601169/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652454079/5000000000 : ℝ)*X 2 0+(5417202637/10000000000 : ℝ)*X 2 1+(-497200353/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4335919267/10000000000 : ℝ)*X 0 0+(4521565277/10000000000 : ℝ)*X 0 1+(4157586243/10000000000 : ℝ)*X 0 2+(4335919267/10000000000 : ℝ)*X 1 0+(4521565277/10000000000 : ℝ)*X 1 1+(4157586243/10000000000 : ℝ)*X 1 2+(4335919267/10000000000 : ℝ)*X 2 0+(4521565277/10000000000 : ℝ)*X 2 1+(4157586243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (354268801636601720399690167/144300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29057383/6250000000000 : ℝ)*(base19) + (108906901/25000000000000 : ℝ)*(base23) + (1402081/6250000000000 : ℝ)*(lower2) + (58933631/100000000000000 : ℝ)*(upper3) + (39213339/100000000000000 : ℝ)*(upper5) + (4180854860087023/100000000000000 : ℝ)*(major0) + (4180854860087023/100000000000000 : ℝ)*(major1) + (4180854860087023/100000000000000 : ℝ)*(major2) + (2817337204576729/50000000000000 : ℝ)*(sp0) + (1408670685957141/25000000000000 : ℝ)*(sp1) + (352167673319943/6250000000000 : ℝ)*(sp2) + (1363510868056781/50000000000000 : ℝ)*(sp3) + (8799593233/100000000000000 : ℝ)*(sp4) + (4693477611/100000000000000 : ℝ)*(sp7) + (681756607397793/25000000000000 : ℝ)*(f.failure) + (5634683208746691/100000000000000 : ℝ)*(f.sum) + (5115574965013/541125000000000000000000000 : ℝ)*base66 + (2757267020752490167/865800000000000000000000000000000 : ℝ)*base67 + (1571690997671690167/865800000000000000000000000000000 : ℝ)*base69 + (6205346214893709833/865800000000000000000000000000000 : ℝ)*base72 + (476784023077/2164500000000000000000000000 : ℝ)*base74 + (4456866280258509833/865800000000000000000000000000000 : ℝ)*base76 + (6991865746988109833/865800000000000000000000000000000 : ℝ)*base78 + (5746667245001709833/865800000000000000000000000000000 : ℝ)*base80 + (11132788605157/2164500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (7531601/2500000000000000000000 : ℝ)*base89 + (7531601/2500000000000000000000 : ℝ)*base91 + (7531601/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (397350124529352623899264507/36075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2247075567/100000000000000 : ℝ)*(base19) + (1066919951/50000000000000 : ℝ)*(base23) + (52388217/20000000000000 : ℝ)*(upper3) + (8067597/12500000000000 : ℝ)*(lower4) + (163260691/100000000000000 : ℝ)*(upper5) + (2106053497201483/50000000000000 : ℝ)*(major0) + (2106053497201483/50000000000000 : ℝ)*(major1) + (2106053497201483/50000000000000 : ℝ)*(major2) + (10046144877/25000000000000 : ℝ)*(sp1) + (11464439901/25000000000000 : ℝ)*(sp2) + (11353605020389/200000000000 : ℝ)*(sp4) + (227070403141577/4000000000000 : ℝ)*(sp5) + (2838377259297497/50000000000000 : ℝ)*(sp6) + (343426388932443/12500000000000 : ℝ)*(sp7) + (343426388932443/12500000000000 : ℝ)*(f.failure) + (11353605020389/200000000000 : ℝ)*(f.sum) + (13863045827639/2164500000000000000000000000 : ℝ)*base66 + (397101604285660493/432900000000000000000000000000000 : ℝ)*base68 + (2005697616467260493/432900000000000000000000000000000 : ℝ)*base70 + (3913898147658760493/432900000000000000000000000000000 : ℝ)*base72 + (1568272450721/541125000000000000000000000 : ℝ)*base74 + (1354058694946660493/432900000000000000000000000000000 : ℝ)*base76 + (1820602103549539507/432900000000000000000000000000000 : ℝ)*base77 + (5102616691839460493/432900000000000000000000000000000 : ℝ)*base80 + (3339225745231/432900000000000000000000000 : ℝ)*base82 + (8876651/1250000000000000000000 : ℝ)*base89 + (8876651/1250000000000000000000 : ℝ)*base91 + (8876651/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1306_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1881/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10997/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1306_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1306_s5_0 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1037708503/5000000000 : ℝ)*x 0 + (676887251/1250000000 : ℝ)*x 1 + (1310736007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037708503/5000000000 : ℝ)^2133 ≤ (3157549001227/25000000000000 : ℝ)^1621 := by
    have hnat : (1037708503 : ℕ)^2133*25000000000000^1621 ≤ 3157549001227^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037708503 5000000000 3157549001227 25000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676887251/1250000000 : ℝ)^2133 ≤ (2230666819089/5000000000000 : ℝ)^1621 := by
    have hnat : (676887251 : ℕ)^2133*5000000000000^1621 ≤ 2230666819089^1621*1250000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676887251 1250000000 2230666819089 5000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310736007/2500000000 : ℝ)^2133 ≤ (42756467607297/100000000000000 : ℝ)^1621 := by
    have hnat : (1310736007 : ℕ)^2133*100000000000000^1621 ≤ 42756467607297^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310736007 2500000000 42756467607297 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1037708503/5000000000 : ℝ), (676887251/1250000000 : ℝ), (1310736007/2500000000 : ℝ)] ![(3157549001227/25000000000000 : ℝ), (2230666819089/5000000000000 : ℝ), (42756467607297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1037708503/5000000000 : ℝ)|^2133 ≤ (3157549001227/25000000000000 : ℝ)^1621
        have hw : |(-1037708503/5000000000 : ℝ)|=(1037708503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676887251/1250000000 : ℝ)|^2133 ≤ (2230666819089/5000000000000 : ℝ)^1621
        have hw : |(676887251/1250000000 : ℝ)|=(676887251/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310736007/2500000000 : ℝ)|^2133 ≤ (42756467607297/100000000000000 : ℝ)^1621
        have hw : |(1310736007/2500000000 : ℝ)|=(1310736007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s5_1 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674861913/5000000000 : ℝ)*x 0 + (-2163170761/10000000000 : ℝ)*x 1 + (524294403/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674861913/5000000000 : ℝ)^2133 ≤ (43905974939359/100000000000000 : ℝ)^1621 := by
    have hnat : (2674861913 : ℕ)^2133*100000000000000^1621 ≤ 43905974939359^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674861913 5000000000 43905974939359 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2163170761/10000000000 : ℝ)^2133 ≤ (1333755740673/10000000000000 : ℝ)^1621 := by
    have hnat : (2163170761 : ℕ)^2133*10000000000000^1621 ≤ 1333755740673^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163170761 10000000000 1333755740673 10000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524294403/1000000000 : ℝ)^2133 ≤ (21378233814379/50000000000000 : ℝ)^1621 := by
    have hnat : (524294403 : ℕ)^2133*50000000000000^1621 ≤ 21378233814379^1621*1000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524294403 1000000000 21378233814379 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674861913/5000000000 : ℝ), (-2163170761/10000000000 : ℝ), (524294403/1000000000 : ℝ)] ![(43905974939359/100000000000000 : ℝ), (1333755740673/10000000000000 : ℝ), (21378233814379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674861913/5000000000 : ℝ)|^2133 ≤ (43905974939359/100000000000000 : ℝ)^1621
        have hw : |(2674861913/5000000000 : ℝ)|=(2674861913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2163170761/10000000000 : ℝ)|^2133 ≤ (1333755740673/10000000000000 : ℝ)^1621
        have hw : |(-2163170761/10000000000 : ℝ)|=(2163170761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524294403/1000000000 : ℝ)|^2133 ≤ (21378233814379/50000000000000 : ℝ)^1621
        have hw : |(524294403/1000000000 : ℝ)|=(524294403/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s5_2 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674861909/5000000000 : ℝ)*x 0 + (1310736007/2500000000 : ℝ)*x 1 + (-270396347/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674861909/5000000000 : ℝ)^2133 ≤ (43905974852963/100000000000000 : ℝ)^1621 := by
    have hnat : (2674861909 : ℕ)^2133*100000000000000^1621 ≤ 43905974852963^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674861909 5000000000 43905974852963 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310736007/2500000000 : ℝ)^2133 ≤ (42756467607297/100000000000000 : ℝ)^1621 := by
    have hnat : (1310736007 : ℕ)^2133*100000000000000^1621 ≤ 42756467607297^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310736007 2500000000 42756467607297 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270396347/1250000000 : ℝ)^2133 ≤ (13337557528429/100000000000000 : ℝ)^1621 := by
    have hnat : (270396347 : ℕ)^2133*100000000000000^1621 ≤ 13337557528429^1621*1250000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270396347 1250000000 13337557528429 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674861909/5000000000 : ℝ), (1310736007/2500000000 : ℝ), (-270396347/1250000000 : ℝ)] ![(43905974852963/100000000000000 : ℝ), (42756467607297/100000000000000 : ℝ), (13337557528429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674861909/5000000000 : ℝ)|^2133 ≤ (43905974852963/100000000000000 : ℝ)^1621
        have hw : |(2674861909/5000000000 : ℝ)|=(2674861909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310736007/2500000000 : ℝ)|^2133 ≤ (42756467607297/100000000000000 : ℝ)^1621
        have hw : |(1310736007/2500000000 : ℝ)|=(1310736007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-270396347/1250000000 : ℝ)|^2133 ≤ (13337557528429/100000000000000 : ℝ)^1621
        have hw : |(-270396347/1250000000 : ℝ)|=(270396347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s5_3 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4336083317/10000000000 : ℝ)*x 0 + (166467697/400000000 : ℝ)*x 1 + (4517403389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4336083317/10000000000 : ℝ)^2133 ≤ (33302228824389/100000000000000 : ℝ)^1621 := by
    have hnat : (4336083317 : ℕ)^2133*100000000000000^1621 ≤ 33302228824389^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4336083317 10000000000 33302228824389 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166467697/400000000 : ℝ)^2133 ≤ (1577555794447/5000000000000 : ℝ)^1621 := by
    have hnat : (166467697 : ℕ)^2133*5000000000000^1621 ≤ 1577555794447^1621*400000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166467697 400000000 1577555794447 5000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4517403389/10000000000 : ℝ)^2133 ≤ (4393331909133/12500000000000 : ℝ)^1621 := by
    have hnat : (4517403389 : ℕ)^2133*12500000000000^1621 ≤ 4393331909133^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517403389 10000000000 4393331909133 12500000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4336083317/10000000000 : ℝ), (166467697/400000000 : ℝ), (4517403389/10000000000 : ℝ)] ![(33302228824389/100000000000000 : ℝ), (1577555794447/5000000000000 : ℝ), (4393331909133/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4336083317/10000000000 : ℝ)|^2133 ≤ (33302228824389/100000000000000 : ℝ)^1621
        have hw : |(4336083317/10000000000 : ℝ)|=(4336083317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(166467697/400000000 : ℝ)|^2133 ≤ (1577555794447/5000000000000 : ℝ)^1621
        have hw : |(166467697/400000000 : ℝ)|=(166467697/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4517403389/10000000000 : ℝ)|^2133 ≤ (4393331909133/12500000000000 : ℝ)^1621
        have hw : |(4517403389/10000000000 : ℝ)|=(4517403389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s5_4 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2075429743/10000000000 : ℝ)*x 0 + (1048712467/2000000000 : ℝ)*x 1 + (5414476547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2075429743/10000000000 : ℝ)^2133 ≤ (12630298000201/100000000000000 : ℝ)^1621 := by
    have hnat : (2075429743 : ℕ)^2133*100000000000000^1621 ≤ 12630298000201^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075429743 10000000000 12630298000201 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048712467/2000000000 : ℝ)^2133 ≤ (21381551347661/50000000000000 : ℝ)^1621 := by
    have hnat : (1048712467 : ℕ)^2133*50000000000000^1621 ≤ 21381551347661^1621*2000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048712467 2000000000 21381551347661 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414476547/10000000000 : ℝ)^2133 ≤ (22303299646813/50000000000000 : ℝ)^1621 := by
    have hnat : (5414476547 : ℕ)^2133*50000000000000^1621 ≤ 22303299646813^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414476547 10000000000 22303299646813 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2075429743/10000000000 : ℝ), (1048712467/2000000000 : ℝ), (5414476547/10000000000 : ℝ)] ![(12630298000201/100000000000000 : ℝ), (21381551347661/50000000000000 : ℝ), (22303299646813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2075429743/10000000000 : ℝ)|^2133 ≤ (12630298000201/100000000000000 : ℝ)^1621
        have hw : |(-2075429743/10000000000 : ℝ)|=(2075429743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048712467/2000000000 : ℝ)|^2133 ≤ (21381551347661/50000000000000 : ℝ)^1621
        have hw : |(1048712467/2000000000 : ℝ)|=(1048712467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414476547/10000000000 : ℝ)|^2133 ≤ (22303299646813/50000000000000 : ℝ)^1621
        have hw : |(5414476547/10000000000 : ℝ)|=(5414476547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s5_5 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (331598177/625000000 : ℝ)*x 0 + (-995819117/5000000000 : ℝ)*x 1 + (5414476461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331598177/625000000 : ℝ)^2133 ≤ (43429771254349/100000000000000 : ℝ)^1621 := by
    have hnat : (331598177 : ℕ)^2133*100000000000000^1621 ≤ 43429771254349^1621*625000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331598177 625000000 43429771254349 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (995819117/5000000000 : ℝ)^2133 ≤ (2392726071341/20000000000000 : ℝ)^1621 := by
    have hnat : (995819117 : ℕ)^2133*20000000000000^1621 ≤ 2392726071341^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995819117 5000000000 2392726071341 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414476461/10000000000 : ℝ)^2133 ≤ (44606598361341/100000000000000 : ℝ)^1621 := by
    have hnat : (5414476461 : ℕ)^2133*100000000000000^1621 ≤ 44606598361341^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414476461 10000000000 44606598361341 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331598177/625000000 : ℝ), (-995819117/5000000000 : ℝ), (5414476461/10000000000 : ℝ)] ![(43429771254349/100000000000000 : ℝ), (2392726071341/20000000000000 : ℝ), (44606598361341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331598177/625000000 : ℝ)|^2133 ≤ (43429771254349/100000000000000 : ℝ)^1621
        have hw : |(331598177/625000000 : ℝ)|=(331598177/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-995819117/5000000000 : ℝ)|^2133 ≤ (2392726071341/20000000000000 : ℝ)^1621
        have hw : |(-995819117/5000000000 : ℝ)|=(995819117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414476461/10000000000 : ℝ)|^2133 ≤ (44606598361341/100000000000000 : ℝ)^1621
        have hw : |(5414476461/10000000000 : ℝ)|=(5414476461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s5_6 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326392677/2500000000 : ℝ)*x 0 + (2707238301/5000000000 : ℝ)*x 1 + (-1991638211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326392677/2500000000 : ℝ)^2133 ≤ (43429769918723/100000000000000 : ℝ)^1621 := by
    have hnat : (1326392677 : ℕ)^2133*100000000000000^1621 ≤ 43429769918723^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326392677 2500000000 43429769918723 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707238301/5000000000 : ℝ)^2133 ≤ (8921319977971/20000000000000 : ℝ)^1621 := by
    have hnat : (2707238301 : ℕ)^2133*20000000000000^1621 ≤ 8921319977971^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707238301 5000000000 8921319977971 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1991638211/10000000000 : ℝ)^2133 ≤ (11963630174907/100000000000000 : ℝ)^1621 := by
    have hnat : (1991638211 : ℕ)^2133*100000000000000^1621 ≤ 11963630174907^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991638211 10000000000 11963630174907 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326392677/2500000000 : ℝ), (2707238301/5000000000 : ℝ), (-1991638211/10000000000 : ℝ)] ![(43429769918723/100000000000000 : ℝ), (8921319977971/20000000000000 : ℝ), (11963630174907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326392677/2500000000 : ℝ)|^2133 ≤ (43429769918723/100000000000000 : ℝ)^1621
        have hw : |(1326392677/2500000000 : ℝ)|=(1326392677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707238301/5000000000 : ℝ)|^2133 ≤ (8921319977971/20000000000000 : ℝ)^1621
        have hw : |(2707238301/5000000000 : ℝ)|=(2707238301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1991638211/10000000000 : ℝ)|^2133 ≤ (11963630174907/100000000000000 : ℝ)^1621
        have hw : |(-1991638211/10000000000 : ℝ)|=(1991638211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s5_7 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4336109779/10000000000 : ℝ)*x 0 + (45161259/100000000 : ℝ)*x 1 + (4162976511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4336109779/10000000000 : ℝ)^2133 ≤ (33302496252223/100000000000000 : ℝ)^1621 := by
    have hnat : (4336109779 : ℕ)^2133*100000000000000^1621 ≤ 33302496252223^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4336109779 10000000000 33302496252223 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45161259/100000000 : ℝ)^2133 ≤ (35133577290901/100000000000000 : ℝ)^1621 := by
    have hnat : (45161259 : ℕ)^2133*100000000000000^1621 ≤ 35133577290901^1621*100000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45161259 100000000 35133577290901 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4162976511/10000000000 : ℝ)^2133 ≤ (315639264413/1000000000000 : ℝ)^1621 := by
    have hnat : (4162976511 : ℕ)^2133*1000000000000^1621 ≤ 315639264413^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162976511 10000000000 315639264413 1000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4336109779/10000000000 : ℝ), (45161259/100000000 : ℝ), (4162976511/10000000000 : ℝ)] ![(33302496252223/100000000000000 : ℝ), (35133577290901/100000000000000 : ℝ), (315639264413/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4336109779/10000000000 : ℝ)|^2133 ≤ (33302496252223/100000000000000 : ℝ)^1621
        have hw : |(4336109779/10000000000 : ℝ)|=(4336109779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(45161259/100000000 : ℝ)|^2133 ≤ (35133577290901/100000000000000 : ℝ)^1621
        have hw : |(45161259/100000000 : ℝ)|=(45161259/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4162976511/10000000000 : ℝ)|^2133 ≤ (315639264413/1000000000000 : ℝ)^1621
        have hw : |(4162976511/10000000000 : ℝ)|=(4162976511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1306_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10997/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11051/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2939/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10997/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10997/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10997/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10997/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10997/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10997/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10997/100000 : ℝ) ^ (4265/1024 : ℝ) ≤ (5079719149995639/50000000000000000000 : ℝ) := by
    have hpowers : (10997/100000 : ℝ)^4265 ≤ (5079719149995639/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10997 : ℕ)^4265*50000000000000000000^1024 ≤ 5079719149995639^1024*100000^4265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10997 100000 5079719149995639 50000000000000000000 4265 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10997/100000 : ℝ)) (X := (5079719149995639/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14753/100000 : ℝ) ^ (4265/1024 : ℝ) ≤ (6908506271945673/20000000000000000000 : ℝ) := by
    have hpowers : (14753/100000 : ℝ)^4265 ≤ (6908506271945673/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14753 : ℕ)^4265*20000000000000000000^1024 ≤ 6908506271945673^1024*100000^4265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14753 100000 6908506271945673 20000000000000000000 4265 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14753/100000 : ℝ)) (X := (6908506271945673/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005079719149995639/25000000000000000000 : ℝ) ≤ (2000097561188839/2000000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (25005079719149995639/25000000000000000000 : ℝ)^1024 ≤ (2000097561188839/2000000000000000 : ℝ)^4265 := by
      have hnat : (25005079719149995639 : ℕ)^1024*2000000000000000^4265 ≤ 2000097561188839^4265*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005079719149995639 25000000000000000000 2000097561188839 2000000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000097561188839/2000000000000000 : ℝ)) (X := (25005079719149995639/25000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044701969659719643/100000000000000000000 : ℝ) ≤ (1000107308427377/1000000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (100044701969659719643/100000000000000000000 : ℝ)^1024 ≤ (1000107308427377/1000000000000000 : ℝ)^4265 := by
      have hnat : (100044701969659719643 : ℕ)^1024*1000000000000000^4265 ≤ 1000107308427377^4265*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044701969659719643 100000000000000000000 1000107308427377 1000000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000107308427377/1000000000000000 : ℝ)) (X := (100044701969659719643/100000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006908506271945673/10000000000000000000 : ℝ) ≤ (2000331672520669/2000000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (10006908506271945673/10000000000000000000 : ℝ)^1024 ≤ (2000331672520669/2000000000000000 : ℝ)^4265 := by
      have hnat : (10006908506271945673 : ℕ)^1024*2000000000000000^4265 ≤ 2000331672520669^4265*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006908506271945673 10000000000000000000 2000331672520669 2000000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000331672520669/2000000000000000 : ℝ)) (X := (10006908506271945673/10000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5079719149995639/50000000000000000000 : ℝ) ≤ ((1251631986251524129/1252000000000000000 : ℝ)+2*(7803711061/5008000000000 : ℝ)*(10997/100000 : ℝ))^(4265/1024 : ℝ) := by
    rw [show (1251631986251524129/1252000000000000000 : ℝ)+2*(7803711061/5008000000000 : ℝ)*(10997/100000 : ℝ)=(2000097561188839/2000000000000000 : ℝ) by norm_num, show 1+2*(5079719149995639/50000000000000000000 : ℝ)=(25005079719149995639/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6908506271945673/20000000000000000000 : ℝ)+(5079719149995639/50000000000000000000 : ℝ) ≤ ((1251631986251524129/1252000000000000000 : ℝ)+(7803711061/5008000000000 : ℝ)*((14753/100000 : ℝ)+(10997/100000 : ℝ)))^(4265/1024 : ℝ) := by
    rw [show (1251631986251524129/1252000000000000000 : ℝ)+(7803711061/5008000000000 : ℝ)*((14753/100000 : ℝ)+(10997/100000 : ℝ))=(1000107308427377/1000000000000000 : ℝ) by norm_num, show 1+(6908506271945673/20000000000000000000 : ℝ)+(5079719149995639/50000000000000000000 : ℝ)=(100044701969659719643/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6908506271945673/20000000000000000000 : ℝ) ≤ ((1251631986251524129/1252000000000000000 : ℝ)+2*(7803711061/5008000000000 : ℝ)*(14753/100000 : ℝ))^(4265/1024 : ℝ) := by
    rw [show (1251631986251524129/1252000000000000000 : ℝ)+2*(7803711061/5008000000000 : ℝ)*(14753/100000 : ℝ)=(2000331672520669/2000000000000000 : ℝ) by norm_num, show 1+2*(6908506271945673/20000000000000000000 : ℝ)=(10006908506271945673/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1251631986251524129/1252000000000000000 : ℝ)*(X 1 0+X 2 0)+(7803711061/5008000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (10997/100000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (1251631986251524129/1252000000000000000 : ℝ)) (alpha := (7803711061/5008000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1251631986251524129/1252000000000000000 : ℝ)*(X 0 1+X 2 1)+(7803711061/5008000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (10997/100000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (1251631986251524129/1252000000000000000 : ℝ)) (alpha := (7803711061/5008000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1251631986251524129/1252000000000000000 : ℝ)*(X 0 2+X 1 2)+(7803711061/5008000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (10997/100000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (1251631986251524129/1252000000000000000 : ℝ)) (alpha := (7803711061/5008000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1037708503/5000000000 : ℝ)*X 0 0+(676887251/1250000000 : ℝ)*X 0 1+(1310736007/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674861913/5000000000 : ℝ)*X 1 0+(-2163170761/10000000000 : ℝ)*X 1 1+(524294403/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674861909/5000000000 : ℝ)*X 2 0+(1310736007/2500000000 : ℝ)*X 2 1+(-270396347/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4336083317/10000000000 : ℝ)*X 0 0+(166467697/400000000 : ℝ)*X 0 1+(4517403389/10000000000 : ℝ)*X 0 2+(4336083317/10000000000 : ℝ)*X 1 0+(166467697/400000000 : ℝ)*X 1 1+(4517403389/10000000000 : ℝ)*X 1 2+(4336083317/10000000000 : ℝ)*X 2 0+(166467697/400000000 : ℝ)*X 2 1+(4517403389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2075429743/10000000000 : ℝ)*X 0 0+(1048712467/2000000000 : ℝ)*X 0 1+(5414476547/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331598177/625000000 : ℝ)*X 1 0+(-995819117/5000000000 : ℝ)*X 1 1+(5414476461/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326392677/2500000000 : ℝ)*X 2 0+(2707238301/5000000000 : ℝ)*X 2 1+(-1991638211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4336109779/10000000000 : ℝ)*X 0 0+(45161259/100000000 : ℝ)*X 0 1+(4162976511/10000000000 : ℝ)*X 0 2+(4336109779/10000000000 : ℝ)*X 1 0+(45161259/100000000 : ℝ)*X 1 1+(4162976511/10000000000 : ℝ)*X 1 2+(4336109779/10000000000 : ℝ)*X 2 0+(45161259/100000000 : ℝ)*X 2 1+(4162976511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23181773120959854504721233/3130000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1378957207/100000000000000 : ℝ)*(base19) + (1270166837/100000000000000 : ℝ)*(base23) + (10710559/20000000000000 : ℝ)*(lower2) + (3890709/2000000000000 : ℝ)*(upper3) + (101545461/100000000000000 : ℝ)*(upper5) + (431005412114259/10000000000000 : ℝ)*(major0) + (431005412114259/10000000000000 : ℝ)*(major1) + (431005412114259/10000000000000 : ℝ)*(major2) + (5808782405873381/100000000000000 : ℝ)*(sp0) + (5808807995795053/100000000000000 : ℝ)*(sp1) + (5808808104585423/100000000000000 : ℝ)*(sp2) + (1405642009961211/50000000000000 : ℝ)*(sp3) + (168555493/625000000000 : ℝ)*(sp4) + (7300366623/50000000000000 : ℝ)*(sp7) + (702824655163917/25000000000000 : ℝ)*(f.failure) + (5808809374752261/100000000000000 : ℝ)*(f.sum) + (3104759367443/626000000000000000000000000 : ℝ)*base65 + (156111984423754589/12520000000000000000000000000000 : ℝ)*base68 + (51589819784634589/12520000000000000000000000000000 : ℝ)*base70 + (62800909334485411/12520000000000000000000000000000 : ℝ)*base71 + (2082200345067/626000000000000000000000000 : ℝ)*base74 + (33412502060874589/12520000000000000000000000000000 : ℝ)*base76 + (182486827060234589/12520000000000000000000000000000 : ℝ)*base78 + (126507117253674589/12520000000000000000000000000000 : ℝ)*base80 + (342425860359/626000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4663869/2500000000000000000000 : ℝ)*base89 + (4663869/2500000000000000000000 : ℝ)*base91 + (4663869/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (145493573377261896325647099/15650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1637346903/100000000000000 : ℝ)*(base19) + (34889907/2000000000000 : ℝ)*(base23) + (89840573/50000000000000 : ℝ)*(upper3) + (107515029/100000000000000 : ℝ)*(lower4) + (16157827/10000000000000 : ℝ)*(upper5) + (1085318370458659/25000000000000 : ℝ)*(major0) + (1085318370458659/25000000000000 : ℝ)*(major1) + (1085318370458659/25000000000000 : ℝ)*(major2) + (15181109437/50000000000000 : ℝ)*(sp1) + (17659296661/50000000000000 : ℝ)*(sp2) + (1170176945670289/20000000000000 : ℝ)*(sp4) + (1462713182196417/25000000000000 : ℝ)*(sp5) + (5850847665262773/100000000000000 : ℝ)*(sp6) + (2831661925427357/100000000000000 : ℝ)*(sp7) + (2831661925427357/100000000000000 : ℝ)*(f.failure) + (1170176945670289/20000000000000 : ℝ)*(f.sum) + (2222155654511/313000000000000000000000000 : ℝ)*base65 + (143721093402266989/31300000000000000000000000000000 : ℝ)*base68 + (48159109319366989/31300000000000000000000000000000 : ℝ)*base70 + (280179122098666989/31300000000000000000000000000000 : ℝ)*base72 + (1506863826433/313000000000000000000000000 : ℝ)*base73 + (191066231488266989/31300000000000000000000000000000 : ℝ)*base76 + (65012561172666989/31300000000000000000000000000000 : ℝ)*base78 + (265349584585366989/31300000000000000000000000000000 : ℝ)*base80 + (953178852519/313000000000000000000000000 : ℝ)*base81 + (20271949/10000000000000000000000 : ℝ)*base89 + (20271949/10000000000000000000000 : ℝ)*base91 + (20271949/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1306_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10997/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1306_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1306_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8127/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4803/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1306_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1306_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1306_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8127/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4803/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2939/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1306_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
