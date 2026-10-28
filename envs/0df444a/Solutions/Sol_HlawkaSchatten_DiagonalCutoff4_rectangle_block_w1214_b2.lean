-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1214_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:08:14.022719+00:00
-- url     : https://prove2.me/submissions/e4c59e38-409c-4a72-ad03-d92c74c68e3a

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
theorem support_rectangle_w1214_s6_0 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2132899619/10000000000 : ℝ)*x 0 + (673993437/1250000000 : ℝ)*x 1 + (658326837/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132899619/10000000000 : ℝ)^8407 ≤ (6483753185237/50000000000000 : ℝ)^6359 := by
    have hnat : (2132899619 : ℕ)^8407*50000000000000^6359 ≤ 6483753185237^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132899619 10000000000 6483753185237 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673993437/1250000000 : ℝ)^8407 ≤ (8838545311253/20000000000000 : ℝ)^6359 := by
    have hnat : (673993437 : ℕ)^8407*20000000000000^6359 ≤ 8838545311253^6359*1250000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673993437 1250000000 8838545311253 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658326837/1250000000 : ℝ)^8407 ≤ (535497088137/1250000000000 : ℝ)^6359 := by
    have hnat : (658326837 : ℕ)^8407*1250000000000^6359 ≤ 535497088137^6359*1250000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658326837 1250000000 535497088137 1250000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2132899619/10000000000 : ℝ), (673993437/1250000000 : ℝ), (658326837/1250000000 : ℝ)] ![(6483753185237/50000000000000 : ℝ), (8838545311253/20000000000000 : ℝ), (535497088137/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2132899619/10000000000 : ℝ)|^8407 ≤ (6483753185237/50000000000000 : ℝ)^6359
        have hw : |(-2132899619/10000000000 : ℝ)|=(2132899619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673993437/1250000000 : ℝ)|^8407 ≤ (8838545311253/20000000000000 : ℝ)^6359
        have hw : |(673993437/1250000000 : ℝ)|=(673993437/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658326837/1250000000 : ℝ)|^8407 ≤ (535497088137/1250000000000 : ℝ)^6359
        have hw : |(658326837/1250000000 : ℝ)|=(658326837/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s6_1 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672254899/5000000000 : ℝ)*x 0 + (-549114109/2500000000 : ℝ)*x 1 + (210664581/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672254899/5000000000 : ℝ)^8407 ≤ (43679435113399/100000000000000 : ℝ)^6359 := by
    have hnat : (2672254899 : ℕ)^8407*100000000000000^6359 ≤ 43679435113399^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672254899 5000000000 43679435113399 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549114109/2500000000 : ℝ)^8407 ≤ (6740399829689/50000000000000 : ℝ)^6359 := by
    have hnat : (549114109 : ℕ)^8407*50000000000000^6359 ≤ 6740399829689^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549114109 2500000000 6740399829689 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210664581/400000000 : ℝ)^8407 ≤ (10709941303009/25000000000000 : ℝ)^6359 := by
    have hnat : (210664581 : ℕ)^8407*25000000000000^6359 ≤ 10709941303009^6359*400000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210664581 400000000 10709941303009 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672254899/5000000000 : ℝ), (-549114109/2500000000 : ℝ), (210664581/400000000 : ℝ)] ![(43679435113399/100000000000000 : ℝ), (6740399829689/50000000000000 : ℝ), (10709941303009/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672254899/5000000000 : ℝ)|^8407 ≤ (43679435113399/100000000000000 : ℝ)^6359
        have hw : |(2672254899/5000000000 : ℝ)|=(2672254899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-549114109/2500000000 : ℝ)|^8407 ≤ (6740399829689/50000000000000 : ℝ)^6359
        have hw : |(-549114109/2500000000 : ℝ)|=(549114109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210664581/400000000 : ℝ)|^8407 ≤ (10709941303009/25000000000000 : ℝ)^6359
        have hw : |(210664581/400000000 : ℝ)|=(210664581/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s6_2 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (20876991/39062500 : ℝ)*x 0 + (82290853/156250000 : ℝ)*x 1 + (-2196456483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20876991/39062500 : ℝ)^8407 ≤ (21839717005649/50000000000000 : ℝ)^6359 := by
    have hnat : (20876991 : ℕ)^8407*50000000000000^6359 ≤ 21839717005649^6359*39062500^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20876991 39062500 21839717005649 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82290853/156250000 : ℝ)^8407 ≤ (856795318651/2000000000000 : ℝ)^6359 := by
    have hnat : (82290853 : ℕ)^8407*2000000000000^6359 ≤ 856795318651^6359*156250000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82290853 156250000 856795318651 2000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2196456483/10000000000 : ℝ)^8407 ≤ (2696160008149/20000000000000 : ℝ)^6359 := by
    have hnat : (2196456483 : ℕ)^8407*20000000000000^6359 ≤ 2696160008149^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196456483 10000000000 2696160008149 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20876991/39062500 : ℝ), (82290853/156250000 : ℝ), (-2196456483/10000000000 : ℝ)] ![(21839717005649/50000000000000 : ℝ), (856795318651/2000000000000 : ℝ), (2696160008149/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20876991/39062500 : ℝ)|^8407 ≤ (21839717005649/50000000000000 : ℝ)^6359
        have hw : |(20876991/39062500 : ℝ)|=(20876991/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82290853/156250000 : ℝ)|^8407 ≤ (856795318651/2000000000000 : ℝ)^6359
        have hw : |(82290853/156250000 : ℝ)|=(82290853/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2196456483/10000000000 : ℝ)|^8407 ≤ (2696160008149/20000000000000 : ℝ)^6359
        have hw : |(-2196456483/10000000000 : ℝ)|=(2196456483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s6_3 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (272163513/625000000 : ℝ)*x 0 + (2114988111/5000000000 : ℝ)*x 1 + (2241424533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272163513/625000000 : ℝ)^8407 ≤ (33317232759141/100000000000000 : ℝ)^6359 := by
    have hnat : (272163513 : ℕ)^8407*100000000000000^6359 ≤ 33317232759141^6359*625000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272163513 625000000 33317232759141 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114988111/5000000000 : ℝ)^8407 ≤ (4007791587211/12500000000000 : ℝ)^6359 := by
    have hnat : (2114988111 : ℕ)^8407*12500000000000^6359 ≤ 4007791587211^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114988111 5000000000 4007791587211 12500000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241424533/5000000000 : ℝ)^8407 ≤ (34620434527297/100000000000000 : ℝ)^6359 := by
    have hnat : (2241424533 : ℕ)^8407*100000000000000^6359 ≤ 34620434527297^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241424533 5000000000 34620434527297 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272163513/625000000 : ℝ), (2114988111/5000000000 : ℝ), (2241424533/5000000000 : ℝ)] ![(33317232759141/100000000000000 : ℝ), (4007791587211/12500000000000 : ℝ), (34620434527297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272163513/625000000 : ℝ)|^8407 ≤ (33317232759141/100000000000000 : ℝ)^6359
        have hw : |(272163513/625000000 : ℝ)|=(272163513/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114988111/5000000000 : ℝ)|^8407 ≤ (4007791587211/12500000000000 : ℝ)^6359
        have hw : |(2114988111/5000000000 : ℝ)|=(2114988111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2241424533/5000000000 : ℝ)|^8407 ≤ (34620434527297/100000000000000 : ℝ)^6359
        have hw : |(2241424533/5000000000 : ℝ)|=(2241424533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s6_4 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1066452239/5000000000 : ℝ)*x 0 + (2633465717/5000000000 : ℝ)*x 1 + (5391629539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066452239/5000000000 : ℝ)^8407 ≤ (810471589141/6250000000000 : ℝ)^6359 := by
    have hnat : (1066452239 : ℕ)^8407*6250000000000^6359 ≤ 810471589141^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066452239 5000000000 810471589141 6250000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633465717/5000000000 : ℝ)^8407 ≤ (42843173266707/100000000000000 : ℝ)^6359 := by
    have hnat : (2633465717 : ℕ)^8407*100000000000000^6359 ≤ 42843173266707^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633465717 5000000000 42843173266707 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391629539/10000000000 : ℝ)^8407 ≤ (11047320324801/25000000000000 : ℝ)^6359 := by
    have hnat : (5391629539 : ℕ)^8407*25000000000000^6359 ≤ 11047320324801^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391629539 10000000000 11047320324801 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1066452239/5000000000 : ℝ), (2633465717/5000000000 : ℝ), (5391629539/10000000000 : ℝ)] ![(810471589141/6250000000000 : ℝ), (42843173266707/100000000000000 : ℝ), (11047320324801/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1066452239/5000000000 : ℝ)|^8407 ≤ (810471589141/6250000000000 : ℝ)^6359
        have hw : |(-1066452239/5000000000 : ℝ)|=(1066452239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633465717/5000000000 : ℝ)|^8407 ≤ (42843173266707/100000000000000 : ℝ)^6359
        have hw : |(2633465717/5000000000 : ℝ)|=(2633465717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391629539/10000000000 : ℝ)|^8407 ≤ (11047320324801/25000000000000 : ℝ)^6359
        have hw : |(5391629539/10000000000 : ℝ)|=(5391629539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s6_5 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312591667/10000000000 : ℝ)*x 0 + (-2071441487/10000000000 : ℝ)*x 1 + (1078325907/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312591667/10000000000 : ℝ)^8407 ≤ (43334894531993/100000000000000 : ℝ)^6359 := by
    have hnat : (5312591667 : ℕ)^8407*100000000000000^6359 ≤ 43334894531993^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312591667 10000000000 43334894531993 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071441487/10000000000 : ℝ)^8407 ≤ (6237912099309/50000000000000 : ℝ)^6359 := by
    have hnat : (2071441487 : ℕ)^8407*50000000000000^6359 ≤ 6237912099309^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071441487 10000000000 6237912099309 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078325907/2000000000 : ℝ)^8407 ≤ (22094640627931/50000000000000 : ℝ)^6359 := by
    have hnat : (1078325907 : ℕ)^8407*50000000000000^6359 ≤ 22094640627931^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078325907 2000000000 22094640627931 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312591667/10000000000 : ℝ), (-2071441487/10000000000 : ℝ), (1078325907/2000000000 : ℝ)] ![(43334894531993/100000000000000 : ℝ), (6237912099309/50000000000000 : ℝ), (22094640627931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312591667/10000000000 : ℝ)|^8407 ≤ (43334894531993/100000000000000 : ℝ)^6359
        have hw : |(5312591667/10000000000 : ℝ)|=(5312591667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2071441487/10000000000 : ℝ)|^8407 ≤ (6237912099309/50000000000000 : ℝ)^6359
        have hw : |(-2071441487/10000000000 : ℝ)|=(2071441487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078325907/2000000000 : ℝ)|^8407 ≤ (22094640627931/50000000000000 : ℝ)^6359
        have hw : |(1078325907/2000000000 : ℝ)|=(1078325907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s6_6 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312591669/10000000000 : ℝ)*x 0 + (5391629533/10000000000 : ℝ)*x 1 + (-2071441487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312591669/10000000000 : ℝ)^8407 ≤ (21667447276781/50000000000000 : ℝ)^6359 := by
    have hnat : (5312591669 : ℕ)^8407*50000000000000^6359 ≤ 21667447276781^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312591669 10000000000 21667447276781 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391629533/10000000000 : ℝ)^8407 ≤ (44189281234191/100000000000000 : ℝ)^6359 := by
    have hnat : (5391629533 : ℕ)^8407*100000000000000^6359 ≤ 44189281234191^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391629533 10000000000 44189281234191 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2071441487/10000000000 : ℝ)^8407 ≤ (6237912099309/50000000000000 : ℝ)^6359 := by
    have hnat : (2071441487 : ℕ)^8407*50000000000000^6359 ≤ 6237912099309^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071441487 10000000000 6237912099309 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312591669/10000000000 : ℝ), (5391629533/10000000000 : ℝ), (-2071441487/10000000000 : ℝ)] ![(21667447276781/50000000000000 : ℝ), (44189281234191/100000000000000 : ℝ), (6237912099309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312591669/10000000000 : ℝ)|^8407 ≤ (21667447276781/50000000000000 : ℝ)^6359
        have hw : |(5312591669/10000000000 : ℝ)|=(5312591669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391629533/10000000000 : ℝ)|^8407 ≤ (44189281234191/100000000000000 : ℝ)^6359
        have hw : |(5391629533/10000000000 : ℝ)|=(5391629533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2071441487/10000000000 : ℝ)|^8407 ≤ (6237912099309/50000000000000 : ℝ)^6359
        have hw : |(-2071441487/10000000000 : ℝ)|=(2071441487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s6_7 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177312999/5000000000 : ℝ)*x 0 + (896441943/2000000000 : ℝ)*x 1 + (33051701/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177312999/5000000000 : ℝ)^8407 ≤ (8329332946563/25000000000000 : ℝ)^6359 := by
    have hnat : (2177312999 : ℕ)^8407*25000000000000^6359 ≤ 8329332946563^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177312999 5000000000 8329332946563 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896441943/2000000000 : ℝ)^8407 ≤ (2163369176887/6250000000000 : ℝ)^6359 := by
    have hnat : (896441943 : ℕ)^8407*6250000000000^6359 ≤ 2163369176887^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896441943 2000000000 2163369176887 6250000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33051701/78125000 : ℝ)^8407 ≤ (32068761361887/100000000000000 : ℝ)^6359 := by
    have hnat : (33051701 : ℕ)^8407*100000000000000^6359 ≤ 32068761361887^6359*78125000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33051701 78125000 32068761361887 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177312999/5000000000 : ℝ), (896441943/2000000000 : ℝ), (33051701/78125000 : ℝ)] ![(8329332946563/25000000000000 : ℝ), (2163369176887/6250000000000 : ℝ), (32068761361887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177312999/5000000000 : ℝ)|^8407 ≤ (8329332946563/25000000000000 : ℝ)^6359
        have hw : |(2177312999/5000000000 : ℝ)|=(2177312999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(896441943/2000000000 : ℝ)|^8407 ≤ (2163369176887/6250000000000 : ℝ)^6359
        have hw : |(896441943/2000000000 : ℝ)|=(896441943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33051701/78125000 : ℝ)|^8407 ≤ (32068761361887/100000000000000 : ℝ)^6359
        have hw : |(33051701/78125000 : ℝ)|=(33051701/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1214_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11417/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (143/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2819/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14119/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11417/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14119/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11417/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14119/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11417/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14119/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11417/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14119/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11417/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14119/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11417/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11417/100000 : ℝ) ^ (4203/1024 : ℝ) ≤ (1354345756107723/10000000000000000000 : ℝ) := by
    have hpowers : (11417/100000 : ℝ)^4203 ≤ (1354345756107723/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11417 : ℕ)^4203*10000000000000000000^1024 ≤ 1354345756107723^1024*100000^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11417 100000 1354345756107723 10000000000000000000 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11417/100000 : ℝ)) (X := (1354345756107723/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14119/100000 : ℝ) ^ (4203/1024 : ℝ) ≤ (6477492253389893/20000000000000000000 : ℝ) := by
    have hpowers : (14119/100000 : ℝ)^4203 ≤ (6477492253389893/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14119 : ℕ)^4203*20000000000000000000^1024 ≤ 6477492253389893^1024*100000^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14119 100000 6477492253389893 20000000000000000000 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14119/100000 : ℝ)) (X := (6477492253389893/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001354345756107723/5000000000000000000 : ℝ) ≤ (5000329932907629/5000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (5001354345756107723/5000000000000000000 : ℝ)^1024 ≤ (5000329932907629/5000000000000000 : ℝ)^4203 := by
      have hnat : (5001354345756107723 : ℕ)^1024*5000000000000000^4203 ≤ 5000329932907629^4203*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001354345756107723 5000000000000000000 5000329932907629 5000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000329932907629/5000000000000000 : ℝ)) (X := (5001354345756107723/5000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009186183765605339/20000000000000000000 : ℝ) ≤ (2000223769180477/2000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (20009186183765605339/20000000000000000000 : ℝ)^1024 ≤ (2000223769180477/2000000000000000 : ℝ)^4203 := by
      have hnat : (20009186183765605339 : ℕ)^1024*2000000000000000^4203 ≤ 2000223769180477^4203*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009186183765605339 20000000000000000000 2000223769180477 2000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000223769180477/2000000000000000 : ℝ)) (X := (20009186183765605339/20000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006477492253389893/10000000000000000000 : ℝ) ≤ (1250197228248689/1250000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (10006477492253389893/10000000000000000000 : ℝ)^1024 ≤ (1250197228248689/1250000000000000 : ℝ)^4203 := by
      have hnat : (10006477492253389893 : ℕ)^1024*1250000000000000^4203 ≤ 1250197228248689^4203*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006477492253389893 10000000000000000000 1250197228248689 1250000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250197228248689/1250000000000000 : ℝ)) (X := (10006477492253389893/10000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1354345756107723/10000000000000000000 : ℝ) ≤ ((1929378757580240657/1930000000000000000 : ℝ)+2*(458980087127/270200000000000 : ℝ)*(11417/100000 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (1929378757580240657/1930000000000000000 : ℝ)+2*(458980087127/270200000000000 : ℝ)*(11417/100000 : ℝ)=(5000329932907629/5000000000000000 : ℝ) by norm_num, show 1+2*(1354345756107723/10000000000000000000 : ℝ)=(5001354345756107723/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6477492253389893/20000000000000000000 : ℝ)+(1354345756107723/10000000000000000000 : ℝ) ≤ ((1929378757580240657/1930000000000000000 : ℝ)+(458980087127/270200000000000 : ℝ)*((14119/100000 : ℝ)+(11417/100000 : ℝ)))^(4203/1024 : ℝ) := by
    rw [show (1929378757580240657/1930000000000000000 : ℝ)+(458980087127/270200000000000 : ℝ)*((14119/100000 : ℝ)+(11417/100000 : ℝ))=(2000223769180477/2000000000000000 : ℝ) by norm_num, show 1+(6477492253389893/20000000000000000000 : ℝ)+(1354345756107723/10000000000000000000 : ℝ)=(20009186183765605339/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6477492253389893/20000000000000000000 : ℝ) ≤ ((1929378757580240657/1930000000000000000 : ℝ)+2*(458980087127/270200000000000 : ℝ)*(14119/100000 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (1929378757580240657/1930000000000000000 : ℝ)+2*(458980087127/270200000000000 : ℝ)*(14119/100000 : ℝ)=(1250197228248689/1250000000000000 : ℝ) by norm_num, show 1+2*(6477492253389893/20000000000000000000 : ℝ)=(10006477492253389893/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1929378757580240657/1930000000000000000 : ℝ)*(X 1 0+X 2 0)+(458980087127/270200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (11417/100000 : ℝ)) (hi := (14119/100000 : ℝ)) (c := (1929378757580240657/1930000000000000000 : ℝ)) (alpha := (458980087127/270200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1929378757580240657/1930000000000000000 : ℝ)*(X 0 1+X 2 1)+(458980087127/270200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (11417/100000 : ℝ)) (hi := (14119/100000 : ℝ)) (c := (1929378757580240657/1930000000000000000 : ℝ)) (alpha := (458980087127/270200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1929378757580240657/1930000000000000000 : ℝ)*(X 0 2+X 1 2)+(458980087127/270200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (11417/100000 : ℝ)) (hi := (14119/100000 : ℝ)) (c := (1929378757580240657/1930000000000000000 : ℝ)) (alpha := (458980087127/270200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2132899619/10000000000 : ℝ)*X 0 0+(673993437/1250000000 : ℝ)*X 0 1+(658326837/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672254899/5000000000 : ℝ)*X 1 0+(-549114109/2500000000 : ℝ)*X 1 1+(210664581/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((20876991/39062500 : ℝ)*X 2 0+(82290853/156250000 : ℝ)*X 2 1+(-2196456483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((272163513/625000000 : ℝ)*X 0 0+(2114988111/5000000000 : ℝ)*X 0 1+(2241424533/5000000000 : ℝ)*X 0 2+(272163513/625000000 : ℝ)*X 1 0+(2114988111/5000000000 : ℝ)*X 1 1+(2241424533/5000000000 : ℝ)*X 1 2+(272163513/625000000 : ℝ)*X 2 0+(2114988111/5000000000 : ℝ)*X 2 1+(2241424533/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1066452239/5000000000 : ℝ)*X 0 0+(2633465717/5000000000 : ℝ)*X 0 1+(5391629539/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312591667/10000000000 : ℝ)*X 1 0+(-2071441487/10000000000 : ℝ)*X 1 1+(1078325907/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312591669/10000000000 : ℝ)*X 2 0+(5391629533/10000000000 : ℝ)*X 2 1+(-2071441487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177312999/5000000000 : ℝ)*X 0 0+(896441943/2000000000 : ℝ)*X 0 1+(33051701/78125000 : ℝ)*X 0 2+(2177312999/5000000000 : ℝ)*X 1 0+(896441943/2000000000 : ℝ)*X 1 1+(33051701/78125000 : ℝ)*X 1 2+(2177312999/5000000000 : ℝ)*X 2 0+(896441943/2000000000 : ℝ)*X 2 1+(33051701/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1070236076554571779420677327/337750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (176178021/50000000000000 : ℝ)*(base19) + (238781601/100000000000000 : ℝ)*(base23) + (13808551/50000000000000 : ℝ)*(lower4) + (6539569/50000000000000 : ℝ)*(lower5) + (2983332665720509/50000000000000 : ℝ)*(major0) + (2983332665720509/50000000000000 : ℝ)*(major1) + (2983332665720509/50000000000000 : ℝ)*(major2) + (49867268486919/625000000000 : ℝ)*(sp0) + (3989382516503751/50000000000000 : ℝ)*(sp1) + (3989381487122737/50000000000000 : ℝ)*(sp2) + (988640341617377/25000000000000 : ℝ)*(sp3) + (485491301/20000000000000 : ℝ)*(sp4) + (217233647/10000000000000 : ℝ)*(sp6) + (3805424887/100000000000000 : ℝ)*(sp7) + (1977282585947197/50000000000000 : ℝ)*(f.failure) + (1595753077072709/20000000000000 : ℝ)*(f.sum) + (55468805961057/6755000000000000000000000000 : ℝ)*base66 + (2318128160105390891/675500000000000000000000000000000 : ℝ)*base67 + (6427754441551390891/675500000000000000000000000000000 : ℝ)*base69 + (2926613592267109109/675500000000000000000000000000000 : ℝ)*base72 + (13217340715913/1688750000000000000000000000 : ℝ)*base74 + (12368367916168890891/675500000000000000000000000000000 : ℝ)*base75 + (2262921155286109109/675500000000000000000000000000000 : ℝ)*base78 + (803471324651390891/675500000000000000000000000000000 : ℝ)*base79 + (60637642065517/6755000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3167/125000000000000000000 : ℝ)*base89 + (3167/125000000000000000000 : ℝ)*base91 + (3167/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6845350239777769839326867439/675500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1827673803/100000000000000 : ℝ)*(base19) + (1987931057/100000000000000 : ℝ)*(base23) + (100762391/50000000000000 : ℝ)*(upper3) + (71769499/100000000000000 : ℝ)*(lower4) + (207448913/100000000000000 : ℝ)*(upper5) + (5997027704215613/100000000000000 : ℝ)*(major0) + (5997027704215613/100000000000000 : ℝ)*(major1) + (5997027704215613/100000000000000 : ℝ)*(major2) + (5099605787/10000000000000 : ℝ)*(sp1) + (13670538559/25000000000000 : ℝ)*(sp2) + (8019366433586417/100000000000000 : ℝ)*(sp4) + (1002414201231843/12500000000000 : ℝ)*(sp5) + (2004827440875281/25000000000000 : ℝ)*(sp6) + (993672159263257/25000000000000 : ℝ)*(sp7) + (993672159263257/25000000000000 : ℝ)*(f.failure) + (8019366433586417/100000000000000 : ℝ)*(f.sum) + (24214812904671/13510000000000000000000000000 : ℝ)*base65 + (7422145490908005813/1351000000000000000000000000000000 : ℝ)*base68 + (8973383604792994187/1351000000000000000000000000000000 : ℝ)*base69 + (14257599505262005813/1351000000000000000000000000000000 : ℝ)*base72 + (28236675678131/13510000000000000000000000000 : ℝ)*base73 + (4803584214315994187/1351000000000000000000000000000000 : ℝ)*base75 + (4036048714633994187/1351000000000000000000000000000000 : ℝ)*base77 + (823581919165994187/1351000000000000000000000000000000 : ℝ)*base79 + (452966264229/13510000000000000000000000000 : ℝ)*base82 + (825173/62500000000000000000 : ℝ)*base90 + (825173/62500000000000000000 : ℝ)*base92 + (825173/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1214_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11417/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (143/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1214_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1214_s7_0 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1066459153/5000000000 : ℝ)*x 0 + (5391723987/10000000000 : ℝ)*x 1 + (1053365187/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066459153/5000000000 : ℝ)^8407 ≤ (3241914143357/25000000000000 : ℝ)^6359 := by
    have hnat : (1066459153 : ℕ)^8407*25000000000000^6359 ≤ 3241914143357^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066459153 5000000000 3241914143357 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391723987/10000000000 : ℝ)^8407 ≤ (11047576173443/25000000000000 : ℝ)^6359 := by
    have hnat : (5391723987 : ℕ)^8407*25000000000000^6359 ≤ 11047576173443^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391723987 10000000000 11047576173443 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053365187/2000000000 : ℝ)^8407 ≤ (42842038718039/100000000000000 : ℝ)^6359 := by
    have hnat : (1053365187 : ℕ)^8407*100000000000000^6359 ≤ 42842038718039^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053365187 2000000000 42842038718039 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1066459153/5000000000 : ℝ), (5391723987/10000000000 : ℝ), (1053365187/2000000000 : ℝ)] ![(3241914143357/25000000000000 : ℝ), (11047576173443/25000000000000 : ℝ), (42842038718039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1066459153/5000000000 : ℝ)|^8407 ≤ (3241914143357/25000000000000 : ℝ)^6359
        have hw : |(-1066459153/5000000000 : ℝ)|=(1066459153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391723987/10000000000 : ℝ)|^8407 ≤ (11047576173443/25000000000000 : ℝ)^6359
        have hw : |(5391723987/10000000000 : ℝ)|=(5391723987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053365187/2000000000 : ℝ)|^8407 ≤ (42842038718039/100000000000000 : ℝ)^6359
        have hw : |(1053365187/2000000000 : ℝ)|=(1053365187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s7_1 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672225389/5000000000 : ℝ)*x 0 + (-219624863/1000000000 : ℝ)*x 1 + (5266830617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672225389/5000000000 : ℝ)^8407 ≤ (8735759481689/20000000000000 : ℝ)^6359 := by
    have hnat : (2672225389 : ℕ)^8407*20000000000000^6359 ≤ 8735759481689^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672225389 5000000000 8735759481689 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219624863/1000000000 : ℝ)^8407 ≤ (13479113507273/100000000000000 : ℝ)^6359 := by
    have hnat : (219624863 : ℕ)^8407*100000000000000^6359 ≤ 13479113507273^6359*1000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219624863 1000000000 13479113507273 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266830617/10000000000 : ℝ)^8407 ≤ (42842089068663/100000000000000 : ℝ)^6359 := by
    have hnat : (5266830617 : ℕ)^8407*100000000000000^6359 ≤ 42842089068663^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266830617 10000000000 42842089068663 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672225389/5000000000 : ℝ), (-219624863/1000000000 : ℝ), (5266830617/10000000000 : ℝ)] ![(8735759481689/20000000000000 : ℝ), (13479113507273/100000000000000 : ℝ), (42842089068663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672225389/5000000000 : ℝ)|^8407 ≤ (8735759481689/20000000000000 : ℝ)^6359
        have hw : |(2672225389/5000000000 : ℝ)|=(2672225389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-219624863/1000000000 : ℝ)|^8407 ≤ (13479113507273/100000000000000 : ℝ)^6359
        have hw : |(-219624863/1000000000 : ℝ)|=(219624863/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266830617/10000000000 : ℝ)|^8407 ≤ (42842089068663/100000000000000 : ℝ)^6359
        have hw : |(5266830617/10000000000 : ℝ)|=(5266830617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s7_2 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668056931/1250000000 : ℝ)*x 0 + (526682757/1000000000 : ℝ)*x 1 + (-2196246451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668056931/1250000000 : ℝ)^8407 ≤ (21839423933613/50000000000000 : ℝ)^6359 := by
    have hnat : (668056931 : ℕ)^8407*50000000000000^6359 ≤ 21839423933613^6359*1250000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668056931 1250000000 21839423933613 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526682757/1000000000 : ℝ)^8407 ≤ (21421028150483/50000000000000 : ℝ)^6359 := by
    have hnat : (526682757 : ℕ)^8407*50000000000000^6359 ≤ 21421028150483^6359*1000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526682757 1000000000 21421028150483 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2196246451/10000000000 : ℝ)^8407 ≤ (1347909582699/10000000000000 : ℝ)^6359 := by
    have hnat : (2196246451 : ℕ)^8407*10000000000000^6359 ≤ 1347909582699^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196246451 10000000000 1347909582699 10000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668056931/1250000000 : ℝ), (526682757/1000000000 : ℝ), (-2196246451/10000000000 : ℝ)] ![(21839423933613/50000000000000 : ℝ), (21421028150483/50000000000000 : ℝ), (1347909582699/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668056931/1250000000 : ℝ)|^8407 ≤ (21839423933613/50000000000000 : ℝ)^6359
        have hw : |(668056931/1250000000 : ℝ)|=(668056931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526682757/1000000000 : ℝ)|^8407 ≤ (21421028150483/50000000000000 : ℝ)^6359
        have hw : |(526682757/1000000000 : ℝ)|=(526682757/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2196246451/10000000000 : ℝ)|^8407 ≤ (1347909582699/10000000000000 : ℝ)^6359
        have hw : |(-2196246451/10000000000 : ℝ)|=(2196246451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s7_3 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088658751/2500000000 : ℝ)*x 0 + (2115206353/5000000000 : ℝ)*x 1 + (4482402033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088658751/2500000000 : ℝ)^8407 ≤ (16658711441583/50000000000000 : ℝ)^6359 := by
    have hnat : (1088658751 : ℕ)^8407*50000000000000^6359 ≤ 16658711441583^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088658751 2500000000 16658711441583 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115206353/5000000000 : ℝ)^8407 ≤ (16033353379959/50000000000000 : ℝ)^6359 := by
    have hnat : (2115206353 : ℕ)^8407*50000000000000^6359 ≤ 16033353379959^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115206353 5000000000 16033353379959 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4482402033/10000000000 : ℝ)^8407 ≤ (8653967585599/25000000000000 : ℝ)^6359 := by
    have hnat : (4482402033 : ℕ)^8407*25000000000000^6359 ≤ 8653967585599^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482402033 10000000000 8653967585599 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088658751/2500000000 : ℝ), (2115206353/5000000000 : ℝ), (4482402033/10000000000 : ℝ)] ![(16658711441583/50000000000000 : ℝ), (16033353379959/50000000000000 : ℝ), (8653967585599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088658751/2500000000 : ℝ)|^8407 ≤ (16658711441583/50000000000000 : ℝ)^6359
        have hw : |(1088658751/2500000000 : ℝ)|=(1088658751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2115206353/5000000000 : ℝ)|^8407 ≤ (16033353379959/50000000000000 : ℝ)^6359
        have hw : |(2115206353/5000000000 : ℝ)|=(2115206353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4482402033/10000000000 : ℝ)|^8407 ≤ (8653967585599/25000000000000 : ℝ)^6359
        have hw : |(4482402033/10000000000 : ℝ)|=(4482402033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s7_4 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2132923577/10000000000 : ℝ)*x 0 + (2633571327/5000000000 : ℝ)*x 1 + (2695702867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132923577/10000000000 : ℝ)^8407 ≤ (6483849470457/50000000000000 : ℝ)^6359 := by
    have hnat : (2132923577 : ℕ)^8407*50000000000000^6359 ≤ 6483849470457^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132923577 10000000000 6483849470457 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633571327/5000000000 : ℝ)^8407 ≤ (42845444773453/100000000000000 : ℝ)^6359 := by
    have hnat : (2633571327 : ℕ)^8407*100000000000000^6359 ≤ 42845444773453^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633571327 5000000000 42845444773453 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695702867/5000000000 : ℝ)^8407 ≤ (22093428137721/50000000000000 : ℝ)^6359 := by
    have hnat : (2695702867 : ℕ)^8407*50000000000000^6359 ≤ 22093428137721^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695702867 5000000000 22093428137721 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2132923577/10000000000 : ℝ), (2633571327/5000000000 : ℝ), (2695702867/5000000000 : ℝ)] ![(6483849470457/50000000000000 : ℝ), (42845444773453/100000000000000 : ℝ), (22093428137721/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2132923577/10000000000 : ℝ)|^8407 ≤ (6483849470457/50000000000000 : ℝ)^6359
        have hw : |(-2132923577/10000000000 : ℝ)|=(2132923577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633571327/5000000000 : ℝ)|^8407 ≤ (42845444773453/100000000000000 : ℝ)^6359
        have hw : |(2633571327/5000000000 : ℝ)|=(2633571327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695702867/5000000000 : ℝ)|^8407 ≤ (22093428137721/50000000000000 : ℝ)^6359
        have hw : |(2695702867/5000000000 : ℝ)|=(2695702867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s7_5 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062529279/2000000000 : ℝ)*x 0 + (-2071671911/10000000000 : ℝ)*x 1 + (1078281147/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062529279/2000000000 : ℝ)^8407 ≤ (8667096944937/20000000000000 : ℝ)^6359 := by
    have hnat : (1062529279 : ℕ)^8407*20000000000000^6359 ≤ 8667096944937^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062529279 2000000000 8667096944937 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071671911/10000000000 : ℝ)^8407 ≤ (12477658979851/100000000000000 : ℝ)^6359 := by
    have hnat : (2071671911 : ℕ)^8407*100000000000000^6359 ≤ 12477658979851^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071671911 10000000000 12477658979851 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078281147/2000000000 : ℝ)^8407 ≤ (22093428143139/50000000000000 : ℝ)^6359 := by
    have hnat : (1078281147 : ℕ)^8407*50000000000000^6359 ≤ 22093428143139^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078281147 2000000000 22093428143139 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062529279/2000000000 : ℝ), (-2071671911/10000000000 : ℝ), (1078281147/2000000000 : ℝ)] ![(8667096944937/20000000000000 : ℝ), (12477658979851/100000000000000 : ℝ), (22093428143139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062529279/2000000000 : ℝ)|^8407 ≤ (8667096944937/20000000000000 : ℝ)^6359
        have hw : |(1062529279/2000000000 : ℝ)|=(1062529279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2071671911/10000000000 : ℝ)|^8407 ≤ (12477658979851/100000000000000 : ℝ)^6359
        have hw : |(-2071671911/10000000000 : ℝ)|=(2071671911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078281147/2000000000 : ℝ)|^8407 ≤ (22093428143139/50000000000000 : ℝ)^6359
        have hw : |(1078281147/2000000000 : ℝ)|=(1078281147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s7_6 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656323197/5000000000 : ℝ)*x 0 + (1078281147/2000000000 : ℝ)*x 1 + (-258958989/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656323197/5000000000 : ℝ)^8407 ≤ (43335484713901/100000000000000 : ℝ)^6359 := by
    have hnat : (2656323197 : ℕ)^8407*100000000000000^6359 ≤ 43335484713901^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656323197 5000000000 43335484713901 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078281147/2000000000 : ℝ)^8407 ≤ (22093428143139/50000000000000 : ℝ)^6359 := by
    have hnat : (1078281147 : ℕ)^8407*50000000000000^6359 ≤ 22093428143139^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078281147 2000000000 22093428143139 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258958989/1250000000 : ℝ)^8407 ≤ (6238829493907/50000000000000 : ℝ)^6359 := by
    have hnat : (258958989 : ℕ)^8407*50000000000000^6359 ≤ 6238829493907^6359*1250000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258958989 1250000000 6238829493907 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656323197/5000000000 : ℝ), (1078281147/2000000000 : ℝ), (-258958989/1250000000 : ℝ)] ![(43335484713901/100000000000000 : ℝ), (22093428143139/50000000000000 : ℝ), (6238829493907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656323197/5000000000 : ℝ)|^8407 ≤ (43335484713901/100000000000000 : ℝ)^6359
        have hw : |(2656323197/5000000000 : ℝ)|=(2656323197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078281147/2000000000 : ℝ)|^8407 ≤ (22093428143139/50000000000000 : ℝ)^6359
        have hw : |(1078281147/2000000000 : ℝ)|=(1078281147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258958989/1250000000 : ℝ)|^8407 ≤ (6238829493907/50000000000000 : ℝ)^6359
        have hw : |(-258958989/1250000000 : ℝ)|=(258958989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s7_7 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177318517/5000000000 : ℝ)*x 0 + (2240884711/5000000000 : ℝ)*x 1 + (4231055137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177318517/5000000000 : ℝ)^8407 ≤ (333174434169/1000000000000 : ℝ)^6359 := by
    have hnat : (2177318517 : ℕ)^8407*1000000000000^6359 ≤ 333174434169^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177318517 5000000000 333174434169 1000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2240884711/5000000000 : ℝ)^8407 ≤ (17304705832889/50000000000000 : ℝ)^6359 := by
    have hnat : (2240884711 : ℕ)^8407*50000000000000^6359 ≤ 17304705832889^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240884711 5000000000 17304705832889 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231055137/10000000000 : ℝ)^8407 ≤ (32073144907889/100000000000000 : ℝ)^6359 := by
    have hnat : (4231055137 : ℕ)^8407*100000000000000^6359 ≤ 32073144907889^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231055137 10000000000 32073144907889 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177318517/5000000000 : ℝ), (2240884711/5000000000 : ℝ), (4231055137/10000000000 : ℝ)] ![(333174434169/1000000000000 : ℝ), (17304705832889/50000000000000 : ℝ), (32073144907889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177318517/5000000000 : ℝ)|^8407 ≤ (333174434169/1000000000000 : ℝ)^6359
        have hw : |(2177318517/5000000000 : ℝ)|=(2177318517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2240884711/5000000000 : ℝ)|^8407 ≤ (17304705832889/50000000000000 : ℝ)^6359
        have hw : |(2240884711/5000000000 : ℝ)|=(2240884711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231055137/10000000000 : ℝ)|^8407 ≤ (32073144907889/100000000000000 : ℝ)^6359
        have hw : |(4231055137/10000000000 : ℝ)|=(4231055137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s7_8 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1931903/312500000 : ℝ)*x 0 + (5914338739/10000000000 : ℝ)*x 1 + (184824563/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1931903/312500000 : ℝ)^8407 ≤ (120154826701/100000000000000 : ℝ)^6359 := by
    have hnat : (1931903 : ℕ)^8407*100000000000000^6359 ≤ 120154826701^6359*312500000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931903 312500000 120154826701 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5914338739/10000000000 : ℝ)^8407 ≤ (49939658702229/100000000000000 : ℝ)^6359 := by
    have hnat : (5914338739 : ℕ)^8407*100000000000000^6359 ≤ 49939658702229^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5914338739 10000000000 49939658702229 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (184824563/312500000 : ℝ)^8407 ≤ (4994018646903/10000000000000 : ℝ)^6359 := by
    have hnat : (184824563 : ℕ)^8407*10000000000000^6359 ≤ 4994018646903^6359*312500000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184824563 312500000 4994018646903 10000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1931903/312500000 : ℝ), (5914338739/10000000000 : ℝ), (184824563/312500000 : ℝ)] ![(120154826701/100000000000000 : ℝ), (49939658702229/100000000000000 : ℝ), (4994018646903/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1931903/312500000 : ℝ)|^8407 ≤ (120154826701/100000000000000 : ℝ)^6359
        have hw : |(-1931903/312500000 : ℝ)|=(1931903/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5914338739/10000000000 : ℝ)|^8407 ≤ (49939658702229/100000000000000 : ℝ)^6359
        have hw : |(5914338739/10000000000 : ℝ)|=(5914338739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(184824563/312500000 : ℝ)|^8407 ≤ (4994018646903/10000000000000 : ℝ)^6359
        have hw : |(184824563/312500000 : ℝ)|=(184824563/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1214_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (143/1250 : ℝ)*pair X i i ≤ pair X i h) :
    (2861/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1409/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (143/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (143/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (143/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (143/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (143/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (143/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (143/1250 : ℝ) ^ (4203/1024 : ℝ) ≤ (6827897262260119/50000000000000000000 : ℝ) := by
    have hpowers : (143/1250 : ℝ)^4203 ≤ (6827897262260119/50000000000000000000 : ℝ)^1024 := by
      have hnat : (143 : ℕ)^4203*50000000000000000000^1024 ≤ 6827897262260119^1024*1250^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        143 1250 6827897262260119 50000000000000000000 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (143/1250 : ℝ)) (X := (6827897262260119/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2819/20000 : ℝ) ^ (4203/1024 : ℝ) ≤ (16081045249651249/50000000000000000000 : ℝ) := by
    have hpowers : (2819/20000 : ℝ)^4203 ≤ (16081045249651249/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2819 : ℕ)^4203*50000000000000000000^1024 ≤ 16081045249651249^1024*20000^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2819 20000 16081045249651249 50000000000000000000 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2819/20000 : ℝ)) (X := (16081045249651249/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006827897262260119/25000000000000000000 : ℝ) ≤ (10000665338543833/10000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (25006827897262260119/25000000000000000000 : ℝ)^1024 ≤ (10000665338543833/10000000000000000 : ℝ)^4203 := by
      have hnat : (25006827897262260119 : ℕ)^1024*10000000000000000^4203 ≤ 10000665338543833^4203*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006827897262260119 25000000000000000000 10000665338543833 10000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000665338543833/10000000000000000 : ℝ)) (X := (25006827897262260119/25000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252863617813988921/6250000000000000000 : ℝ) ≤ (10001116092952821/10000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (6252863617813988921/6250000000000000000 : ℝ)^1024 ≤ (10001116092952821/10000000000000000 : ℝ)^4203 := by
      have hnat : (6252863617813988921 : ℕ)^1024*10000000000000000^4203 ≤ 10001116092952821^4203*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252863617813988921 6250000000000000000 10001116092952821 10000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001116092952821/10000000000000000 : ℝ)) (X := (6252863617813988921/6250000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016081045249651249/25000000000000000000 : ℝ) ≤ (10001566847361809/10000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (25016081045249651249/25000000000000000000 : ℝ)^1024 ≤ (10001566847361809/10000000000000000 : ℝ)^4203 := by
      have hnat : (25016081045249651249 : ℕ)^1024*10000000000000000^4203 ≤ 10001566847361809^4203*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016081045249651249 25000000000000000000 10001566847361809 10000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001566847361809/10000000000000000 : ℝ)) (X := (25016081045249651249/25000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6827897262260119/50000000000000000000 : ℝ) ≤ ((1061658128518249247/1062000000000000000 : ℝ)+2*(112688602247/66375000000000 : ℝ)*(143/1250 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (1061658128518249247/1062000000000000000 : ℝ)+2*(112688602247/66375000000000 : ℝ)*(143/1250 : ℝ)=(10000665338543833/10000000000000000 : ℝ) by norm_num, show 1+2*(6827897262260119/50000000000000000000 : ℝ)=(25006827897262260119/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16081045249651249/50000000000000000000 : ℝ)+(6827897262260119/50000000000000000000 : ℝ) ≤ ((1061658128518249247/1062000000000000000 : ℝ)+(112688602247/66375000000000 : ℝ)*((2819/20000 : ℝ)+(143/1250 : ℝ)))^(4203/1024 : ℝ) := by
    rw [show (1061658128518249247/1062000000000000000 : ℝ)+(112688602247/66375000000000 : ℝ)*((2819/20000 : ℝ)+(143/1250 : ℝ))=(10001116092952821/10000000000000000 : ℝ) by norm_num, show 1+(16081045249651249/50000000000000000000 : ℝ)+(6827897262260119/50000000000000000000 : ℝ)=(6252863617813988921/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16081045249651249/50000000000000000000 : ℝ) ≤ ((1061658128518249247/1062000000000000000 : ℝ)+2*(112688602247/66375000000000 : ℝ)*(2819/20000 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (1061658128518249247/1062000000000000000 : ℝ)+2*(112688602247/66375000000000 : ℝ)*(2819/20000 : ℝ)=(10001566847361809/10000000000000000 : ℝ) by norm_num, show 1+2*(16081045249651249/50000000000000000000 : ℝ)=(25016081045249651249/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1061658128518249247/1062000000000000000 : ℝ)*(X 1 0+X 2 0)+(112688602247/66375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (143/1250 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (1061658128518249247/1062000000000000000 : ℝ)) (alpha := (112688602247/66375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1061658128518249247/1062000000000000000 : ℝ)*(X 0 1+X 2 1)+(112688602247/66375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (143/1250 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (1061658128518249247/1062000000000000000 : ℝ)) (alpha := (112688602247/66375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1061658128518249247/1062000000000000000 : ℝ)*(X 0 2+X 1 2)+(112688602247/66375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (143/1250 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (1061658128518249247/1062000000000000000 : ℝ)) (alpha := (112688602247/66375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1066459153/5000000000 : ℝ)*X 0 0+(5391723987/10000000000 : ℝ)*X 0 1+(1053365187/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672225389/5000000000 : ℝ)*X 1 0+(-219624863/1000000000 : ℝ)*X 1 1+(5266830617/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668056931/1250000000 : ℝ)*X 2 0+(526682757/1000000000 : ℝ)*X 2 1+(-2196246451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088658751/2500000000 : ℝ)*X 0 0+(2115206353/5000000000 : ℝ)*X 0 1+(4482402033/10000000000 : ℝ)*X 0 2+(1088658751/2500000000 : ℝ)*X 1 0+(2115206353/5000000000 : ℝ)*X 1 1+(4482402033/10000000000 : ℝ)*X 1 2+(1088658751/2500000000 : ℝ)*X 2 0+(2115206353/5000000000 : ℝ)*X 2 1+(4482402033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2132923577/10000000000 : ℝ)*X 0 0+(2633571327/5000000000 : ℝ)*X 0 1+(2695702867/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062529279/2000000000 : ℝ)*X 1 0+(-2071671911/10000000000 : ℝ)*X 1 1+(1078281147/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656323197/5000000000 : ℝ)*X 2 0+(1078281147/2000000000 : ℝ)*X 2 1+(-258958989/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177318517/5000000000 : ℝ)*X 0 0+(2240884711/5000000000 : ℝ)*X 0 1+(4231055137/10000000000 : ℝ)*X 0 2+(2177318517/5000000000 : ℝ)*X 1 0+(2240884711/5000000000 : ℝ)*X 1 1+(4231055137/10000000000 : ℝ)*X 1 2+(2177318517/5000000000 : ℝ)*X 2 0+(2240884711/5000000000 : ℝ)*X 2 1+(4231055137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1931903/312500000 : ℝ)*X 0 0+(5914338739/10000000000 : ℝ)*X 0 1+(184824563/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s7_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6731907817196786444881/1475000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5925964013/100000000000000 : ℝ)*(lower2) + (26260081/10000000000000 : ℝ)*(lower3) + (1093396519/50000000000000 : ℝ)*(lower4) + (564349027/100000000000000 : ℝ)*(lower5) + (5987622753378887/100000000000000 : ℝ)*(major0) + (5987622753378887/100000000000000 : ℝ)*(major1) + (5987622753378887/100000000000000 : ℝ)*(major2) + (2001640669977359/25000000000000 : ℝ)*(sp0) + (8006790097349757/100000000000000 : ℝ)*(sp1) + (8006790097349757/100000000000000 : ℝ)*(sp2) + (49604973748037/1250000000000 : ℝ)*(sp3) + (20488852149/10000000000000 : ℝ)*(sp4) + (57357431533/100000000000000 : ℝ)*(sp7) + (1408057427/6250000000000 : ℝ)*(sp8) + (992113814318623/25000000000000 : ℝ)*(f.failure) + (8006790097349757/100000000000000 : ℝ)*(f.sum) + (48980241370061/3318750000000000000000000000 : ℝ)*base66 + (489568455182327911/106200000000000000000000000000000 : ℝ)*base68 + (773369378074272089/106200000000000000000000000000000 : ℝ)*base69 + (817788431590727911/106200000000000000000000000000000 : ℝ)*base72 + (11905172328761/3318750000000000000000000000 : ℝ)*base74 + (539622069664872089/106200000000000000000000000000000 : ℝ)*base75 + (1308789814768727911/106200000000000000000000000000000 : ℝ)*base78 + (129291670347672089/106200000000000000000000000000000 : ℝ)*base79 + (2495072208247/6637500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (914147/62500000000000000000 : ℝ)*base90 + (914147/62500000000000000000 : ℝ)*base92 + (914147/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (65402520982971885196225137/5900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (569860181/100000000000000 : ℝ)*(lower2) + (1511601/800000000000 : ℝ)*(lower3) + (17833279/3125000000000 : ℝ)*(lower4) + (189962783/100000000000000 : ℝ)*(lower5) + (6018036783805613/100000000000000 : ℝ)*(major0) + (6018036783805613/100000000000000 : ℝ)*(major1) + (6018036783805613/100000000000000 : ℝ)*(major2) + (1573812649/25000000000000 : ℝ)*(sp0) + (2232235657/50000000000000 : ℝ)*(sp3) + (16094897630021/200000000000 : ℝ)*(sp4) + (8047460238197841/100000000000000 : ℝ)*(sp5) + (8047460238197841/100000000000000 : ℝ)*(sp6) + (7790250967649/195312500000 : ℝ)*(sp7) + (1025587349/20000000000000 : ℝ)*(sp8) + (1994306479953801/50000000000000 : ℝ)*(f.failure) + (8047460238197841/100000000000000 : ℝ)*(f.sum) + (116591027488207/1659375000000000000000000000 : ℝ)*base66 + (310596359737200589/106200000000000000000000000000000 : ℝ)*base68 + (3557373129857400589/106200000000000000000000000000000 : ℝ)*base70 + (318467820476400589/106200000000000000000000000000000 : ℝ)*base72 + (20679831958669/13275000000000000000000000000 : ℝ)*base73 + (779383949721599411/106200000000000000000000000000000 : ℝ)*base75 + (1355171209762200589/106200000000000000000000000000000 : ℝ)*base78 + (613360597429199411/106200000000000000000000000000000 : ℝ)*base79 + (35316086332753/6637500000000000000000000000 : ℝ)*base82 + (613811/125000000000000000000 : ℝ)*base89 + (613811/125000000000000000000 : ℝ)*base91 + (613811/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1214_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (143/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2861/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1214_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1214_s8_0 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2132925009/10000000000 : ℝ)*x 0 + (2695838737/5000000000 : ℝ)*x 1 + (5266867791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132925009/10000000000 : ℝ)^8407 ≤ (2593542090223/20000000000000 : ℝ)^6359 := by
    have hnat : (2132925009 : ℕ)^8407*20000000000000^6359 ≤ 2593542090223^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132925009 10000000000 2593542090223 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695838737/5000000000 : ℝ)^8407 ≤ (5523725087479/12500000000000 : ℝ)^6359 := by
    have hnat : (2695838737 : ℕ)^8407*12500000000000^6359 ≤ 5523725087479^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695838737 5000000000 5523725087479 12500000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266867791/10000000000 : ℝ)^8407 ≤ (8568497768303/20000000000000 : ℝ)^6359 := by
    have hnat : (5266867791 : ℕ)^8407*20000000000000^6359 ≤ 8568497768303^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266867791 10000000000 8568497768303 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2132925009/10000000000 : ℝ), (2695838737/5000000000 : ℝ), (5266867791/10000000000 : ℝ)] ![(2593542090223/20000000000000 : ℝ), (5523725087479/12500000000000 : ℝ), (8568497768303/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2132925009/10000000000 : ℝ)|^8407 ≤ (2593542090223/20000000000000 : ℝ)^6359
        have hw : |(-2132925009/10000000000 : ℝ)|=(2132925009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695838737/5000000000 : ℝ)|^8407 ≤ (5523725087479/12500000000000 : ℝ)^6359
        have hw : |(2695838737/5000000000 : ℝ)|=(2695838737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266867791/10000000000 : ℝ)|^8407 ≤ (8568497768303/20000000000000 : ℝ)^6359
        have hw : |(5266867791/10000000000 : ℝ)|=(5266867791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s8_1 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344440729/10000000000 : ℝ)*x 0 + (-549053139/2500000000 : ℝ)*x 1 + (5266867931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344440729/10000000000 : ℝ)^8407 ≤ (682479512973/1562500000000 : ℝ)^6359 := by
    have hnat : (5344440729 : ℕ)^8407*1562500000000^6359 ≤ 682479512973^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344440729 10000000000 682479512973 1562500000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549053139/2500000000 : ℝ)^8407 ≤ (6739410402801/50000000000000 : ℝ)^6359 := by
    have hnat : (549053139 : ℕ)^8407*50000000000000^6359 ≤ 6739410402801^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549053139 2500000000 6739410402801 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266867931/10000000000 : ℝ)^8407 ≤ (42842490347091/100000000000000 : ℝ)^6359 := by
    have hnat : (5266867931 : ℕ)^8407*100000000000000^6359 ≤ 42842490347091^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266867931 10000000000 42842490347091 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344440729/10000000000 : ℝ), (-549053139/2500000000 : ℝ), (5266867931/10000000000 : ℝ)] ![(682479512973/1562500000000 : ℝ), (6739410402801/50000000000000 : ℝ), (42842490347091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344440729/10000000000 : ℝ)|^8407 ≤ (682479512973/1562500000000 : ℝ)^6359
        have hw : |(5344440729/10000000000 : ℝ)|=(5344440729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-549053139/2500000000 : ℝ)|^8407 ≤ (6739410402801/50000000000000 : ℝ)^6359
        have hw : |(-549053139/2500000000 : ℝ)|=(549053139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266867931/10000000000 : ℝ)|^8407 ≤ (42842490347091/100000000000000 : ℝ)^6359
        have hw : |(5266867931/10000000000 : ℝ)|=(5266867931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s8_2 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267222037/500000000 : ℝ)*x 0 + (5266867931/10000000000 : ℝ)*x 1 + (-2196212541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267222037/500000000 : ℝ)^8407 ≤ (21839344474563/50000000000000 : ℝ)^6359 := by
    have hnat : (267222037 : ℕ)^8407*50000000000000^6359 ≤ 21839344474563^6359*500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267222037 500000000 21839344474563 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266867931/10000000000 : ℝ)^8407 ≤ (42842490347091/100000000000000 : ℝ)^6359 := by
    have hnat : (5266867931 : ℕ)^8407*100000000000000^6359 ≤ 42842490347091^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266867931 10000000000 42842490347091 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2196212541/10000000000 : ℝ)^8407 ≤ (6739410341947/50000000000000 : ℝ)^6359 := by
    have hnat : (2196212541 : ℕ)^8407*50000000000000^6359 ≤ 6739410341947^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196212541 10000000000 6739410341947 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267222037/500000000 : ℝ), (5266867931/10000000000 : ℝ), (-2196212541/10000000000 : ℝ)] ![(21839344474563/50000000000000 : ℝ), (42842490347091/100000000000000 : ℝ), (6739410341947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267222037/500000000 : ℝ)|^8407 ≤ (21839344474563/50000000000000 : ℝ)^6359
        have hw : |(267222037/500000000 : ℝ)|=(267222037/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266867931/10000000000 : ℝ)|^8407 ≤ (42842490347091/100000000000000 : ℝ)^6359
        have hw : |(5266867931/10000000000 : ℝ)|=(5266867931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2196212541/10000000000 : ℝ)|^8407 ≤ (6739410341947/50000000000000 : ℝ)^6359
        have hw : |(-2196212541/10000000000 : ℝ)|=(2196212541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s8_3 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177314789/5000000000 : ℝ)*x 0 + (846100487/2000000000 : ℝ)*x 1 + (560289917/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177314789/5000000000 : ℝ)^8407 ≤ (1041167749951/3125000000000 : ℝ)^6359 := by
    have hnat : (2177314789 : ℕ)^8407*3125000000000^6359 ≤ 1041167749951^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177314789 5000000000 1041167749951 3125000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846100487/2000000000 : ℝ)^8407 ≤ (8016901490941/25000000000000 : ℝ)^6359 := by
    have hnat : (846100487 : ℕ)^8407*25000000000000^6359 ≤ 8016901490941^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846100487 2000000000 8016901490941 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560289917/1250000000 : ℝ)^8407 ≤ (34615026026169/100000000000000 : ℝ)^6359 := by
    have hnat : (560289917 : ℕ)^8407*100000000000000^6359 ≤ 34615026026169^6359*1250000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560289917 1250000000 34615026026169 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177314789/5000000000 : ℝ), (846100487/2000000000 : ℝ), (560289917/1250000000 : ℝ)] ![(1041167749951/3125000000000 : ℝ), (8016901490941/25000000000000 : ℝ), (34615026026169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177314789/5000000000 : ℝ)|^8407 ≤ (1041167749951/3125000000000 : ℝ)^6359
        have hw : |(2177314789/5000000000 : ℝ)|=(2177314789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846100487/2000000000 : ℝ)|^8407 ≤ (8016901490941/25000000000000 : ℝ)^6359
        have hw : |(846100487/2000000000 : ℝ)|=(846100487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(560289917/1250000000 : ℝ)|^8407 ≤ (34615026026169/100000000000000 : ℝ)^6359
        have hw : |(560289917/1250000000 : ℝ)|=(560289917/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s8_4 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2132929683/10000000000 : ℝ)*x 0 + (658397761/1250000000 : ℝ)*x 1 + (1078272413/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132929683/10000000000 : ℝ)^8407 ≤ (12967748020043/100000000000000 : ℝ)^6359 := by
    have hnat : (2132929683 : ℕ)^8407*100000000000000^6359 ≤ 12967748020043^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132929683 10000000000 12967748020043 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658397761/1250000000 : ℝ)^8407 ≤ (669466700917/1562500000000 : ℝ)^6359 := by
    have hnat : (658397761 : ℕ)^8407*1562500000000^6359 ≤ 669466700917^6359*1250000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658397761 1250000000 669466700917 1562500000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078272413/2000000000 : ℝ)^8407 ≤ (44186383106761/100000000000000 : ℝ)^6359 := by
    have hnat : (1078272413 : ℕ)^8407*100000000000000^6359 ≤ 44186383106761^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078272413 2000000000 44186383106761 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2132929683/10000000000 : ℝ), (658397761/1250000000 : ℝ), (1078272413/2000000000 : ℝ)] ![(12967748020043/100000000000000 : ℝ), (669466700917/1562500000000 : ℝ), (44186383106761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2132929683/10000000000 : ℝ)|^8407 ≤ (12967748020043/100000000000000 : ℝ)^6359
        have hw : |(-2132929683/10000000000 : ℝ)|=(2132929683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658397761/1250000000 : ℝ)|^8407 ≤ (669466700917/1562500000000 : ℝ)^6359
        have hw : |(658397761/1250000000 : ℝ)|=(658397761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078272413/2000000000 : ℝ)|^8407 ≤ (44186383106761/100000000000000 : ℝ)^6359
        have hw : |(1078272413/2000000000 : ℝ)|=(1078272413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s8_5 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312655951/10000000000 : ℝ)*x 0 + (-258964799/1250000000 : ℝ)*x 1 + (1078272413/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312655951/10000000000 : ℝ)^8407 ≤ (43335587777827/100000000000000 : ℝ)^6359 := by
    have hnat : (5312655951 : ℕ)^8407*100000000000000^6359 ≤ 43335587777827^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312655951 10000000000 43335587777827 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258964799/1250000000 : ℝ)^8407 ≤ (6239014549429/50000000000000 : ℝ)^6359 := by
    have hnat : (258964799 : ℕ)^8407*50000000000000^6359 ≤ 6239014549429^6359*1250000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258964799 1250000000 6239014549429 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078272413/2000000000 : ℝ)^8407 ≤ (44186383106761/100000000000000 : ℝ)^6359 := by
    have hnat : (1078272413 : ℕ)^8407*100000000000000^6359 ≤ 44186383106761^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078272413 2000000000 44186383106761 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312655951/10000000000 : ℝ), (-258964799/1250000000 : ℝ), (1078272413/2000000000 : ℝ)] ![(43335587777827/100000000000000 : ℝ), (6239014549429/50000000000000 : ℝ), (44186383106761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312655951/10000000000 : ℝ)|^8407 ≤ (43335587777827/100000000000000 : ℝ)^6359
        have hw : |(5312655951/10000000000 : ℝ)|=(5312655951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-258964799/1250000000 : ℝ)|^8407 ≤ (6239014549429/50000000000000 : ℝ)^6359
        have hw : |(-258964799/1250000000 : ℝ)|=(258964799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078272413/2000000000 : ℝ)|^8407 ≤ (44186383106761/100000000000000 : ℝ)^6359
        have hw : |(1078272413/2000000000 : ℝ)|=(1078272413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s8_6 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312655951/10000000000 : ℝ)*x 0 + (1078272413/2000000000 : ℝ)*x 1 + (-258964799/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312655951/10000000000 : ℝ)^8407 ≤ (43335587777827/100000000000000 : ℝ)^6359 := by
    have hnat : (5312655951 : ℕ)^8407*100000000000000^6359 ≤ 43335587777827^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312655951 10000000000 43335587777827 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078272413/2000000000 : ℝ)^8407 ≤ (44186383106761/100000000000000 : ℝ)^6359 := by
    have hnat : (1078272413 : ℕ)^8407*100000000000000^6359 ≤ 44186383106761^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078272413 2000000000 44186383106761 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258964799/1250000000 : ℝ)^8407 ≤ (6239014549429/50000000000000 : ℝ)^6359 := by
    have hnat : (258964799 : ℕ)^8407*50000000000000^6359 ≤ 6239014549429^6359*1250000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258964799 1250000000 6239014549429 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312655951/10000000000 : ℝ), (1078272413/2000000000 : ℝ), (-258964799/1250000000 : ℝ)] ![(43335587777827/100000000000000 : ℝ), (44186383106761/100000000000000 : ℝ), (6239014549429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312655951/10000000000 : ℝ)|^8407 ≤ (43335587777827/100000000000000 : ℝ)^6359
        have hw : |(5312655951/10000000000 : ℝ)|=(5312655951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078272413/2000000000 : ℝ)|^8407 ≤ (44186383106761/100000000000000 : ℝ)^6359
        have hw : |(1078272413/2000000000 : ℝ)|=(1078272413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258964799/1250000000 : ℝ)|^8407 ≤ (6239014549429/50000000000000 : ℝ)^6359
        have hw : |(-258964799/1250000000 : ℝ)|=(258964799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s8_7 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4354639137/10000000000 : ℝ)*x 0 + (70026333/156250000 : ℝ)*x 1 + (4231138697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354639137/10000000000 : ℝ)^8407 ≤ (33317464689043/100000000000000 : ℝ)^6359 := by
    have hnat : (4354639137 : ℕ)^8407*100000000000000^6359 ≤ 33317464689043^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354639137 10000000000 33317464689043 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70026333/156250000 : ℝ)^8407 ≤ (34608552962243/100000000000000 : ℝ)^6359 := by
    have hnat : (70026333 : ℕ)^8407*100000000000000^6359 ≤ 34608552962243^6359*156250000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70026333 156250000 34608552962243 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231138697/10000000000 : ℝ)^8407 ≤ (1002311947841/3125000000000 : ℝ)^6359 := by
    have hnat : (4231138697 : ℕ)^8407*3125000000000^6359 ≤ 1002311947841^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231138697 10000000000 1002311947841 3125000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354639137/10000000000 : ℝ), (70026333/156250000 : ℝ), (4231138697/10000000000 : ℝ)] ![(33317464689043/100000000000000 : ℝ), (34608552962243/100000000000000 : ℝ), (1002311947841/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354639137/10000000000 : ℝ)|^8407 ≤ (33317464689043/100000000000000 : ℝ)^6359
        have hw : |(4354639137/10000000000 : ℝ)|=(4354639137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(70026333/156250000 : ℝ)|^8407 ≤ (34608552962243/100000000000000 : ℝ)^6359
        have hw : |(70026333/156250000 : ℝ)|=(70026333/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231138697/10000000000 : ℝ)|^8407 ≤ (1002311947841/3125000000000 : ℝ)^6359
        have hw : |(4231138697/10000000000 : ℝ)|=(4231138697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1214_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2861/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2289/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14089/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1409/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2861/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2861/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2861/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2861/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2861/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2861/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2861/25000 : ℝ) ^ (4203/1024 : ℝ) ≤ (13675403101521849/100000000000000000000 : ℝ) := by
    have hpowers : (2861/25000 : ℝ)^4203 ≤ (13675403101521849/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2861 : ℕ)^4203*100000000000000000000^1024 ≤ 13675403101521849^1024*25000^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2861 25000 13675403101521849 100000000000000000000 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2861/25000 : ℝ)) (X := (13675403101521849/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1409/10000 : ℝ) ^ (4203/1024 : ℝ) ≤ (32115287952942239/100000000000000000000 : ℝ) := by
    have hpowers : (1409/10000 : ℝ)^4203 ≤ (32115287952942239/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1409 : ℕ)^4203*100000000000000000000^1024 ≤ 32115287952942239^1024*10000^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409 10000 32115287952942239 100000000000000000000 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1409/10000 : ℝ)) (X := (32115287952942239/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013675403101521849/50000000000000000000 : ℝ) ≤ (10000666293815449/10000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (50013675403101521849/50000000000000000000 : ℝ)^1024 ≤ (10000666293815449/10000000000000000 : ℝ)^4203 := by
      have hnat : (50013675403101521849 : ℕ)^1024*10000000000000000^4203 ≤ 10000666293815449^4203*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013675403101521849 50000000000000000000 10000666293815449 10000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000666293815449/10000000000000000 : ℝ)) (X := (50013675403101521849/50000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505723836381808011/12500000000000000000 : ℝ) ≤ (2500278857660159/2500000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (12505723836381808011/12500000000000000000 : ℝ)^1024 ≤ (2500278857660159/2500000000000000 : ℝ)^4203 := by
      have hnat : (12505723836381808011 : ℕ)^1024*2500000000000000^4203 ≤ 2500278857660159^4203*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505723836381808011 12500000000000000000 2500278857660159 2500000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500278857660159/2500000000000000 : ℝ)) (X := (12505723836381808011/12500000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032115287952942239/50000000000000000000 : ℝ) ≤ (10001564567465823/10000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (50032115287952942239/50000000000000000000 : ℝ)^1024 ≤ (10001564567465823/10000000000000000 : ℝ)^4203 := by
      have hnat : (50032115287952942239 : ℕ)^1024*10000000000000000^4203 ≤ 10001564567465823^4203*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032115287952942239 50000000000000000000 10001564567465823 10000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001564567465823/10000000000000000 : ℝ)) (X := (50032115287952942239/50000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13675403101521849/100000000000000000000 : ℝ) ≤ ((13225741584890398999/13230000000000000000 : ℝ)+2*(449136825187/264600000000000 : ℝ)*(2861/25000 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (13225741584890398999/13230000000000000000 : ℝ)+2*(449136825187/264600000000000 : ℝ)*(2861/25000 : ℝ)=(10000666293815449/10000000000000000 : ℝ) by norm_num, show 1+2*(13675403101521849/100000000000000000000 : ℝ)=(50013675403101521849/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32115287952942239/100000000000000000000 : ℝ)+(13675403101521849/100000000000000000000 : ℝ) ≤ ((13225741584890398999/13230000000000000000 : ℝ)+(449136825187/264600000000000 : ℝ)*((1409/10000 : ℝ)+(2861/25000 : ℝ)))^(4203/1024 : ℝ) := by
    rw [show (13225741584890398999/13230000000000000000 : ℝ)+(449136825187/264600000000000 : ℝ)*((1409/10000 : ℝ)+(2861/25000 : ℝ))=(2500278857660159/2500000000000000 : ℝ) by norm_num, show 1+(32115287952942239/100000000000000000000 : ℝ)+(13675403101521849/100000000000000000000 : ℝ)=(12505723836381808011/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32115287952942239/100000000000000000000 : ℝ) ≤ ((13225741584890398999/13230000000000000000 : ℝ)+2*(449136825187/264600000000000 : ℝ)*(1409/10000 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (13225741584890398999/13230000000000000000 : ℝ)+2*(449136825187/264600000000000 : ℝ)*(1409/10000 : ℝ)=(10001564567465823/10000000000000000 : ℝ) by norm_num, show 1+2*(32115287952942239/100000000000000000000 : ℝ)=(50032115287952942239/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13225741584890398999/13230000000000000000 : ℝ)*(X 1 0+X 2 0)+(449136825187/264600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (2861/25000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (13225741584890398999/13230000000000000000 : ℝ)) (alpha := (449136825187/264600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13225741584890398999/13230000000000000000 : ℝ)*(X 0 1+X 2 1)+(449136825187/264600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (2861/25000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (13225741584890398999/13230000000000000000 : ℝ)) (alpha := (449136825187/264600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13225741584890398999/13230000000000000000 : ℝ)*(X 0 2+X 1 2)+(449136825187/264600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (2861/25000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (13225741584890398999/13230000000000000000 : ℝ)) (alpha := (449136825187/264600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2132925009/10000000000 : ℝ)*X 0 0+(2695838737/5000000000 : ℝ)*X 0 1+(5266867791/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344440729/10000000000 : ℝ)*X 1 0+(-549053139/2500000000 : ℝ)*X 1 1+(5266867931/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267222037/500000000 : ℝ)*X 2 0+(5266867931/10000000000 : ℝ)*X 2 1+(-2196212541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2177314789/5000000000 : ℝ)*X 0 0+(846100487/2000000000 : ℝ)*X 0 1+(560289917/1250000000 : ℝ)*X 0 2+(2177314789/5000000000 : ℝ)*X 1 0+(846100487/2000000000 : ℝ)*X 1 1+(560289917/1250000000 : ℝ)*X 1 2+(2177314789/5000000000 : ℝ)*X 2 0+(846100487/2000000000 : ℝ)*X 2 1+(560289917/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2132929683/10000000000 : ℝ)*X 0 0+(658397761/1250000000 : ℝ)*X 0 1+(1078272413/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312655951/10000000000 : ℝ)*X 1 0+(-258964799/1250000000 : ℝ)*X 1 1+(1078272413/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312655951/10000000000 : ℝ)*X 2 0+(1078272413/2000000000 : ℝ)*X 2 1+(-258964799/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4354639137/10000000000 : ℝ)*X 0 0+(70026333/156250000 : ℝ)*X 0 1+(4231138697/10000000000 : ℝ)*X 0 2+(4354639137/10000000000 : ℝ)*X 1 0+(70026333/156250000 : ℝ)*X 1 1+(4231138697/10000000000 : ℝ)*X 1 2+(4354639137/10000000000 : ℝ)*X 2 0+(70026333/156250000 : ℝ)*X 2 1+(4231138697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78054945887942750569298973/12250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (229045499/20000000000000 : ℝ)*(base19) + (287955377/25000000000000 : ℝ)*(base23) + (121199617/100000000000000 : ℝ)*(upper3) + (264469/5000000000000 : ℝ)*(upper4) + (141375287/100000000000000 : ℝ)*(upper5) + (2995865211222081/50000000000000 : ℝ)*(major0) + (2995865211222081/50000000000000 : ℝ)*(major1) + (2995865211222081/50000000000000 : ℝ)*(major2) + (8012240093850757/100000000000000 : ℝ)*(sp0) + (1001535220467041/12500000000000 : ℝ)*(sp1) + (2003070439285579/25000000000000 : ℝ)*(sp2) + (7942317225459/200000000000 : ℝ)*(sp3) + (21407556533/50000000000000 : ℝ)*(sp4) + (19110800577/100000000000000 : ℝ)*(sp7) + (992794430882519/25000000000000 : ℝ)*(f.failure) + (8012282908963823/100000000000000 : ℝ)*(f.sum) + (1505490266149/245000000000000000000000000 : ℝ)*base66 + (48626298854648429/3500000000000000000000000000000 : ℝ)*base68 + (64172186190648429/3500000000000000000000000000000 : ℝ)*base70 + (81314790393148429/3500000000000000000000000000000 : ℝ)*base72 + (2826851215659/245000000000000000000000000 : ℝ)*base74 + (73833545209148429/3500000000000000000000000000000 : ℝ)*base76 + (56913667941148429/3500000000000000000000000000000 : ℝ)*base78 + (31051953849648429/3500000000000000000000000000000 : ℝ)*base80 + (86423741297/30625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (125709/62500000000000000000 : ℝ)*base89 + (125709/62500000000000000000 : ℝ)*base91 + (125709/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1014915763437572786009/147000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1243122439/100000000000000 : ℝ)*(base19) + (676087263/50000000000000 : ℝ)*(base23) + (434187927/100000000000000 : ℝ)*(lower1) + (17340277/12500000000000 : ℝ)*(upper3) + (1984307/4000000000000 : ℝ)*(lower4) + (70488013/50000000000000 : ℝ)*(upper5) + (602202374066429/10000000000000 : ℝ)*(major0) + (602202374066429/10000000000000 : ℝ)*(major1) + (602202374066429/10000000000000 : ℝ)*(major2) + (2620095611/100000000000000 : ℝ)*(sp2) + (4026395915115777/50000000000000 : ℝ)*(sp4) + (1610558117421823/20000000000000 : ℝ)*(sp5) + (8052787857961417/100000000000000 : ℝ)*(sp6) + (1995627710478671/50000000000000 : ℝ)*(sp7) + (1995627710478671/50000000000000 : ℝ)*(f.failure) + (4026395915115777/50000000000000 : ℝ)*(f.sum) + (4677431225233/1323000000000000000000000000 : ℝ)*base66 + (11408425209135161/700000000000000000000000000000 : ℝ)*base68 + (1022453058735161/700000000000000000000000000000 : ℝ)*base70 + (190911820443235161/700000000000000000000000000000 : ℝ)*base72 + (7022767769329/1323000000000000000000000000 : ℝ)*base74 + (138819960515764839/700000000000000000000000000000 : ℝ)*base75 + (7058020617364839/700000000000000000000000000000 : ℝ)*base77 + (14172380255064839/700000000000000000000000000000 : ℝ)*base79 + (9356600789867/661500000000000000000000000 : ℝ)*base82 + (222619/125000000000000000000 : ℝ)*base90 + (222619/125000000000000000000 : ℝ)*base92 + (222619/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1214_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2861/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1214_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1214_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11417/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1214_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1214_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1214_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11417/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2289/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1214_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
