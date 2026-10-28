-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1104_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:02:28.825082+00:00
-- url     : https://prove2.me/submissions/9c5e7e94-08cb-4098-86da-f027a3a1054e

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
theorem support_rectangle_w1104_s6_0 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1092577729/5000000000 : ℝ)*x 0 + (5394143677/10000000000 : ℝ)*x 1 + (5264698947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092577729/5000000000 : ℝ)^8297 ≤ (530969124523/4000000000000 : ℝ)^6249 := by
    have hnat : (1092577729 : ℕ)^8297*4000000000000^6249 ≤ 530969124523^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092577729 5000000000 530969124523 4000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394143677/10000000000 : ℝ)^8297 ≤ (44062062369087/100000000000000 : ℝ)^6249 := by
    have hnat : (5394143677 : ℕ)^8297*100000000000000^6249 ≤ 44062062369087^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394143677 10000000000 44062062369087 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264698947/10000000000 : ℝ)^8297 ≤ (2133185475397/5000000000000 : ℝ)^6249 := by
    have hnat : (5264698947 : ℕ)^8297*5000000000000^6249 ≤ 2133185475397^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264698947 10000000000 2133185475397 5000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1092577729/5000000000 : ℝ), (5394143677/10000000000 : ℝ), (5264698947/10000000000 : ℝ)] ![(530969124523/4000000000000 : ℝ), (44062062369087/100000000000000 : ℝ), (2133185475397/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1092577729/5000000000 : ℝ)|^8297 ≤ (530969124523/4000000000000 : ℝ)^6249
        have hw : |(-1092577729/5000000000 : ℝ)|=(1092577729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394143677/10000000000 : ℝ)|^8297 ≤ (44062062369087/100000000000000 : ℝ)^6249
        have hw : |(5394143677/10000000000 : ℝ)|=(5394143677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264698947/10000000000 : ℝ)|^8297 ≤ (2133185475397/5000000000000 : ℝ)^6249
        have hw : |(5264698947/10000000000 : ℝ)|=(5264698947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s6_1 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344991989/10000000000 : ℝ)*x 0 + (-1125414021/5000000000 : ℝ)*x 1 + (5264698947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344991989/10000000000 : ℝ)^8297 ≤ (43529781290711/100000000000000 : ℝ)^6249 := by
    have hnat : (5344991989 : ℕ)^8297*100000000000000^6249 ≤ 43529781290711^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344991989 10000000000 43529781290711 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125414021/5000000000 : ℝ)^8297 ≤ (3451627297627/25000000000000 : ℝ)^6249 := by
    have hnat : (1125414021 : ℕ)^8297*25000000000000^6249 ≤ 3451627297627^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125414021 5000000000 3451627297627 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264698947/10000000000 : ℝ)^8297 ≤ (2133185475397/5000000000000 : ℝ)^6249 := by
    have hnat : (5264698947 : ℕ)^8297*5000000000000^6249 ≤ 2133185475397^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264698947 10000000000 2133185475397 5000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344991989/10000000000 : ℝ), (-1125414021/5000000000 : ℝ), (5264698947/10000000000 : ℝ)] ![(43529781290711/100000000000000 : ℝ), (3451627297627/25000000000000 : ℝ), (2133185475397/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344991989/10000000000 : ℝ)|^8297 ≤ (43529781290711/100000000000000 : ℝ)^6249
        have hw : |(5344991989/10000000000 : ℝ)|=(5344991989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1125414021/5000000000 : ℝ)|^8297 ≤ (3451627297627/25000000000000 : ℝ)^6249
        have hw : |(-1125414021/5000000000 : ℝ)|=(1125414021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264698947/10000000000 : ℝ)|^8297 ≤ (2133185475397/5000000000000 : ℝ)^6249
        have hw : |(5264698947/10000000000 : ℝ)|=(5264698947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s6_2 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344991989/10000000000 : ℝ)*x 0 + (5264698947/10000000000 : ℝ)*x 1 + (-1125414021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344991989/10000000000 : ℝ)^8297 ≤ (43529781290711/100000000000000 : ℝ)^6249 := by
    have hnat : (5344991989 : ℕ)^8297*100000000000000^6249 ≤ 43529781290711^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344991989 10000000000 43529781290711 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264698947/10000000000 : ℝ)^8297 ≤ (2133185475397/5000000000000 : ℝ)^6249 := by
    have hnat : (5264698947 : ℕ)^8297*5000000000000^6249 ≤ 2133185475397^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264698947 10000000000 2133185475397 5000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125414021/5000000000 : ℝ)^8297 ≤ (3451627297627/25000000000000 : ℝ)^6249 := by
    have hnat : (1125414021 : ℕ)^8297*25000000000000^6249 ≤ 3451627297627^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125414021 5000000000 3451627297627 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344991989/10000000000 : ℝ), (5264698947/10000000000 : ℝ), (-1125414021/5000000000 : ℝ)] ![(43529781290711/100000000000000 : ℝ), (2133185475397/5000000000000 : ℝ), (3451627297627/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344991989/10000000000 : ℝ)|^8297 ≤ (43529781290711/100000000000000 : ℝ)^6249
        have hw : |(5344991989/10000000000 : ℝ)|=(5344991989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264698947/10000000000 : ℝ)|^8297 ≤ (2133185475397/5000000000000 : ℝ)^6249
        have hw : |(5264698947/10000000000 : ℝ)|=(5264698947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1125414021/5000000000 : ℝ)|^8297 ≤ (3451627297627/25000000000000 : ℝ)^6249
        have hw : |(-1125414021/5000000000 : ℝ)|=(1125414021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s6_3 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1092508189/2500000000 : ℝ)*x 0 + (1061026169/2500000000 : ℝ)*x 1 + (4499713551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092508189/2500000000 : ℝ)^8297 ≤ (33316537827857/100000000000000 : ℝ)^6249 := by
    have hnat : (1092508189 : ℕ)^8297*100000000000000^6249 ≤ 33316537827857^6249*2500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092508189 2500000000 33316537827857 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061026169/2500000000 : ℝ)^8297 ≤ (32047895349607/100000000000000 : ℝ)^6249 := by
    have hnat : (1061026169 : ℕ)^8297*100000000000000^6249 ≤ 32047895349607^6249*2500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061026169 2500000000 32047895349607 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499713551/10000000000 : ℝ)^8297 ≤ (34635566804973/100000000000000 : ℝ)^6249 := by
    have hnat : (4499713551 : ℕ)^8297*100000000000000^6249 ≤ 34635566804973^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499713551 10000000000 34635566804973 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092508189/2500000000 : ℝ), (1061026169/2500000000 : ℝ), (4499713551/10000000000 : ℝ)] ![(33316537827857/100000000000000 : ℝ), (32047895349607/100000000000000 : ℝ), (34635566804973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092508189/2500000000 : ℝ)|^8297 ≤ (33316537827857/100000000000000 : ℝ)^6249
        have hw : |(1092508189/2500000000 : ℝ)|=(1092508189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061026169/2500000000 : ℝ)|^8297 ≤ (32047895349607/100000000000000 : ℝ)^6249
        have hw : |(1061026169/2500000000 : ℝ)|=(1061026169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499713551/10000000000 : ℝ)|^8297 ≤ (34635566804973/100000000000000 : ℝ)^6249
        have hw : |(4499713551/10000000000 : ℝ)|=(4499713551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s6_4 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2185160531/10000000000 : ℝ)*x 0 + (5265025829/10000000000 : ℝ)*x 1 + (5393815607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185160531/10000000000 : ℝ)^8297 ≤ (13274269029957/100000000000000 : ℝ)^6249 := by
    have hnat : (2185160531 : ℕ)^8297*100000000000000^6249 ≤ 13274269029957^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185160531 10000000000 13274269029957 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265025829/10000000000 : ℝ)^8297 ≤ (42667226659331/100000000000000 : ℝ)^6249 := by
    have hnat : (5265025829 : ℕ)^8297*100000000000000^6249 ≤ 42667226659331^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265025829 10000000000 42667226659331 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393815607/10000000000 : ℝ)^8297 ≤ (44058504294347/100000000000000 : ℝ)^6249 := by
    have hnat : (5393815607 : ℕ)^8297*100000000000000^6249 ≤ 44058504294347^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393815607 10000000000 44058504294347 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2185160531/10000000000 : ℝ), (5265025829/10000000000 : ℝ), (5393815607/10000000000 : ℝ)] ![(13274269029957/100000000000000 : ℝ), (42667226659331/100000000000000 : ℝ), (44058504294347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2185160531/10000000000 : ℝ)|^8297 ≤ (13274269029957/100000000000000 : ℝ)^6249
        have hw : |(-2185160531/10000000000 : ℝ)|=(2185160531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265025829/10000000000 : ℝ)|^8297 ≤ (42667226659331/100000000000000 : ℝ)^6249
        have hw : |(5265025829/10000000000 : ℝ)|=(5265025829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393815607/10000000000 : ℝ)|^8297 ≤ (44058504294347/100000000000000 : ℝ)^6249
        have hw : |(5393815607/10000000000 : ℝ)|=(5393815607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s6_5 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656145271/5000000000 : ℝ)*x 0 + (-2121711381/10000000000 : ℝ)*x 1 + (674226951/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656145271/5000000000 : ℝ)^8297 ≤ (43176532454867/100000000000000 : ℝ)^6249 := by
    have hnat : (2656145271 : ℕ)^8297*100000000000000^6249 ≤ 43176532454867^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656145271 5000000000 43176532454867 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2121711381/10000000000 : ℝ)^8297 ≤ (2552992645391/20000000000000 : ℝ)^6249 := by
    have hnat : (2121711381 : ℕ)^8297*20000000000000^6249 ≤ 2552992645391^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121711381 10000000000 2552992645391 20000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674226951/1250000000 : ℝ)^8297 ≤ (5507313038149/12500000000000 : ℝ)^6249 := by
    have hnat : (674226951 : ℕ)^8297*12500000000000^6249 ≤ 5507313038149^6249*1250000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674226951 1250000000 5507313038149 12500000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656145271/5000000000 : ℝ), (-2121711381/10000000000 : ℝ), (674226951/1250000000 : ℝ)] ![(43176532454867/100000000000000 : ℝ), (2552992645391/20000000000000 : ℝ), (5507313038149/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656145271/5000000000 : ℝ)|^8297 ≤ (43176532454867/100000000000000 : ℝ)^6249
        have hw : |(2656145271/5000000000 : ℝ)|=(2656145271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2121711381/10000000000 : ℝ)|^8297 ≤ (2552992645391/20000000000000 : ℝ)^6249
        have hw : |(-2121711381/10000000000 : ℝ)|=(2121711381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674226951/1250000000 : ℝ)|^8297 ≤ (5507313038149/12500000000000 : ℝ)^6249
        have hw : |(674226951/1250000000 : ℝ)|=(674226951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s6_6 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312290541/10000000000 : ℝ)*x 0 + (674226951/1250000000 : ℝ)*x 1 + (-2121711381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312290541/10000000000 : ℝ)^8297 ≤ (10794133111019/25000000000000 : ℝ)^6249 := by
    have hnat : (5312290541 : ℕ)^8297*25000000000000^6249 ≤ 10794133111019^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312290541 10000000000 10794133111019 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674226951/1250000000 : ℝ)^8297 ≤ (5507313038149/12500000000000 : ℝ)^6249 := by
    have hnat : (674226951 : ℕ)^8297*12500000000000^6249 ≤ 5507313038149^6249*1250000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674226951 1250000000 5507313038149 12500000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121711381/10000000000 : ℝ)^8297 ≤ (2552992645391/20000000000000 : ℝ)^6249 := by
    have hnat : (2121711381 : ℕ)^8297*20000000000000^6249 ≤ 2552992645391^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121711381 10000000000 2552992645391 20000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312290541/10000000000 : ℝ), (674226951/1250000000 : ℝ), (-2121711381/10000000000 : ℝ)] ![(10794133111019/25000000000000 : ℝ), (5507313038149/12500000000000 : ℝ), (2552992645391/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312290541/10000000000 : ℝ)|^8297 ≤ (10794133111019/25000000000000 : ℝ)^6249
        have hw : |(5312290541/10000000000 : ℝ)|=(5312290541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674226951/1250000000 : ℝ)|^8297 ≤ (5507313038149/12500000000000 : ℝ)^6249
        have hw : |(674226951/1250000000 : ℝ)|=(674226951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2121711381/10000000000 : ℝ)|^8297 ≤ (2552992645391/20000000000000 : ℝ)^6249
        have hw : |(-2121711381/10000000000 : ℝ)|=(2121711381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s6_7 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2185021387/5000000000 : ℝ)*x 0 + (4499068073/10000000000 : ℝ)*x 1 + (4244752499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185021387/5000000000 : ℝ)^8297 ≤ (16658319617311/50000000000000 : ℝ)^6249 := by
    have hnat : (2185021387 : ℕ)^8297*50000000000000^6249 ≤ 16658319617311^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185021387 5000000000 16658319617311 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4499068073/10000000000 : ℝ)^8297 ≤ (34628970218917/100000000000000 : ℝ)^6249 := by
    have hnat : (4499068073 : ℕ)^8297*100000000000000^6249 ≤ 34628970218917^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499068073 10000000000 34628970218917 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4244752499/10000000000 : ℝ)^8297 ≤ (6410878106001/20000000000000 : ℝ)^6249 := by
    have hnat : (4244752499 : ℕ)^8297*20000000000000^6249 ≤ 6410878106001^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244752499 10000000000 6410878106001 20000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185021387/5000000000 : ℝ), (4499068073/10000000000 : ℝ), (4244752499/10000000000 : ℝ)] ![(16658319617311/50000000000000 : ℝ), (34628970218917/100000000000000 : ℝ), (6410878106001/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185021387/5000000000 : ℝ)|^8297 ≤ (16658319617311/50000000000000 : ℝ)^6249
        have hw : |(2185021387/5000000000 : ℝ)|=(2185021387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4499068073/10000000000 : ℝ)|^8297 ≤ (34628970218917/100000000000000 : ℝ)^6249
        have hw : |(4499068073/10000000000 : ℝ)|=(4499068073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4244752499/10000000000 : ℝ)|^8297 ≤ (6410878106001/20000000000000 : ℝ)^6249
        have hw : |(4244752499/10000000000 : ℝ)|=(4244752499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1104_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5647/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3509/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5629/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5629/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5629/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5629/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5629/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5629/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5629/50000 : ℝ) ^ (1037/256 : ℝ) ≤ (7188644350470461/50000000000000000000 : ℝ) := by
    have hpowers : (5629/50000 : ℝ)^1037 ≤ (7188644350470461/50000000000000000000 : ℝ)^256 := by
      have hnat : (5629 : ℕ)^1037*50000000000000000000^256 ≤ 7188644350470461^256*50000^1037 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5629 50000 7188644350470461 50000000000000000000 1037 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5629/50000 : ℝ)) (X := (7188644350470461/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14073/100000 : ℝ) ^ (1037/256 : ℝ) ≤ (4438239917639503/12500000000000000000 : ℝ) := by
    have hpowers : (14073/100000 : ℝ)^1037 ≤ (4438239917639503/12500000000000000000 : ℝ)^256 := by
      have hnat : (14073 : ℕ)^1037*12500000000000000000^256 ≤ 4438239917639503^256*100000^1037 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14073 100000 4438239917639503 12500000000000000000 1037 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14073/100000 : ℝ)) (X := (4438239917639503/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007188644350470461/25000000000000000000 : ℝ) ≤ (5000354887891959/5000000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (25007188644350470461/25000000000000000000 : ℝ)^256 ≤ (5000354887891959/5000000000000000 : ℝ)^1037 := by
      have hnat : (25007188644350470461 : ℕ)^256*5000000000000000^1037 ≤ 5000354887891959^1037*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007188644350470461 25000000000000000000 5000354887891959 5000000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000354887891959/5000000000000000 : ℝ)) (X := (25007188644350470461/25000000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024941604021028473/50000000000000000000 : ℝ) ≤ (10001231215349527/10000000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (50024941604021028473/50000000000000000000 : ℝ)^256 ≤ (10001231215349527/10000000000000000 : ℝ)^1037 := by
      have hnat : (50024941604021028473 : ℕ)^256*10000000000000000^1037 ≤ 10001231215349527^1037*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024941604021028473 50000000000000000000 10001231215349527 10000000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001231215349527/10000000000000000 : ℝ)) (X := (50024941604021028473/50000000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254438239917639503/6250000000000000000 : ℝ) ≤ (156277385233049/156250000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (6254438239917639503/6250000000000000000 : ℝ)^256 ≤ (156277385233049/156250000000000 : ℝ)^1037 := by
      have hnat : (6254438239917639503 : ℕ)^256*156250000000000^1037 ≤ 156277385233049^1037*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254438239917639503 6250000000000000000 156277385233049 156250000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156277385233049/156250000000000 : ℝ)) (X := (6254438239917639503/6250000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7188644350470461/50000000000000000000 : ℝ) ≤ ((14070128642786238463/14075000000000000000 : ℝ)+2*(521439565609/281500000000000 : ℝ)*(5629/50000 : ℝ))^(1037/256 : ℝ) := by
    rw [show (14070128642786238463/14075000000000000000 : ℝ)+2*(521439565609/281500000000000 : ℝ)*(5629/50000 : ℝ)=(5000354887891959/5000000000000000 : ℝ) by norm_num, show 1+2*(7188644350470461/50000000000000000000 : ℝ)=(25007188644350470461/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4438239917639503/12500000000000000000 : ℝ)+(7188644350470461/50000000000000000000 : ℝ) ≤ ((14070128642786238463/14075000000000000000 : ℝ)+(521439565609/281500000000000 : ℝ)*((14073/100000 : ℝ)+(5629/50000 : ℝ)))^(1037/256 : ℝ) := by
    rw [show (14070128642786238463/14075000000000000000 : ℝ)+(521439565609/281500000000000 : ℝ)*((14073/100000 : ℝ)+(5629/50000 : ℝ))=(10001231215349527/10000000000000000 : ℝ) by norm_num, show 1+(4438239917639503/12500000000000000000 : ℝ)+(7188644350470461/50000000000000000000 : ℝ)=(50024941604021028473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4438239917639503/12500000000000000000 : ℝ) ≤ ((14070128642786238463/14075000000000000000 : ℝ)+2*(521439565609/281500000000000 : ℝ)*(14073/100000 : ℝ))^(1037/256 : ℝ) := by
    rw [show (14070128642786238463/14075000000000000000 : ℝ)+2*(521439565609/281500000000000 : ℝ)*(14073/100000 : ℝ)=(156277385233049/156250000000000 : ℝ) by norm_num, show 1+2*(4438239917639503/12500000000000000000 : ℝ)=(6254438239917639503/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14070128642786238463/14075000000000000000 : ℝ)*(X 1 0+X 2 0)+(521439565609/281500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (14070128642786238463/14075000000000000000 : ℝ)) (alpha := (521439565609/281500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14070128642786238463/14075000000000000000 : ℝ)*(X 0 1+X 2 1)+(521439565609/281500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (14070128642786238463/14075000000000000000 : ℝ)) (alpha := (521439565609/281500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14070128642786238463/14075000000000000000 : ℝ)*(X 0 2+X 1 2)+(521439565609/281500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (5629/50000 : ℝ)) (hi := (14073/100000 : ℝ)) (c := (14070128642786238463/14075000000000000000 : ℝ)) (alpha := (521439565609/281500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1092577729/5000000000 : ℝ)*X 0 0+(5394143677/10000000000 : ℝ)*X 0 1+(5264698947/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344991989/10000000000 : ℝ)*X 1 0+(-1125414021/5000000000 : ℝ)*X 1 1+(5264698947/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344991989/10000000000 : ℝ)*X 2 0+(5264698947/10000000000 : ℝ)*X 2 1+(-1125414021/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1092508189/2500000000 : ℝ)*X 0 0+(1061026169/2500000000 : ℝ)*X 0 1+(4499713551/10000000000 : ℝ)*X 0 2+(1092508189/2500000000 : ℝ)*X 1 0+(1061026169/2500000000 : ℝ)*X 1 1+(4499713551/10000000000 : ℝ)*X 1 2+(1092508189/2500000000 : ℝ)*X 2 0+(1061026169/2500000000 : ℝ)*X 2 1+(4499713551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2185160531/10000000000 : ℝ)*X 0 0+(5265025829/10000000000 : ℝ)*X 0 1+(5393815607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656145271/5000000000 : ℝ)*X 1 0+(-2121711381/10000000000 : ℝ)*X 1 1+(674226951/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312290541/10000000000 : ℝ)*X 2 0+(674226951/1250000000 : ℝ)*X 2 1+(-2121711381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2185021387/5000000000 : ℝ)*X 0 0+(4499068073/10000000000 : ℝ)*X 0 1+(4244752499/10000000000 : ℝ)*X 0 2+(2185021387/5000000000 : ℝ)*X 1 0+(4499068073/10000000000 : ℝ)*X 1 1+(4244752499/10000000000 : ℝ)*X 1 2+(2185021387/5000000000 : ℝ)*X 2 0+(4499068073/10000000000 : ℝ)*X 2 1+(4244752499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4862026213236920110151704371/703750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (689212103/50000000000000 : ℝ)*(base19) + (320987811/25000000000000 : ℝ)*(base23) + (25247861/50000000000000 : ℝ)*(lower2) + (4373273/2500000000000 : ℝ)*(upper3) + (104737357/100000000000000 : ℝ)*(upper5) + (5818823295512161/100000000000000 : ℝ)*(major0) + (5818823295512161/100000000000000 : ℝ)*(major1) + (5818823295512161/100000000000000 : ℝ)*(major2) + (7725343630643741/100000000000000 : ℝ)*(sp0) + (7725379257083117/100000000000000 : ℝ)*(sp1) + (7725379351556079/100000000000000 : ℝ)*(sp2) + (3912245467284987/100000000000000 : ℝ)*(sp3) + (18502431791/50000000000000 : ℝ)*(sp4) + (20257940643/100000000000000 : ℝ)*(sp7) + (391226572522563/10000000000000 : ℝ)*(f.failure) + (3862690317753661/50000000000000 : ℝ)*(f.sum) + (52248771762501/14075000000000000000000000000 : ℝ)*base66 + (1980933558230101457/1407500000000000000000000000000000 : ℝ)*base68 + (31239704253602398543/1407500000000000000000000000000000 : ℝ)*base69 + (1407309831262398543/1407500000000000000000000000000000 : ℝ)*base71 + (32859746155137/7037500000000000000000000000 : ℝ)*base73 + (24639918740417398543/1407500000000000000000000000000000 : ℝ)*base75 + (5724635414572601457/1407500000000000000000000000000000 : ℝ)*base78 + (18967573439984898543/1407500000000000000000000000000000 : ℝ)*base79 + (64754156478849/14075000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1411511/125000000000000000000 : ℝ)*base90 + (1411511/125000000000000000000 : ℝ)*base92 + (1411511/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (104338543470123069415407/14075000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1369718539/100000000000000 : ℝ)*(base19) + (297583837/20000000000000 : ℝ)*(base23) + (58463/39062500000 : ℝ)*(upper3) + (2719583/5000000000000 : ℝ)*(lower4) + (150756223/100000000000000 : ℝ)*(upper5) + (5848356176149203/100000000000000 : ℝ)*(major0) + (5848356176149203/100000000000000 : ℝ)*(major1) + (5848356176149203/100000000000000 : ℝ)*(major2) + (18666405661/50000000000000 : ℝ)*(sp1) + (40138930089/100000000000000 : ℝ)*(sp2) + (7764590049779613/100000000000000 : ℝ)*(sp4) + (7764551347249753/100000000000000 : ℝ)*(sp5) + (7764548422930339/100000000000000 : ℝ)*(sp6) + (24575762846359/625000000000 : ℝ)*(sp7) + (24575762846359/625000000000 : ℝ)*(f.failure) + (7764590049779613/100000000000000 : ℝ)*(f.sum) + (5366455057169/1759375000000000000000000000 : ℝ)*base65 + (4913180334920755011/1407500000000000000000000000000000 : ℝ)*base68 + (733589529324244989/1407500000000000000000000000000000 : ℝ)*base69 + (3408245602926744989/1407500000000000000000000000000000 : ℝ)*base71 + (13727113257451/7037500000000000000000000000 : ℝ)*base73 + (9933575224478255011/1407500000000000000000000000000000 : ℝ)*base76 + (19949843003743255011/1407500000000000000000000000000000 : ℝ)*base78 + (19496777985744244989/1407500000000000000000000000000000 : ℝ)*base79 + (39387414938951/7037500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (19551/3906250000000000000 : ℝ)*base89 + (19551/3906250000000000000 : ℝ)*base91 + (19551/3906250000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1104_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3509/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1104_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1104_s7_0 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2185186533/10000000000 : ℝ)*x 0 + (5393760633/10000000000 : ℝ)*x 1 + (5265061749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185186533/10000000000 : ℝ)^8297 ≤ (6637239376327/50000000000000 : ℝ)^6249 := by
    have hnat : (2185186533 : ℕ)^8297*50000000000000^6249 ≤ 6637239376327^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185186533 10000000000 6637239376327 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393760633/10000000000 : ℝ)^8297 ≤ (44057908082183/100000000000000 : ℝ)^6249 := by
    have hnat : (5393760633 : ℕ)^8297*100000000000000^6249 ≤ 44057908082183^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393760633 10000000000 44057908082183 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265061749/10000000000 : ℝ)^8297 ≤ (5333451644003/12500000000000 : ℝ)^6249 := by
    have hnat : (5265061749 : ℕ)^8297*12500000000000^6249 ≤ 5333451644003^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265061749 10000000000 5333451644003 12500000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2185186533/10000000000 : ℝ), (5393760633/10000000000 : ℝ), (5265061749/10000000000 : ℝ)] ![(6637239376327/50000000000000 : ℝ), (44057908082183/100000000000000 : ℝ), (5333451644003/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2185186533/10000000000 : ℝ)|^8297 ≤ (6637239376327/50000000000000 : ℝ)^6249
        have hw : |(-2185186533/10000000000 : ℝ)|=(2185186533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393760633/10000000000 : ℝ)|^8297 ≤ (44057908082183/100000000000000 : ℝ)^6249
        have hw : |(5393760633/10000000000 : ℝ)|=(5393760633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265061749/10000000000 : ℝ)|^8297 ≤ (5333451644003/12500000000000 : ℝ)^6249
        have hw : |(5265061749/10000000000 : ℝ)|=(5265061749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s7_1 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668112073/1250000000 : ℝ)*x 0 + (-2250475281/10000000000 : ℝ)*x 1 + (5265061831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668112073/1250000000 : ℝ)^8297 ≤ (43528749670463/100000000000000 : ℝ)^6249 := by
    have hnat : (668112073 : ℕ)^8297*100000000000000^6249 ≤ 43528749670463^6249*1250000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668112073 1250000000 43528749670463 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250475281/10000000000 : ℝ)^8297 ≤ (13803636283653/100000000000000 : ℝ)^6249 := by
    have hnat : (2250475281 : ℕ)^8297*100000000000000^6249 ≤ 13803636283653^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250475281 10000000000 13803636283653 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265061831/10000000000 : ℝ)^8297 ≤ (4266761403433/10000000000000 : ℝ)^6249 := by
    have hnat : (5265061831 : ℕ)^8297*10000000000000^6249 ≤ 4266761403433^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265061831 10000000000 4266761403433 10000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668112073/1250000000 : ℝ), (-2250475281/10000000000 : ℝ), (5265061831/10000000000 : ℝ)] ![(43528749670463/100000000000000 : ℝ), (13803636283653/100000000000000 : ℝ), (4266761403433/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668112073/1250000000 : ℝ)|^8297 ≤ (43528749670463/100000000000000 : ℝ)^6249
        have hw : |(668112073/1250000000 : ℝ)|=(668112073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2250475281/10000000000 : ℝ)|^8297 ≤ (13803636283653/100000000000000 : ℝ)^6249
        have hw : |(-2250475281/10000000000 : ℝ)|=(2250475281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265061831/10000000000 : ℝ)|^8297 ≤ (4266761403433/10000000000000 : ℝ)^6249
        have hw : |(5265061831/10000000000 : ℝ)|=(5265061831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s7_2 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672448393/5000000000 : ℝ)*x 0 + (5265061693/10000000000 : ℝ)*x 1 + (-1125237597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672448393/5000000000 : ℝ)^8297 ≤ (5441093981837/12500000000000 : ℝ)^6249 := by
    have hnat : (2672448393 : ℕ)^8297*12500000000000^6249 ≤ 5441093981837^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672448393 5000000000 5441093981837 12500000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265061693/10000000000 : ℝ)^8297 ≤ (21333806274737/50000000000000 : ℝ)^6249 := by
    have hnat : (5265061693 : ℕ)^8297*50000000000000^6249 ≤ 21333806274737^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265061693 10000000000 21333806274737 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125237597/5000000000 : ℝ)^8297 ≤ (6901817787569/50000000000000 : ℝ)^6249 := by
    have hnat : (1125237597 : ℕ)^8297*50000000000000^6249 ≤ 6901817787569^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125237597 5000000000 6901817787569 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672448393/5000000000 : ℝ), (5265061693/10000000000 : ℝ), (-1125237597/5000000000 : ℝ)] ![(5441093981837/12500000000000 : ℝ), (21333806274737/50000000000000 : ℝ), (6901817787569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672448393/5000000000 : ℝ)|^8297 ≤ (5441093981837/12500000000000 : ℝ)^6249
        have hw : |(2672448393/5000000000 : ℝ)|=(2672448393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265061693/10000000000 : ℝ)|^8297 ≤ (21333806274737/50000000000000 : ℝ)^6249
        have hw : |(5265061693/10000000000 : ℝ)|=(5265061693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1125237597/5000000000 : ℝ)|^8297 ≤ (6901817787569/50000000000000 : ℝ)^6249
        have hw : |(-1125237597/5000000000 : ℝ)|=(1125237597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s7_3 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2185025939/5000000000 : ℝ)*x 0 + (1061209677/2500000000 : ℝ)*x 1 + (2249487237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185025939/5000000000 : ℝ)^8297 ≤ (4164591423691/12500000000000 : ℝ)^6249 := by
    have hnat : (2185025939 : ℕ)^8297*12500000000000^6249 ≤ 4164591423691^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185025939 5000000000 4164591423691 12500000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061209677/2500000000 : ℝ)^8297 ≤ (32055254900173/100000000000000 : ℝ)^6249 := by
    have hnat : (1061209677 : ℕ)^8297*100000000000000^6249 ≤ 32055254900173^6249*2500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061209677 2500000000 32055254900173 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249487237/5000000000 : ℝ)^8297 ≤ (8657003422939/25000000000000 : ℝ)^6249 := by
    have hnat : (2249487237 : ℕ)^8297*25000000000000^6249 ≤ 8657003422939^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249487237 5000000000 8657003422939 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185025939/5000000000 : ℝ), (1061209677/2500000000 : ℝ), (2249487237/5000000000 : ℝ)] ![(4164591423691/12500000000000 : ℝ), (32055254900173/100000000000000 : ℝ), (8657003422939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185025939/5000000000 : ℝ)|^8297 ≤ (4164591423691/12500000000000 : ℝ)^6249
        have hw : |(2185025939/5000000000 : ℝ)|=(2185025939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061209677/2500000000 : ℝ)|^8297 ≤ (32055254900173/100000000000000 : ℝ)^6249
        have hw : |(1061209677/2500000000 : ℝ)|=(1061209677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249487237/5000000000 : ℝ)|^8297 ≤ (8657003422939/25000000000000 : ℝ)^6249
        have hw : |(2249487237/5000000000 : ℝ)|=(2249487237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s7_4 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-109259579/500000000 : ℝ)*x 0 + (1053076979/2000000000 : ℝ)*x 1 + (2696718137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109259579/500000000 : ℝ)^8297 ≤ (663725973001/5000000000000 : ℝ)^6249 := by
    have hnat : (109259579 : ℕ)^8297*5000000000000^6249 ≤ 663725973001^6249*500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109259579 500000000 663725973001 5000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053076979/2000000000 : ℝ)^8297 ≤ (42671090183303/100000000000000 : ℝ)^6249 := by
    have hnat : (1053076979 : ℕ)^8297*100000000000000^6249 ≤ 42671090183303^6249*2000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053076979 2000000000 42671090183303 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696718137/5000000000 : ℝ)^8297 ≤ (1762175613459/4000000000000 : ℝ)^6249 := by
    have hnat : (2696718137 : ℕ)^8297*4000000000000^6249 ≤ 1762175613459^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696718137 5000000000 1762175613459 4000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109259579/500000000 : ℝ), (1053076979/2000000000 : ℝ), (2696718137/5000000000 : ℝ)] ![(663725973001/5000000000000 : ℝ), (42671090183303/100000000000000 : ℝ), (1762175613459/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109259579/500000000 : ℝ)|^8297 ≤ (663725973001/5000000000000 : ℝ)^6249
        have hw : |(-109259579/500000000 : ℝ)|=(109259579/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053076979/2000000000 : ℝ)|^8297 ≤ (42671090183303/100000000000000 : ℝ)^6249
        have hw : |(1053076979/2000000000 : ℝ)|=(1053076979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696718137/5000000000 : ℝ)|^8297 ≤ (1762175613459/4000000000000 : ℝ)^6249
        have hw : |(2696718137/5000000000 : ℝ)|=(2696718137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s7_5 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312383487/10000000000 : ℝ)*x 0 + (-2122100827/10000000000 : ℝ)*x 1 + (1348359067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312383487/10000000000 : ℝ)^8297 ≤ (863550709229/2000000000000 : ℝ)^6249 := by
    have hnat : (5312383487 : ℕ)^8297*2000000000000^6249 ≤ 863550709229^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312383487 10000000000 863550709229 2000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122100827/10000000000 : ℝ)^8297 ≤ (12768074256511/100000000000000 : ℝ)^6249 := by
    have hnat : (2122100827 : ℕ)^8297*100000000000000^6249 ≤ 12768074256511^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122100827 10000000000 12768074256511 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348359067/2500000000 : ℝ)^8297 ≤ (11013597567851/25000000000000 : ℝ)^6249 := by
    have hnat : (1348359067 : ℕ)^8297*25000000000000^6249 ≤ 11013597567851^6249*2500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348359067 2500000000 11013597567851 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312383487/10000000000 : ℝ), (-2122100827/10000000000 : ℝ), (1348359067/2500000000 : ℝ)] ![(863550709229/2000000000000 : ℝ), (12768074256511/100000000000000 : ℝ), (11013597567851/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312383487/10000000000 : ℝ)|^8297 ≤ (863550709229/2000000000000 : ℝ)^6249
        have hw : |(5312383487/10000000000 : ℝ)|=(5312383487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2122100827/10000000000 : ℝ)|^8297 ≤ (12768074256511/100000000000000 : ℝ)^6249
        have hw : |(-2122100827/10000000000 : ℝ)|=(2122100827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348359067/2500000000 : ℝ)|^8297 ≤ (11013597567851/25000000000000 : ℝ)^6249
        have hw : |(1348359067/2500000000 : ℝ)|=(1348359067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s7_6 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531238349/1000000000 : ℝ)*x 0 + (269671813/500000000 : ℝ)*x 1 + (-2122100833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531238349/1000000000 : ℝ)^8297 ≤ (1727101419753/4000000000000 : ℝ)^6249 := by
    have hnat : (531238349 : ℕ)^8297*4000000000000^6249 ≤ 1727101419753^6249*1000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531238349 1000000000 1727101419753 4000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269671813/500000000 : ℝ)^8297 ≤ (44054390184643/100000000000000 : ℝ)^6249 := by
    have hnat : (269671813 : ℕ)^8297*100000000000000^6249 ≤ 44054390184643^6249*500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269671813 500000000 44054390184643 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122100833/10000000000 : ℝ)^8297 ≤ (6384037152221/50000000000000 : ℝ)^6249 := by
    have hnat : (2122100833 : ℕ)^8297*50000000000000^6249 ≤ 6384037152221^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122100833 10000000000 6384037152221 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531238349/1000000000 : ℝ), (269671813/500000000 : ℝ), (-2122100833/10000000000 : ℝ)] ![(1727101419753/4000000000000 : ℝ), (44054390184643/100000000000000 : ℝ), (6384037152221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531238349/1000000000 : ℝ)|^8297 ≤ (1727101419753/4000000000000 : ℝ)^6249
        have hw : |(531238349/1000000000 : ℝ)|=(531238349/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269671813/500000000 : ℝ)|^8297 ≤ (44054390184643/100000000000000 : ℝ)^6249
        have hw : |(269671813/500000000 : ℝ)|=(269671813/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2122100833/10000000000 : ℝ)|^8297 ≤ (6384037152221/50000000000000 : ℝ)^6249
        have hw : |(-2122100833/10000000000 : ℝ)|=(2122100833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s7_7 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370061627/10000000000 : ℝ)*x 0 + (1124584133/2500000000 : ℝ)*x 1 + (84909581/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370061627/10000000000 : ℝ)^8297 ≤ (33316830073493/100000000000000 : ℝ)^6249 := by
    have hnat : (4370061627 : ℕ)^8297*100000000000000^6249 ≤ 33316830073493^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370061627 10000000000 33316830073493 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124584133/2500000000 : ℝ)^8297 ≤ (34621494470499/100000000000000 : ℝ)^6249 := by
    have hnat : (1124584133 : ℕ)^8297*100000000000000^6249 ≤ 34621494470499^6249*2500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124584133 2500000000 34621494470499 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84909581/200000000 : ℝ)^8297 ≤ (32061675436837/100000000000000 : ℝ)^6249 := by
    have hnat : (84909581 : ℕ)^8297*100000000000000^6249 ≤ 32061675436837^6249*200000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84909581 200000000 32061675436837 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370061627/10000000000 : ℝ), (1124584133/2500000000 : ℝ), (84909581/200000000 : ℝ)] ![(33316830073493/100000000000000 : ℝ), (34621494470499/100000000000000 : ℝ), (32061675436837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370061627/10000000000 : ℝ)|^8297 ≤ (33316830073493/100000000000000 : ℝ)^6249
        have hw : |(4370061627/10000000000 : ℝ)|=(4370061627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124584133/2500000000 : ℝ)|^8297 ≤ (34621494470499/100000000000000 : ℝ)^6249
        have hw : |(1124584133/2500000000 : ℝ)|=(1124584133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84909581/200000000 : ℝ)|^8297 ≤ (32061675436837/100000000000000 : ℝ)^6249
        have hw : |(84909581/200000000 : ℝ)|=(84909581/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1104_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3509/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5651/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3507/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3509/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5647/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3509/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5647/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3509/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5647/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3509/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5647/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3509/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5647/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3509/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5647/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5647/50000 : ℝ) ^ (1037/256 : ℝ) ≤ (14564432265335757/100000000000000000000 : ℝ) := by
    have hpowers : (5647/50000 : ℝ)^1037 ≤ (14564432265335757/100000000000000000000 : ℝ)^256 := by
      have hnat : (5647 : ℕ)^1037*100000000000000000000^256 ≤ 14564432265335757^256*50000^1037 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5647 50000 14564432265335757 100000000000000000000 1037 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5647/50000 : ℝ)) (X := (14564432265335757/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3509/25000 : ℝ) ^ (1037/256 : ℝ) ≤ (702585828624819/2000000000000000000 : ℝ) := by
    have hpowers : (3509/25000 : ℝ)^1037 ≤ (702585828624819/2000000000000000000 : ℝ)^256 := by
      have hnat : (3509 : ℕ)^1037*2000000000000000000^256 ≤ 702585828624819^256*25000^1037 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3509 25000 702585828624819 2000000000000000000 1037 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3509/25000 : ℝ)) (X := (702585828624819/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014564432265335757/50000000000000000000 : ℝ) ≤ (2500179753411383/2500000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (50014564432265335757/50000000000000000000 : ℝ)^256 ≤ (2500179753411383/2500000000000000 : ℝ)^1037 := by
      have hnat : (50014564432265335757 : ℕ)^256*2500000000000000^1037 ≤ 2500179753411383^1037*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014564432265335757 50000000000000000000 2500179753411383 2500000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500179753411383/2500000000000000 : ℝ)) (X := (50014564432265335757/50000000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049693723696576707/100000000000000000000 : ℝ) ≤ (1000122653937931/1000000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (100049693723696576707/100000000000000000000 : ℝ)^256 ≤ (1000122653937931/1000000000000000 : ℝ)^1037 := by
      have hnat : (100049693723696576707 : ℕ)^256*1000000000000000^1037 ≤ 1000122653937931^1037*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049693723696576707 100000000000000000000 1000122653937931 1000000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000122653937931/1000000000000000 : ℝ)) (X := (100049693723696576707/100000000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000702585828624819/1000000000000000000 : ℝ) ≤ (4883659211481/4882812500000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (1000702585828624819/1000000000000000000 : ℝ)^256 ≤ (4883659211481/4882812500000 : ℝ)^1037 := by
      have hnat : (1000702585828624819 : ℕ)^256*4882812500000^1037 ≤ 4883659211481^1037*1000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000702585828624819 1000000000000000000 4883659211481 4882812500000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (4883659211481/4882812500000 : ℝ)) (X := (1000702585828624819/1000000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14564432265335757/100000000000000000000 : ℝ) ≤ ((342631344301768391/342750000000000000 : ℝ)+2*(253762866889/137100000000000 : ℝ)*(5647/50000 : ℝ))^(1037/256 : ℝ) := by
    rw [show (342631344301768391/342750000000000000 : ℝ)+2*(253762866889/137100000000000 : ℝ)*(5647/50000 : ℝ)=(2500179753411383/2500000000000000 : ℝ) by norm_num, show 1+2*(14564432265335757/100000000000000000000 : ℝ)=(50014564432265335757/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(702585828624819/2000000000000000000 : ℝ)+(14564432265335757/100000000000000000000 : ℝ) ≤ ((342631344301768391/342750000000000000 : ℝ)+(253762866889/137100000000000 : ℝ)*((3509/25000 : ℝ)+(5647/50000 : ℝ)))^(1037/256 : ℝ) := by
    rw [show (342631344301768391/342750000000000000 : ℝ)+(253762866889/137100000000000 : ℝ)*((3509/25000 : ℝ)+(5647/50000 : ℝ))=(1000122653937931/1000000000000000 : ℝ) by norm_num, show 1+(702585828624819/2000000000000000000 : ℝ)+(14564432265335757/100000000000000000000 : ℝ)=(100049693723696576707/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(702585828624819/2000000000000000000 : ℝ) ≤ ((342631344301768391/342750000000000000 : ℝ)+2*(253762866889/137100000000000 : ℝ)*(3509/25000 : ℝ))^(1037/256 : ℝ) := by
    rw [show (342631344301768391/342750000000000000 : ℝ)+2*(253762866889/137100000000000 : ℝ)*(3509/25000 : ℝ)=(4883659211481/4882812500000 : ℝ) by norm_num, show 1+2*(702585828624819/2000000000000000000 : ℝ)=(1000702585828624819/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (342631344301768391/342750000000000000 : ℝ)*(X 1 0+X 2 0)+(253762866889/137100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (5647/50000 : ℝ)) (hi := (3509/25000 : ℝ)) (c := (342631344301768391/342750000000000000 : ℝ)) (alpha := (253762866889/137100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (342631344301768391/342750000000000000 : ℝ)*(X 0 1+X 2 1)+(253762866889/137100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (5647/50000 : ℝ)) (hi := (3509/25000 : ℝ)) (c := (342631344301768391/342750000000000000 : ℝ)) (alpha := (253762866889/137100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (342631344301768391/342750000000000000 : ℝ)*(X 0 2+X 1 2)+(253762866889/137100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (5647/50000 : ℝ)) (hi := (3509/25000 : ℝ)) (c := (342631344301768391/342750000000000000 : ℝ)) (alpha := (253762866889/137100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2185186533/10000000000 : ℝ)*X 0 0+(5393760633/10000000000 : ℝ)*X 0 1+(5265061749/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668112073/1250000000 : ℝ)*X 1 0+(-2250475281/10000000000 : ℝ)*X 1 1+(5265061831/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672448393/5000000000 : ℝ)*X 2 0+(5265061693/10000000000 : ℝ)*X 2 1+(-1125237597/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2185025939/5000000000 : ℝ)*X 0 0+(1061209677/2500000000 : ℝ)*X 0 1+(2249487237/5000000000 : ℝ)*X 0 2+(2185025939/5000000000 : ℝ)*X 1 0+(1061209677/2500000000 : ℝ)*X 1 1+(2249487237/5000000000 : ℝ)*X 1 2+(2185025939/5000000000 : ℝ)*X 2 0+(1061209677/2500000000 : ℝ)*X 2 1+(2249487237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-109259579/500000000 : ℝ)*X 0 0+(1053076979/2000000000 : ℝ)*X 0 1+(2696718137/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312383487/10000000000 : ℝ)*X 1 0+(-2122100827/10000000000 : ℝ)*X 1 1+(1348359067/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531238349/1000000000 : ℝ)*X 2 0+(269671813/500000000 : ℝ)*X 2 1+(-2122100833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4370061627/10000000000 : ℝ)*X 0 0+(1124584133/2500000000 : ℝ)*X 0 1+(84909581/200000000 : ℝ)*X 0 2+(4370061627/10000000000 : ℝ)*X 1 0+(1124584133/2500000000 : ℝ)*X 1 1+(84909581/200000000 : ℝ)*X 1 2+(4370061627/10000000000 : ℝ)*X 2 0+(1124584133/2500000000 : ℝ)*X 2 1+(84909581/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1842323830839711573877/457000000000000000000000000 : ℝ) := by norm_num
    linear_combination (227077481/25000000000000 : ℝ)*(base19) + (968531701/100000000000000 : ℝ)*(base23) + (124768817/100000000000000 : ℝ)*(lower2) + (25573939/50000000000000 : ℝ)*(upper3) + (70378141/100000000000000 : ℝ)*(upper5) + (585253359330827/10000000000000 : ℝ)*(major0) + (585253359330827/10000000000000 : ℝ)*(major1) + (585253359330827/10000000000000 : ℝ)*(major2) + (3885050921989609/50000000000000 : ℝ)*(sp0) + (242816731766463/3125000000000 : ℝ)*(sp1) + (7770135356305039/100000000000000 : ℝ)*(sp2) + (3934916419929229/100000000000000 : ℝ)*(sp3) + (17240428761/50000000000000 : ℝ)*(sp4) + (7153736229/50000000000000 : ℝ)*(sp7) + (1967465363700843/50000000000000 : ℝ)*(f.failure) + (388506816241837/5000000000000 : ℝ)*(f.sum) + (277848284219/171375000000000000000000000 : ℝ)*base65 + (11142851459344381/1142500000000000000000000000000 : ℝ)*base68 + (878293032564381/1142500000000000000000000000000 : ℝ)*base70 + (2432309776655619/1142500000000000000000000000000 : ℝ)*base71 + (2096213008063/685500000000000000000000000 : ℝ)*base74 + (24969361975569381/1142500000000000000000000000000 : ℝ)*base76 + (371344760980619/1142500000000000000000000000000 : ℝ)*base77 + (559415190028119/1142500000000000000000000000000 : ℝ)*base79 + (1601560587037/685500000000000000000000000 : ℝ)*base82 + (3678671/625000000000000000000 : ℝ)*base90 + (3678671/625000000000000000000 : ℝ)*base92 + (3678671/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22802015509889056132725377/2856250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (682447083/50000000000000 : ℝ)*(base19) + (379131803/25000000000000 : ℝ)*(base23) + (142525459/100000000000000 : ℝ)*(upper3) + (13636811/20000000000000 : ℝ)*(lower4) + (147439961/100000000000000 : ℝ)*(upper5) + (2941040097547703/50000000000000 : ℝ)*(major0) + (2941040097547703/50000000000000 : ℝ)*(major1) + (2941040097547703/50000000000000 : ℝ)*(major2) + (2344392557/6250000000000 : ℝ)*(sp1) + (2029692161/5000000000000 : ℝ)*(sp2) + (1952340960280701/25000000000000 : ℝ)*(sp4) + (7809324965947727/100000000000000 : ℝ)*(sp5) + (7809321730752373/100000000000000 : ℝ)*(sp6) + (1977398141480661/50000000000000 : ℝ)*(sp7) + (1977398141480661/50000000000000 : ℝ)*(f.failure) + (1952340960280701/25000000000000 : ℝ)*(f.sum) + (10227233380709/1713750000000000000000000000 : ℝ)*base66 + (75759674581807791/5712500000000000000000000000000 : ℝ)*base67 + (22713196719507791/5712500000000000000000000000000 : ℝ)*base69 + (33815893303429709/5712500000000000000000000000000 : ℝ)*base72 + (16553733067369/6855000000000000000000000000 : ℝ)*base73 + (13168520865957791/5712500000000000000000000000000 : ℝ)*base75 + (46614826908057791/5712500000000000000000000000000 : ℝ)*base77 + (111995181455942209/5712500000000000000000000000000 : ℝ)*base80 + (28334067621971/6855000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6010417/625000000000000000000 : ℝ)*base90 + (6010417/625000000000000000000 : ℝ)*base92 + (6010417/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1104_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3509/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5647/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3507/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1104_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1104_s8_0 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2185192739/10000000000 : ℝ)*x 0 + (26968391/50000000 : ℝ)*x 1 + (658142523/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185192739/10000000000 : ℝ)^8297 ≤ (13274528808119/100000000000000 : ℝ)^6249 := by
    have hnat : (2185192739 : ℕ)^8297*100000000000000^6249 ≤ 13274528808119^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185192739 10000000000 13274528808119 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26968391/50000000 : ℝ)^8297 ≤ (44057014071339/100000000000000 : ℝ)^6249 := by
    have hnat : (26968391 : ℕ)^8297*100000000000000^6249 ≤ 44057014071339^6249*50000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26968391 50000000 44057014071339 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658142523/1250000000 : ℝ)^8297 ≤ (42668457101419/100000000000000 : ℝ)^6249 := by
    have hnat : (658142523 : ℕ)^8297*100000000000000^6249 ≤ 42668457101419^6249*1250000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658142523 1250000000 42668457101419 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2185192739/10000000000 : ℝ), (26968391/50000000 : ℝ), (658142523/1250000000 : ℝ)] ![(13274528808119/100000000000000 : ℝ), (44057014071339/100000000000000 : ℝ), (42668457101419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2185192739/10000000000 : ℝ)|^8297 ≤ (13274528808119/100000000000000 : ℝ)^6249
        have hw : |(-2185192739/10000000000 : ℝ)|=(2185192739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26968391/50000000 : ℝ)|^8297 ≤ (44057014071339/100000000000000 : ℝ)^6249
        have hw : |(26968391/50000000 : ℝ)|=(26968391/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658142523/1250000000 : ℝ)|^8297 ≤ (42668457101419/100000000000000 : ℝ)^6249
        have hw : |(658142523/1250000000 : ℝ)|=(658142523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s8_1 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334054767/625000000 : ℝ)*x 0 + (-2250398137/10000000000 : ℝ)*x 1 + (5265140631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334054767/625000000 : ℝ)^8297 ≤ (43528530036313/100000000000000 : ℝ)^6249 := by
    have hnat : (334054767 : ℕ)^8297*100000000000000^6249 ≤ 43528530036313^6249*625000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334054767 625000000 43528530036313 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250398137/10000000000 : ℝ)^8297 ≤ (13803008037931/100000000000000 : ℝ)^6249 := by
    have hnat : (2250398137 : ℕ)^8297*100000000000000^6249 ≤ 13803008037931^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250398137 10000000000 13803008037931 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265140631/10000000000 : ℝ)^8297 ≤ (42668461911087/100000000000000 : ℝ)^6249 := by
    have hnat : (5265140631 : ℕ)^8297*100000000000000^6249 ≤ 42668461911087^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265140631 10000000000 42668461911087 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334054767/625000000 : ℝ), (-2250398137/10000000000 : ℝ), (5265140631/10000000000 : ℝ)] ![(43528530036313/100000000000000 : ℝ), (13803008037931/100000000000000 : ℝ), (42668461911087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334054767/625000000 : ℝ)|^8297 ≤ (43528530036313/100000000000000 : ℝ)^6249
        have hw : |(334054767/625000000 : ℝ)|=(334054767/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2250398137/10000000000 : ℝ)|^8297 ≤ (13803008037931/100000000000000 : ℝ)^6249
        have hw : |(-2250398137/10000000000 : ℝ)|=(2250398137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265140631/10000000000 : ℝ)|^8297 ≤ (42668461911087/100000000000000 : ℝ)^6249
        have hw : |(5265140631/10000000000 : ℝ)|=(5265140631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s8_2 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672437863/5000000000 : ℝ)*x 0 + (263257061/500000000 : ℝ)*x 1 + (-562599521/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672437863/5000000000 : ℝ)^8297 ≤ (8705704826481/20000000000000 : ℝ)^6249 := by
    have hnat : (2672437863 : ℕ)^8297*20000000000000^6249 ≤ 8705704826481^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672437863 5000000000 8705704826481 20000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263257061/500000000 : ℝ)^8297 ≤ (42668468248659/100000000000000 : ℝ)^6249 := by
    have hnat : (263257061 : ℕ)^8297*100000000000000^6249 ≤ 42668468248659^6249*500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263257061 500000000 42668468248659 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562599521/2500000000 : ℝ)^8297 ≤ (1725375950789/12500000000000 : ℝ)^6249 := by
    have hnat : (562599521 : ℕ)^8297*12500000000000^6249 ≤ 1725375950789^6249*2500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562599521 2500000000 1725375950789 12500000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672437863/5000000000 : ℝ), (263257061/500000000 : ℝ), (-562599521/2500000000 : ℝ)] ![(8705704826481/20000000000000 : ℝ), (42668468248659/100000000000000 : ℝ), (1725375950789/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672437863/5000000000 : ℝ)|^8297 ≤ (8705704826481/20000000000000 : ℝ)^6249
        have hw : |(2672437863/5000000000 : ℝ)|=(2672437863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263257061/500000000 : ℝ)|^8297 ≤ (42668468248659/100000000000000 : ℝ)^6249
        have hw : |(263257061/500000000 : ℝ)|=(263257061/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-562599521/2500000000 : ℝ)|^8297 ≤ (1725375950789/12500000000000 : ℝ)^6249
        have hw : |(-562599521/2500000000 : ℝ)|=(562599521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s8_3 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (546256989/1250000000 : ℝ)*x 0 + (212249853/500000000 : ℝ)*x 1 + (2249407557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546256989/1250000000 : ℝ)^8297 ≤ (6663354444713/20000000000000 : ℝ)^6249 := by
    have hnat : (546256989 : ℕ)^8297*20000000000000^6249 ≤ 6663354444713^6249*1250000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546256989 1250000000 6663354444713 20000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212249853/500000000 : ℝ)^8297 ≤ (32056842623461/100000000000000 : ℝ)^6249 := by
    have hnat : (212249853 : ℕ)^8297*100000000000000^6249 ≤ 32056842623461^6249*500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212249853 500000000 32056842623461 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249407557/5000000000 : ℝ)^8297 ≤ (6925277028111/20000000000000 : ℝ)^6249 := by
    have hnat : (2249407557 : ℕ)^8297*20000000000000^6249 ≤ 6925277028111^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249407557 5000000000 6925277028111 20000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546256989/1250000000 : ℝ), (212249853/500000000 : ℝ), (2249407557/5000000000 : ℝ)] ![(6663354444713/20000000000000 : ℝ), (32056842623461/100000000000000 : ℝ), (6925277028111/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546256989/1250000000 : ℝ)|^8297 ≤ (6663354444713/20000000000000 : ℝ)^6249
        have hw : |(546256989/1250000000 : ℝ)|=(546256989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(212249853/500000000 : ℝ)|^8297 ≤ (32056842623461/100000000000000 : ℝ)^6249
        have hw : |(212249853/500000000 : ℝ)|=(212249853/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249407557/5000000000 : ℝ)|^8297 ≤ (6925277028111/20000000000000 : ℝ)^6249
        have hw : |(2249407557/5000000000 : ℝ)|=(2249407557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s8_4 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-87407901/400000000 : ℝ)*x 0 + (5265462787/10000000000 : ℝ)*x 1 + (1348338643/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87407901/400000000 : ℝ)^8297 ≤ (829660463149/6250000000000 : ℝ)^6249 := by
    have hnat : (87407901 : ℕ)^8297*6250000000000^6249 ≤ 829660463149^6249*400000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87407901 400000000 829660463149 6250000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265462787/10000000000 : ℝ)^8297 ≤ (2133596415347/5000000000000 : ℝ)^6249 := by
    have hnat : (5265462787 : ℕ)^8297*5000000000000^6249 ≤ 2133596415347^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265462787 10000000000 2133596415347 5000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348338643/2500000000 : ℝ)^8297 ≤ (44053504270991/100000000000000 : ℝ)^6249 := by
    have hnat : (1348338643 : ℕ)^8297*100000000000000^6249 ≤ 44053504270991^6249*2500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348338643 2500000000 44053504270991 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87407901/400000000 : ℝ), (5265462787/10000000000 : ℝ), (1348338643/2500000000 : ℝ)] ![(829660463149/6250000000000 : ℝ), (2133596415347/5000000000000 : ℝ), (44053504270991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87407901/400000000 : ℝ)|^8297 ≤ (829660463149/6250000000000 : ℝ)^6249
        have hw : |(-87407901/400000000 : ℝ)|=(87407901/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265462787/10000000000 : ℝ)|^8297 ≤ (2133596415347/5000000000000 : ℝ)^6249
        have hw : |(5265462787/10000000000 : ℝ)|=(5265462787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348338643/2500000000 : ℝ)|^8297 ≤ (44053504270991/100000000000000 : ℝ)^6249
        have hw : |(1348338643/2500000000 : ℝ)|=(1348338643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s8_5 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312403917/10000000000 : ℝ)*x 0 + (-1061092097/5000000000 : ℝ)*x 1 + (5393354529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312403917/10000000000 : ℝ)^8297 ≤ (5397219491313/12500000000000 : ℝ)^6249 := by
    have hnat : (5312403917 : ℕ)^8297*12500000000000^6249 ≤ 5397219491313^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312403917 10000000000 5397219491313 12500000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061092097/5000000000 : ℝ)^8297 ≤ (6384370122651/50000000000000 : ℝ)^6249 := by
    have hnat : (1061092097 : ℕ)^8297*50000000000000^6249 ≤ 6384370122651^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061092097 5000000000 6384370122651 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393354529/10000000000 : ℝ)^8297 ≤ (22026751902327/50000000000000 : ℝ)^6249 := by
    have hnat : (5393354529 : ℕ)^8297*50000000000000^6249 ≤ 22026751902327^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393354529 10000000000 22026751902327 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312403917/10000000000 : ℝ), (-1061092097/5000000000 : ℝ), (5393354529/10000000000 : ℝ)] ![(5397219491313/12500000000000 : ℝ), (6384370122651/50000000000000 : ℝ), (22026751902327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312403917/10000000000 : ℝ)|^8297 ≤ (5397219491313/12500000000000 : ℝ)^6249
        have hw : |(5312403917/10000000000 : ℝ)|=(5312403917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1061092097/5000000000 : ℝ)|^8297 ≤ (6384370122651/50000000000000 : ℝ)^6249
        have hw : |(-1061092097/5000000000 : ℝ)|=(1061092097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393354529/10000000000 : ℝ)|^8297 ≤ (22026751902327/50000000000000 : ℝ)^6249
        have hw : |(5393354529/10000000000 : ℝ)|=(5393354529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s8_6 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531240373/1000000000 : ℝ)*x 0 + (1078670897/2000000000 : ℝ)*x 1 + (-530546127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531240373/1000000000 : ℝ)^8297 ≤ (5397219239063/12500000000000 : ℝ)^6249 := by
    have hnat : (531240373 : ℕ)^8297*12500000000000^6249 ≤ 5397219239063^6249*1000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531240373 1000000000 5397219239063 12500000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078670897/2000000000 : ℝ)^8297 ≤ (44053503327471/100000000000000 : ℝ)^6249 := by
    have hnat : (1078670897 : ℕ)^8297*100000000000000^6249 ≤ 44053503327471^6249*2000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078670897 2000000000 44053503327471 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530546127/2500000000 : ℝ)^8297 ≤ (10214994203/80000000000 : ℝ)^6249 := by
    have hnat : (530546127 : ℕ)^8297*80000000000^6249 ≤ 10214994203^6249*2500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530546127 2500000000 10214994203 80000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531240373/1000000000 : ℝ), (1078670897/2000000000 : ℝ), (-530546127/2500000000 : ℝ)] ![(5397219239063/12500000000000 : ℝ), (44053503327471/100000000000000 : ℝ), (10214994203/80000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531240373/1000000000 : ℝ)|^8297 ≤ (5397219239063/12500000000000 : ℝ)^6249
        have hw : |(531240373/1000000000 : ℝ)|=(531240373/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078670897/2000000000 : ℝ)|^8297 ≤ (44053503327471/100000000000000 : ℝ)^6249
        have hw : |(1078670897/2000000000 : ℝ)|=(1078670897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-530546127/2500000000 : ℝ)|^8297 ≤ (10214994203/80000000000 : ℝ)^6249
        have hw : |(-530546127/2500000000 : ℝ)|=(530546127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s8_7 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4370065529/10000000000 : ℝ)*x 0 + (44981783/100000000 : ℝ)*x 1 + (424563637/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370065529/10000000000 : ℝ)^8297 ≤ (33316869571393/100000000000000 : ℝ)^6249 := by
    have hnat : (4370065529 : ℕ)^8297*100000000000000^6249 ≤ 33316869571393^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370065529 10000000000 33316869571393 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44981783/100000000 : ℝ)^8297 ≤ (17309938760889/50000000000000 : ℝ)^6249 := by
    have hnat : (44981783 : ℕ)^8297*50000000000000^6249 ≤ 17309938760889^6249*100000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44981783 100000000 17309938760889 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424563637/1000000000 : ℝ)^8297 ≤ (4007906611331/12500000000000 : ℝ)^6249 := by
    have hnat : (424563637 : ℕ)^8297*12500000000000^6249 ≤ 4007906611331^6249*1000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424563637 1000000000 4007906611331 12500000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370065529/10000000000 : ℝ), (44981783/100000000 : ℝ), (424563637/1000000000 : ℝ)] ![(33316869571393/100000000000000 : ℝ), (17309938760889/50000000000000 : ℝ), (4007906611331/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370065529/10000000000 : ℝ)|^8297 ≤ (33316869571393/100000000000000 : ℝ)^6249
        have hw : |(4370065529/10000000000 : ℝ)|=(4370065529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(44981783/100000000 : ℝ)|^8297 ≤ (17309938760889/50000000000000 : ℝ)^6249
        have hw : |(44981783/100000000 : ℝ)|=(44981783/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(424563637/1000000000 : ℝ)|^8297 ≤ (4007906611331/12500000000000 : ℝ)^6249
        have hw : |(424563637/1000000000 : ℝ)|=(424563637/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1104_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3507/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11303/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7013/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3507/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5651/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3507/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5651/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3507/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5651/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3507/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5651/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3507/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5651/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3507/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5651/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5651/50000 : ℝ) ^ (1037/256 : ℝ) ≤ (456445864109099/3125000000000000000 : ℝ) := by
    have hpowers : (5651/50000 : ℝ)^1037 ≤ (456445864109099/3125000000000000000 : ℝ)^256 := by
      have hnat : (5651 : ℕ)^1037*3125000000000000000^256 ≤ 456445864109099^256*50000^1037 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5651 50000 456445864109099 3125000000000000000 1037 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5651/50000 : ℝ)) (X := (456445864109099/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3507/25000 : ℝ) ^ (1037/256 : ℝ) ≤ (17524127789031711/50000000000000000000 : ℝ) := by
    have hpowers : (3507/25000 : ℝ)^1037 ≤ (17524127789031711/50000000000000000000 : ℝ)^256 := by
      have hnat : (3507 : ℕ)^1037*50000000000000000000^256 ≤ 17524127789031711^256*25000^1037 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3507 25000 17524127789031711 50000000000000000000 1037 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3507/25000 : ℝ)) (X := (17524127789031711/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562956445864109099/1562500000000000000 : ℝ) ≤ (10000721078738407/10000000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (1562956445864109099/1562500000000000000 : ℝ)^256 ≤ (10000721078738407/10000000000000000 : ℝ)^1037 := by
      have hnat : (1562956445864109099 : ℕ)^256*10000000000000000^1037 ≤ 10000721078738407^1037*1562500000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562956445864109099 1562500000000000000 10000721078738407 10000000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000721078738407/10000000000000000 : ℝ)) (X := (1562956445864109099/1562500000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004965452322955459/10000000000000000000 : ℝ) ≤ (10001225572015101/10000000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (10004965452322955459/10000000000000000000 : ℝ)^256 ≤ (10001225572015101/10000000000000000 : ℝ)^1037 := by
      have hnat : (10004965452322955459 : ℕ)^256*10000000000000000^1037 ≤ 10001225572015101^1037*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004965452322955459 10000000000000000000 10001225572015101 10000000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001225572015101/10000000000000000 : ℝ)) (X := (10004965452322955459/10000000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017524127789031711/25000000000000000000 : ℝ) ≤ (2000346013058359/2000000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (25017524127789031711/25000000000000000000 : ℝ)^256 ≤ (2000346013058359/2000000000000000 : ℝ)^1037 := by
      have hnat : (25017524127789031711 : ℕ)^256*2000000000000000^1037 ≤ 2000346013058359^1037*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017524127789031711 25000000000000000000 2000346013058359 2000000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000346013058359/2000000000000000 : ℝ)) (X := (25017524127789031711/25000000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(456445864109099/3125000000000000000 : ℝ) ≤ ((469837277493353557/470000000000000000 : ℝ)+2*(8698159943/4700000000000 : ℝ)*(5651/50000 : ℝ))^(1037/256 : ℝ) := by
    rw [show (469837277493353557/470000000000000000 : ℝ)+2*(8698159943/4700000000000 : ℝ)*(5651/50000 : ℝ)=(10000721078738407/10000000000000000 : ℝ) by norm_num, show 1+2*(456445864109099/3125000000000000000 : ℝ)=(1562956445864109099/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17524127789031711/50000000000000000000 : ℝ)+(456445864109099/3125000000000000000 : ℝ) ≤ ((469837277493353557/470000000000000000 : ℝ)+(8698159943/4700000000000 : ℝ)*((3507/25000 : ℝ)+(5651/50000 : ℝ)))^(1037/256 : ℝ) := by
    rw [show (469837277493353557/470000000000000000 : ℝ)+(8698159943/4700000000000 : ℝ)*((3507/25000 : ℝ)+(5651/50000 : ℝ))=(10001225572015101/10000000000000000 : ℝ) by norm_num, show 1+(17524127789031711/50000000000000000000 : ℝ)+(456445864109099/3125000000000000000 : ℝ)=(10004965452322955459/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17524127789031711/50000000000000000000 : ℝ) ≤ ((469837277493353557/470000000000000000 : ℝ)+2*(8698159943/4700000000000 : ℝ)*(3507/25000 : ℝ))^(1037/256 : ℝ) := by
    rw [show (469837277493353557/470000000000000000 : ℝ)+2*(8698159943/4700000000000 : ℝ)*(3507/25000 : ℝ)=(2000346013058359/2000000000000000 : ℝ) by norm_num, show 1+2*(17524127789031711/50000000000000000000 : ℝ)=(25017524127789031711/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (469837277493353557/470000000000000000 : ℝ)*(X 1 0+X 2 0)+(8698159943/4700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (3507/25000 : ℝ)) (c := (469837277493353557/470000000000000000 : ℝ)) (alpha := (8698159943/4700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (469837277493353557/470000000000000000 : ℝ)*(X 0 1+X 2 1)+(8698159943/4700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (3507/25000 : ℝ)) (c := (469837277493353557/470000000000000000 : ℝ)) (alpha := (8698159943/4700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (469837277493353557/470000000000000000 : ℝ)*(X 0 2+X 1 2)+(8698159943/4700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (3507/25000 : ℝ)) (c := (469837277493353557/470000000000000000 : ℝ)) (alpha := (8698159943/4700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2185192739/10000000000 : ℝ)*X 0 0+(26968391/50000000 : ℝ)*X 0 1+(658142523/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334054767/625000000 : ℝ)*X 1 0+(-2250398137/10000000000 : ℝ)*X 1 1+(5265140631/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672437863/5000000000 : ℝ)*X 2 0+(263257061/500000000 : ℝ)*X 2 1+(-562599521/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((546256989/1250000000 : ℝ)*X 0 0+(212249853/500000000 : ℝ)*X 0 1+(2249407557/5000000000 : ℝ)*X 0 2+(546256989/1250000000 : ℝ)*X 1 0+(212249853/500000000 : ℝ)*X 1 1+(2249407557/5000000000 : ℝ)*X 1 2+(546256989/1250000000 : ℝ)*X 2 0+(212249853/500000000 : ℝ)*X 2 1+(2249407557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-87407901/400000000 : ℝ)*X 0 0+(5265462787/10000000000 : ℝ)*X 0 1+(1348338643/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312403917/10000000000 : ℝ)*X 1 0+(-1061092097/5000000000 : ℝ)*X 1 1+(5393354529/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531240373/1000000000 : ℝ)*X 2 0+(1078670897/2000000000 : ℝ)*X 2 1+(-530546127/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4370065529/10000000000 : ℝ)*X 0 0+(44981783/100000000 : ℝ)*X 0 1+(424563637/1000000000 : ℝ)*X 0 2+(4370065529/10000000000 : ℝ)*X 1 0+(44981783/100000000 : ℝ)*X 1 1+(424563637/1000000000 : ℝ)*X 1 2+(4370065529/10000000000 : ℝ)*X 2 0+(44981783/100000000 : ℝ)*X 2 1+(424563637/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (271843771668243496846425297/23500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2181509349/100000000000000 : ℝ)*(base19) + (27431511/2000000000000 : ℝ)*(base23) + (318848423/100000000000000 : ℝ)*(upper3) + (1014119/12500000000000 : ℝ)*(upper4) + (121535639/50000000000000 : ℝ)*(upper5) + (5859945476012869/100000000000000 : ℝ)*(major0) + (5859945476012869/100000000000000 : ℝ)*(major1) + (5859945476012869/100000000000000 : ℝ)*(major2) + (3889946834259711/50000000000000 : ℝ)*(sp0) + (311198972152379/4000000000000 : ℝ)*(sp1) + (3889987556871637/50000000000000 : ℝ)*(sp2) + (3939873255548973/100000000000000 : ℝ)*(sp3) + (82816799401/100000000000000 : ℝ)*(sp4) + (40825563929/100000000000000 : ℝ)*(sp7) + (1969957040556451/50000000000000 : ℝ)*(f.failure) + (972497060664853/12500000000000 : ℝ)*(f.sum) + (1092572465523/235000000000000000000000000 : ℝ)*base66 + (105130349403374967/47000000000000000000000000000000 : ℝ)*base68 + (679488660838374967/47000000000000000000000000000000 : ℝ)*base70 + (453146923053374967/47000000000000000000000000000000 : ℝ)*base72 + (517971378677/58750000000000000000000000 : ℝ)*base74 + (329734104973374967/47000000000000000000000000000000 : ℝ)*base76 + (1020065140081374967/47000000000000000000000000000000 : ℝ)*base78 + (260595224174374967/47000000000000000000000000000000 : ℝ)*base80 + (1067490022993/235000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (4830953/625000000000000000000 : ℝ)*base89 + (4830953/625000000000000000000 : ℝ)*base91 + (4830953/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36431776224683585518256823/5875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (968496551/100000000000000 : ℝ)*(base19) + (572225611/100000000000000 : ℝ)*(base23) + (50020577/50000000000000 : ℝ)*(lower1) + (727229/4000000000000 : ℝ)*(lower4) + (5972561/5000000000000 : ℝ)*(upper5) + (2944708857993887/50000000000000 : ℝ)*(major0) + (2944708857993887/50000000000000 : ℝ)*(major1) + (2944708857993887/50000000000000 : ℝ)*(major2) + (513588337/50000000000000 : ℝ)*(sp0) + (25399633367/100000000000000 : ℝ)*(sp1) + (7819104558328571/100000000000000 : ℝ)*(sp4) + (244346225542979/3125000000000 : ℝ)*(sp5) + (1563821002655927/20000000000000 : ℝ)*(sp6) + (494966204970647/12500000000000 : ℝ)*(sp7) + (494966204970647/12500000000000 : ℝ)*(f.failure) + (1563821117101049/20000000000000 : ℝ)*(f.sum) + (1060338144777/235000000000000000000000000 : ℝ)*base65 + (416557105920306059/23500000000000000000000000000000 : ℝ)*base67 + (240555717801806059/23500000000000000000000000000000 : ℝ)*base69 + (279162693835806059/23500000000000000000000000000000 : ℝ)*base71 + (1332793232967/235000000000000000000000000 : ℝ)*base73 + (183433081968306059/23500000000000000000000000000000 : ℝ)*base75 + (401294286510806059/23500000000000000000000000000000 : ℝ)*base77 + (15013785832693941/23500000000000000000000000000000 : ℝ)*base80 + (329843874991/117500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1197859/156250000000000000000 : ℝ)*base90 + (1197859/156250000000000000000 : ℝ)*base92 + (1197859/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1104_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3507/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11303/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7013/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1104_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1104_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11303/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7013/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1104_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1104_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1104_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11303/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7013/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1104_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
