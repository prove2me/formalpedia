-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1241_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:19:22.216994+00:00
-- url     : https://prove2.me/submissions/14e9dd98-ce7c-43ae-b04c-36662e86220a

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
theorem support_rectangle_w1241_s3_0 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2117568833/10000000000 : ℝ)*x 0 + (216790061/400000000 : ℝ)*x 1 + (5240537189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117568833/10000000000 : ℝ)^4217 ≤ (12871601911067/100000000000000 : ℝ)^3193 := by
    have hnat : (2117568833 : ℕ)^4217*100000000000000^3193 ≤ 12871601911067^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117568833 10000000000 12871601911067 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216790061/400000000 : ℝ)^4217 ≤ (44531380011341/100000000000000 : ℝ)^3193 := by
    have hnat : (216790061 : ℕ)^4217*100000000000000^3193 ≤ 44531380011341^3193*400000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216790061 400000000 44531380011341 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240537189/10000000000 : ℝ)^4217 ≤ (42597018056773/100000000000000 : ℝ)^3193 := by
    have hnat : (5240537189 : ℕ)^4217*100000000000000^3193 ≤ 42597018056773^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240537189 10000000000 42597018056773 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2117568833/10000000000 : ℝ), (216790061/400000000 : ℝ), (5240537189/10000000000 : ℝ)] ![(12871601911067/100000000000000 : ℝ), (44531380011341/100000000000000 : ℝ), (42597018056773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2117568833/10000000000 : ℝ)|^4217 ≤ (12871601911067/100000000000000 : ℝ)^3193
        have hw : |(-2117568833/10000000000 : ℝ)|=(2117568833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216790061/400000000 : ℝ)|^4217 ≤ (44531380011341/100000000000000 : ℝ)^3193
        have hw : |(216790061/400000000 : ℝ)|=(216790061/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240537189/10000000000 : ℝ)|^4217 ≤ (42597018056773/100000000000000 : ℝ)^3193
        have hw : |(5240537189/10000000000 : ℝ)|=(5240537189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s3_1 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070302697/2000000000 : ℝ)*x 0 + (-276124351/1250000000 : ℝ)*x 1 + (5240537317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070302697/2000000000 : ℝ)^4217 ≤ (10948097828541/25000000000000 : ℝ)^3193 := by
    have hnat : (1070302697 : ℕ)^4217*25000000000000^3193 ≤ 10948097828541^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070302697 2000000000 10948097828541 25000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276124351/1250000000 : ℝ)^4217 ≤ (13610589240373/100000000000000 : ℝ)^3193 := by
    have hnat : (276124351 : ℕ)^4217*100000000000000^3193 ≤ 13610589240373^3193*1250000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276124351 1250000000 13610589240373 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240537317/10000000000 : ℝ)^4217 ≤ (42597019430873/100000000000000 : ℝ)^3193 := by
    have hnat : (5240537317 : ℕ)^4217*100000000000000^3193 ≤ 42597019430873^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240537317 10000000000 42597019430873 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070302697/2000000000 : ℝ), (-276124351/1250000000 : ℝ), (5240537317/10000000000 : ℝ)] ![(10948097828541/25000000000000 : ℝ), (13610589240373/100000000000000 : ℝ), (42597019430873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070302697/2000000000 : ℝ)|^4217 ≤ (10948097828541/25000000000000 : ℝ)^3193
        have hw : |(1070302697/2000000000 : ℝ)|=(1070302697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-276124351/1250000000 : ℝ)|^4217 ≤ (13610589240373/100000000000000 : ℝ)^3193
        have hw : |(-276124351/1250000000 : ℝ)|=(276124351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240537317/10000000000 : ℝ)|^4217 ≤ (42597019430873/100000000000000 : ℝ)^3193
        have hw : |(5240537317/10000000000 : ℝ)|=(5240537317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s3_2 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351513403/10000000000 : ℝ)*x 0 + (1310134437/2500000000 : ℝ)*x 1 + (-2208994347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351513403/10000000000 : ℝ)^4217 ≤ (21896195213973/50000000000000 : ℝ)^3193 := by
    have hnat : (5351513403 : ℕ)^4217*50000000000000^3193 ≤ 21896195213973^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351513403 10000000000 21896195213973 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310134437/2500000000 : ℝ)^4217 ≤ (21298512028861/50000000000000 : ℝ)^3193 := by
    have hnat : (1310134437 : ℕ)^4217*50000000000000^3193 ≤ 21298512028861^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310134437 2500000000 21298512028861 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2208994347/10000000000 : ℝ)^4217 ≤ (13610585489021/100000000000000 : ℝ)^3193 := by
    have hnat : (2208994347 : ℕ)^4217*100000000000000^3193 ≤ 13610585489021^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208994347 10000000000 13610585489021 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351513403/10000000000 : ℝ), (1310134437/2500000000 : ℝ), (-2208994347/10000000000 : ℝ)] ![(21896195213973/50000000000000 : ℝ), (21298512028861/50000000000000 : ℝ), (13610585489021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351513403/10000000000 : ℝ)|^4217 ≤ (21896195213973/50000000000000 : ℝ)^3193
        have hw : |(5351513403/10000000000 : ℝ)|=(5351513403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310134437/2500000000 : ℝ)|^4217 ≤ (21298512028861/50000000000000 : ℝ)^3193
        have hw : |(1310134437/2500000000 : ℝ)|=(1310134437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2208994347/10000000000 : ℝ)|^4217 ≤ (13610585489021/100000000000000 : ℝ)^3193
        have hw : |(-2208994347/10000000000 : ℝ)|=(2208994347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s3_3 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1087301627/2500000000 : ℝ)*x 0 + (4171156701/10000000000 : ℝ)*x 1 + (283414627/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087301627/2500000000 : ℝ)^4217 ≤ (1332010235347/4000000000000 : ℝ)^3193 := by
    have hnat : (1087301627 : ℕ)^4217*4000000000000^3193 ≤ 1332010235347^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087301627 2500000000 1332010235347 4000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171156701/10000000000 : ℝ)^4217 ≤ (3151172546793/10000000000000 : ℝ)^3193 := by
    have hnat : (4171156701 : ℕ)^4217*10000000000000^3193 ≤ 3151172546793^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171156701 10000000000 3151172546793 10000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283414627/625000000 : ℝ)^4217 ≤ (35188018636281/100000000000000 : ℝ)^3193 := by
    have hnat : (283414627 : ℕ)^4217*100000000000000^3193 ≤ 35188018636281^3193*625000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283414627 625000000 35188018636281 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087301627/2500000000 : ℝ), (4171156701/10000000000 : ℝ), (283414627/625000000 : ℝ)] ![(1332010235347/4000000000000 : ℝ), (3151172546793/10000000000000 : ℝ), (35188018636281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087301627/2500000000 : ℝ)|^4217 ≤ (1332010235347/4000000000000 : ℝ)^3193
        have hw : |(1087301627/2500000000 : ℝ)|=(1087301627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171156701/10000000000 : ℝ)|^4217 ≤ (3151172546793/10000000000000 : ℝ)^3193
        have hw : |(4171156701/10000000000 : ℝ)|=(4171156701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283414627/625000000 : ℝ)|^4217 ≤ (35188018636281/100000000000000 : ℝ)^3193
        have hw : |(283414627/625000000 : ℝ)|=(283414627/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s3_4 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-423516687/2000000000 : ℝ)*x 0 + (5241189067/10000000000 : ℝ)*x 1 + (1354773953/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423516687/2000000000 : ℝ)^4217 ≤ (3217929783499/25000000000000 : ℝ)^3193 := by
    have hnat : (423516687 : ℕ)^4217*25000000000000^3193 ≤ 3217929783499^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423516687 2000000000 3217929783499 25000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241189067/10000000000 : ℝ)^4217 ≤ (21302008101879/50000000000000 : ℝ)^3193 := by
    have hnat : (5241189067 : ℕ)^4217*50000000000000^3193 ≤ 21302008101879^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241189067 10000000000 21302008101879 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354773953/2500000000 : ℝ)^4217 ≤ (5565533081519/12500000000000 : ℝ)^3193 := by
    have hnat : (1354773953 : ℕ)^4217*12500000000000^3193 ≤ 5565533081519^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354773953 2500000000 5565533081519 12500000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-423516687/2000000000 : ℝ), (5241189067/10000000000 : ℝ), (1354773953/2500000000 : ℝ)] ![(3217929783499/25000000000000 : ℝ), (21302008101879/50000000000000 : ℝ), (5565533081519/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-423516687/2000000000 : ℝ)|^4217 ≤ (3217929783499/25000000000000 : ℝ)^3193
        have hw : |(-423516687/2000000000 : ℝ)|=(423516687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241189067/10000000000 : ℝ)|^4217 ≤ (21302008101879/50000000000000 : ℝ)^3193
        have hw : |(5241189067/10000000000 : ℝ)|=(5241189067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354773953/2500000000 : ℝ)|^4217 ≤ (5565533081519/12500000000000 : ℝ)^3193
        have hw : |(1354773953/2500000000 : ℝ)|=(1354773953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s3_5 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652897527/5000000000 : ℝ)*x 0 + (-507608981/2500000000 : ℝ)*x 1 + (5419095741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652897527/5000000000 : ℝ)^4217 ≤ (8659793174963/20000000000000 : ℝ)^3193 := by
    have hnat : (2652897527 : ℕ)^4217*20000000000000^3193 ≤ 8659793174963^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652897527 5000000000 8659793174963 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (507608981/2500000000 : ℝ)^4217 ≤ (12176770224581/100000000000000 : ℝ)^3193 := by
    have hnat : (507608981 : ℕ)^4217*100000000000000^3193 ≤ 12176770224581^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507608981 2500000000 12176770224581 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419095741/10000000000 : ℝ)^4217 ≤ (44524263881723/100000000000000 : ℝ)^3193 := by
    have hnat : (5419095741 : ℕ)^4217*100000000000000^3193 ≤ 44524263881723^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419095741 10000000000 44524263881723 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652897527/5000000000 : ℝ), (-507608981/2500000000 : ℝ), (5419095741/10000000000 : ℝ)] ![(8659793174963/20000000000000 : ℝ), (12176770224581/100000000000000 : ℝ), (44524263881723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652897527/5000000000 : ℝ)|^4217 ≤ (8659793174963/20000000000000 : ℝ)^3193
        have hw : |(2652897527/5000000000 : ℝ)|=(2652897527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-507608981/2500000000 : ℝ)|^4217 ≤ (12176770224581/100000000000000 : ℝ)^3193
        have hw : |(-507608981/2500000000 : ℝ)|=(507608981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419095741/10000000000 : ℝ)|^4217 ≤ (44524263881723/100000000000000 : ℝ)^3193
        have hw : |(5419095741/10000000000 : ℝ)|=(5419095741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s3_6 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061158937/2000000000 : ℝ)*x 0 + (5419096089/10000000000 : ℝ)*x 1 + (-40608719/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061158937/2000000000 : ℝ)^4217 ≤ (676546279653/1562500000000 : ℝ)^3193 := by
    have hnat : (1061158937 : ℕ)^4217*1562500000000^3193 ≤ 676546279653^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061158937 2000000000 676546279653 1562500000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419096089/10000000000 : ℝ)^4217 ≤ (44524267657913/100000000000000 : ℝ)^3193 := by
    have hnat : (5419096089 : ℕ)^4217*100000000000000^3193 ≤ 44524267657913^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419096089 10000000000 44524267657913 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40608719/200000000 : ℝ)^4217 ≤ (761048151907/6250000000000 : ℝ)^3193 := by
    have hnat : (40608719 : ℕ)^4217*6250000000000^3193 ≤ 761048151907^3193*200000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40608719 200000000 761048151907 6250000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061158937/2000000000 : ℝ), (5419096089/10000000000 : ℝ), (-40608719/200000000 : ℝ)] ![(676546279653/1562500000000 : ℝ), (44524267657913/100000000000000 : ℝ), (761048151907/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061158937/2000000000 : ℝ)|^4217 ≤ (676546279653/1562500000000 : ℝ)^3193
        have hw : |(1061158937/2000000000 : ℝ)|=(1061158937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419096089/10000000000 : ℝ)|^4217 ≤ (44524267657913/100000000000000 : ℝ)^3193
        have hw : |(5419096089/10000000000 : ℝ)|=(5419096089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-40608719/200000000 : ℝ)|^4217 ≤ (761048151907/6250000000000 : ℝ)^3193
        have hw : |(-40608719/200000000 : ℝ)|=(40608719/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s3_7 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (54365437/125000000 : ℝ)*x 0 + (4533312321/10000000000 : ℝ)*x 1 + (2086242669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54365437/125000000 : ℝ)^4217 ≤ (16650271797011/50000000000000 : ℝ)^3193 := by
    have hnat : (54365437 : ℕ)^4217*50000000000000^3193 ≤ 16650271797011^3193*125000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54365437 125000000 16650271797011 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4533312321/10000000000 : ℝ)^4217 ≤ (35174473809433/100000000000000 : ℝ)^3193 := by
    have hnat : (4533312321 : ℕ)^4217*100000000000000^3193 ≤ 35174473809433^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533312321 10000000000 35174473809433 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086242669/5000000000 : ℝ)^4217 ≤ (31524982578659/100000000000000 : ℝ)^3193 := by
    have hnat : (2086242669 : ℕ)^4217*100000000000000^3193 ≤ 31524982578659^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086242669 5000000000 31524982578659 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54365437/125000000 : ℝ), (4533312321/10000000000 : ℝ), (2086242669/5000000000 : ℝ)] ![(16650271797011/50000000000000 : ℝ), (35174473809433/100000000000000 : ℝ), (31524982578659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54365437/125000000 : ℝ)|^4217 ≤ (16650271797011/50000000000000 : ℝ)^3193
        have hw : |(54365437/125000000 : ℝ)|=(54365437/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4533312321/10000000000 : ℝ)|^4217 ≤ (35174473809433/100000000000000 : ℝ)^3193
        have hw : |(4533312321/10000000000 : ℝ)|=(4533312321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086242669/5000000000 : ℝ)|^4217 ≤ (31524982578659/100000000000000 : ℝ)^3193
        have hw : |(2086242669/5000000000 : ℝ)|=(2086242669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1241_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8113/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1899/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2727/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7351/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8113/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1899/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8113/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1899/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8113/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1899/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8113/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1899/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8113/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1899/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8113/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1899/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1899/20000 : ℝ) ^ (8433/2048 : ℝ) ≤ (770133137887479/12500000000000000000 : ℝ) := by
    have hpowers : (1899/20000 : ℝ)^8433 ≤ (770133137887479/12500000000000000000 : ℝ)^2048 := by
      have hnat : (1899 : ℕ)^8433*12500000000000000000^2048 ≤ 770133137887479^2048*20000^8433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1899 20000 770133137887479 12500000000000000000 8433 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1899/20000 : ℝ)) (X := (770133137887479/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8113/50000 : ℝ) ^ (8433/2048 : ℝ) ≤ (27981881225171517/50000000000000000000 : ℝ) := by
    have hpowers : (8113/50000 : ℝ)^8433 ≤ (27981881225171517/50000000000000000000 : ℝ)^2048 := by
      have hnat : (8113 : ℕ)^8433*50000000000000000000^2048 ≤ 27981881225171517^2048*50000^8433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8113 50000 27981881225171517 50000000000000000000 8433 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8113/50000 : ℝ)) (X := (27981881225171517/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250770133137887479/6250000000000000000 : ℝ) ≤ (10000299235687739/10000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (6250770133137887479/6250000000000000000 : ℝ)^2048 ≤ (10000299235687739/10000000000000000 : ℝ)^8433 := by
      have hnat : (6250770133137887479 : ℕ)^2048*10000000000000000^8433 ≤ 10000299235687739^8433*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250770133137887479 6250000000000000000 10000299235687739 10000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000299235687739/10000000000000000 : ℝ)) (X := (6250770133137887479/6250000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50031062413776721433/50000000000000000000 : ℝ) ≤ (10001508380581481/10000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (50031062413776721433/50000000000000000000 : ℝ)^2048 ≤ (10001508380581481/10000000000000000 : ℝ)^8433 := by
      have hnat : (50031062413776721433 : ℕ)^2048*10000000000000000^8433 ≤ 10001508380581481^8433*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031062413776721433 50000000000000000000 10001508380581481 10000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001508380581481/10000000000000000 : ℝ)) (X := (50031062413776721433/50000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25027981881225171517/25000000000000000000 : ℝ) ≤ (10002717525475223/10000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (25027981881225171517/25000000000000000000 : ℝ)^2048 ≤ (10002717525475223/10000000000000000 : ℝ)^8433 := by
      have hnat : (25027981881225171517 : ℕ)^2048*10000000000000000^8433 ≤ 10002717525475223^8433*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25027981881225171517 25000000000000000000 10002717525475223 10000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002717525475223/10000000000000000 : ℝ)) (X := (25027981881225171517/25000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(770133137887479/12500000000000000000 : ℝ) ≤ ((67289052493882010629/67310000000000000000 : ℝ)+2*(604572446871/336550000000000 : ℝ)*(1899/20000 : ℝ))^(8433/2048 : ℝ) := by
    rw [show (67289052493882010629/67310000000000000000 : ℝ)+2*(604572446871/336550000000000 : ℝ)*(1899/20000 : ℝ)=(10000299235687739/10000000000000000 : ℝ) by norm_num, show 1+2*(770133137887479/12500000000000000000 : ℝ)=(6250770133137887479/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27981881225171517/50000000000000000000 : ℝ)+(770133137887479/12500000000000000000 : ℝ) ≤ ((67289052493882010629/67310000000000000000 : ℝ)+(604572446871/336550000000000 : ℝ)*((8113/50000 : ℝ)+(1899/20000 : ℝ)))^(8433/2048 : ℝ) := by
    rw [show (67289052493882010629/67310000000000000000 : ℝ)+(604572446871/336550000000000 : ℝ)*((8113/50000 : ℝ)+(1899/20000 : ℝ))=(10001508380581481/10000000000000000 : ℝ) by norm_num, show 1+(27981881225171517/50000000000000000000 : ℝ)+(770133137887479/12500000000000000000 : ℝ)=(50031062413776721433/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27981881225171517/50000000000000000000 : ℝ) ≤ ((67289052493882010629/67310000000000000000 : ℝ)+2*(604572446871/336550000000000 : ℝ)*(8113/50000 : ℝ))^(8433/2048 : ℝ) := by
    rw [show (67289052493882010629/67310000000000000000 : ℝ)+2*(604572446871/336550000000000 : ℝ)*(8113/50000 : ℝ)=(10002717525475223/10000000000000000 : ℝ) by norm_num, show 1+2*(27981881225171517/50000000000000000000 : ℝ)=(25027981881225171517/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (67289052493882010629/67310000000000000000 : ℝ)*(X 1 0+X 2 0)+(604572446871/336550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (1899/20000 : ℝ)) (hi := (8113/50000 : ℝ)) (c := (67289052493882010629/67310000000000000000 : ℝ)) (alpha := (604572446871/336550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (67289052493882010629/67310000000000000000 : ℝ)*(X 0 1+X 2 1)+(604572446871/336550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (1899/20000 : ℝ)) (hi := (8113/50000 : ℝ)) (c := (67289052493882010629/67310000000000000000 : ℝ)) (alpha := (604572446871/336550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (67289052493882010629/67310000000000000000 : ℝ)*(X 0 2+X 1 2)+(604572446871/336550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (1899/20000 : ℝ)) (hi := (8113/50000 : ℝ)) (c := (67289052493882010629/67310000000000000000 : ℝ)) (alpha := (604572446871/336550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2117568833/10000000000 : ℝ)*X 0 0+(216790061/400000000 : ℝ)*X 0 1+(5240537189/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070302697/2000000000 : ℝ)*X 1 0+(-276124351/1250000000 : ℝ)*X 1 1+(5240537317/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351513403/10000000000 : ℝ)*X 2 0+(1310134437/2500000000 : ℝ)*X 2 1+(-2208994347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1087301627/2500000000 : ℝ)*X 0 0+(4171156701/10000000000 : ℝ)*X 0 1+(283414627/625000000 : ℝ)*X 0 2+(1087301627/2500000000 : ℝ)*X 1 0+(4171156701/10000000000 : ℝ)*X 1 1+(283414627/625000000 : ℝ)*X 1 2+(1087301627/2500000000 : ℝ)*X 2 0+(4171156701/10000000000 : ℝ)*X 2 1+(283414627/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-423516687/2000000000 : ℝ)*X 0 0+(5241189067/10000000000 : ℝ)*X 0 1+(1354773953/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652897527/5000000000 : ℝ)*X 1 0+(-507608981/2500000000 : ℝ)*X 1 1+(5419095741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061158937/2000000000 : ℝ)*X 2 0+(5419096089/10000000000 : ℝ)*X 2 1+(-40608719/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((54365437/125000000 : ℝ)*X 0 0+(4533312321/10000000000 : ℝ)*X 0 1+(2086242669/5000000000 : ℝ)*X 0 2+(54365437/125000000 : ℝ)*X 1 0+(4533312321/10000000000 : ℝ)*X 1 1+(2086242669/5000000000 : ℝ)*X 1 2+(54365437/125000000 : ℝ)*X 2 0+(4533312321/10000000000 : ℝ)*X 2 1+(2086242669/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19291862601700204582859708847/1682750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (906900459/50000000000000 : ℝ)*(base19) + (41273259/3125000000000 : ℝ)*(base23) + (109051959/50000000000000 : ℝ)*(lower2) + (18946801/100000000000000 : ℝ)*(upper3) + (227675737/100000000000000 : ℝ)*(upper5) + (2082809910333973/50000000000000 : ℝ)*(major0) + (2082809910333973/50000000000000 : ℝ)*(major1) + (2082809910333973/50000000000000 : ℝ)*(major2) + (2789975169911023/50000000000000 : ℝ)*(sp0) + (5579999811642813/100000000000000 : ℝ)*(sp1) + (5580000304699443/100000000000000 : ℝ)*(sp2) + (42987831142999/1562500000000 : ℝ)*(sp3) + (10257124337/20000000000000 : ℝ)*(sp4) + (8220295353/50000000000000 : ℝ)*(sp7) + (1375618816871321/50000000000000 : ℝ)*(f.failure) + (5580001625443731/100000000000000 : ℝ)*(f.sum) + (200468544746593/33655000000000000000000000000 : ℝ)*base66 + (13658304434363899017/3365500000000000000000000000000000 : ℝ)*base67 + (36395431654265399017/3365500000000000000000000000000000 : ℝ)*base69 + (4699125531700899017/3365500000000000000000000000000000 : ℝ)*base71 + (3148908318971/16827500000000000000000000000 : ℝ)*base73 + (56937094738306899017/3365500000000000000000000000000000 : ℝ)*base75 + (6959727762328899017/3365500000000000000000000000000000 : ℝ)*base77 + (110992480802769399017/3365500000000000000000000000000000 : ℝ)*base79 + (85829683290713/33655000000000000000000000000 : ℝ)*base82 + (20376297/5000000000000000000000 : ℝ)*base90 + (20376297/5000000000000000000000 : ℝ)*base92 + (20376297/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6071368690978286879079417303/841375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2201799509/100000000000000 : ℝ)*(base19) + (2094030879/100000000000000 : ℝ)*(base23) + (520681/390625000000 : ℝ)*(upper2) + (224988977/100000000000000 : ℝ)*(upper3) + (5383071/3125000000000 : ℝ)*(upper5) + (1049040638351631/25000000000000 : ℝ)*(major0) + (1049040638351631/25000000000000 : ℝ)*(major1) + (1049040638351631/25000000000000 : ℝ)*(major2) + (41651678187/100000000000000 : ℝ)*(sp1) + (22678070123/50000000000000 : ℝ)*(sp2) + (5620914888596339/100000000000000 : ℝ)*(sp4) + (5620871035118643/100000000000000 : ℝ)*(sp5) + (5620867438425213/100000000000000 : ℝ)*(sp6) + (86606561802597/3125000000000 : ℝ)*(sp7) + (86606561802597/3125000000000 : ℝ)*(f.failure) + (5620914888596339/100000000000000 : ℝ)*(f.sum) + (101082042552817/33655000000000000000000000000 : ℝ)*base66 + (9657620380174935899/1682750000000000000000000000000000 : ℝ)*base67 + (6173299176396685899/1682750000000000000000000000000000 : ℝ)*base69 + (7982259066184935899/1682750000000000000000000000000000 : ℝ)*base71 + (19932623905657/8413750000000000000000000000 : ℝ)*base73 + (5817929321476814101/1682750000000000000000000000000000 : ℝ)*base76 + (5107292198716564101/1682750000000000000000000000000000 : ℝ)*base78 + (13209447498121935899/1682750000000000000000000000000000 : ℝ)*base79 + (5036616709231/1051718750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1075029/312500000000000000000 : ℝ)*base90 + (1075029/312500000000000000000 : ℝ)*base92 + (1075029/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1241_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8113/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1899/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2727/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7351/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1241_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1241_s4_0 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-10599341/50000000 : ℝ)*x 0 + (674692459/1250000000 : ℝ)*x 1 + (5261242203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10599341/50000000 : ℝ)^4217 ≤ (12890064118787/100000000000000 : ℝ)^3193 := by
    have hnat : (10599341 : ℕ)^4217*100000000000000^3193 ≤ 12890064118787^3193*50000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10599341 50000000 12890064118787 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674692459/1250000000 : ℝ)^4217 ≤ (8858101139887/20000000000000 : ℝ)^3193 := by
    have hnat : (674692459 : ℕ)^4217*20000000000000^3193 ≤ 8858101139887^3193*1250000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674692459 1250000000 8858101139887 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261242203/10000000000 : ℝ)^4217 ≤ (21409715078171/50000000000000 : ℝ)^3193 := by
    have hnat : (5261242203 : ℕ)^4217*50000000000000^3193 ≤ 21409715078171^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261242203 10000000000 21409715078171 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10599341/50000000 : ℝ), (674692459/1250000000 : ℝ), (5261242203/10000000000 : ℝ)] ![(12890064118787/100000000000000 : ℝ), (8858101139887/20000000000000 : ℝ), (21409715078171/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10599341/50000000 : ℝ)|^4217 ≤ (12890064118787/100000000000000 : ℝ)^3193
        have hw : |(-10599341/50000000 : ℝ)|=(10599341/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674692459/1250000000 : ℝ)|^4217 ≤ (8858101139887/20000000000000 : ℝ)^3193
        have hw : |(674692459/1250000000 : ℝ)|=(674692459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261242203/10000000000 : ℝ)|^4217 ≤ (21409715078171/50000000000000 : ℝ)^3193
        have hw : |(5261242203/10000000000 : ℝ)|=(5261242203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s4_1 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672957091/5000000000 : ℝ)*x 0 + (-3420421/15625000 : ℝ)*x 1 + (5261242199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672957091/5000000000 : ℝ)^4217 ≤ (8746377359351/20000000000000 : ℝ)^3193 := by
    have hnat : (2672957091 : ℕ)^4217*20000000000000^3193 ≤ 8746377359351^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672957091 5000000000 8746377359351 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3420421/15625000 : ℝ)^4217 ≤ (13448683082751/100000000000000 : ℝ)^3193 := by
    have hnat : (3420421 : ℕ)^4217*100000000000000^3193 ≤ 13448683082751^3193*15625000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3420421 15625000 13448683082751 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261242199/10000000000 : ℝ)^4217 ≤ (42819430113347/100000000000000 : ℝ)^3193 := by
    have hnat : (5261242199 : ℕ)^4217*100000000000000^3193 ≤ 42819430113347^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261242199 10000000000 42819430113347 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672957091/5000000000 : ℝ), (-3420421/15625000 : ℝ), (5261242199/10000000000 : ℝ)] ![(8746377359351/20000000000000 : ℝ), (13448683082751/100000000000000 : ℝ), (42819430113347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672957091/5000000000 : ℝ)|^4217 ≤ (8746377359351/20000000000000 : ℝ)^3193
        have hw : |(2672957091/5000000000 : ℝ)|=(2672957091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3420421/15625000 : ℝ)|^4217 ≤ (13448683082751/100000000000000 : ℝ)^3193
        have hw : |(-3420421/15625000 : ℝ)|=(3420421/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261242199/10000000000 : ℝ)|^4217 ≤ (42819430113347/100000000000000 : ℝ)^3193
        have hw : |(5261242199/10000000000 : ℝ)|=(5261242199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s4_2 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213836567/400000000 : ℝ)*x 0 + (2630621111/5000000000 : ℝ)*x 1 + (-1094534709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213836567/400000000 : ℝ)^4217 ≤ (5466485840141/12500000000000 : ℝ)^3193 := by
    have hnat : (213836567 : ℕ)^4217*12500000000000^3193 ≤ 5466485840141^3193*400000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213836567 400000000 5466485840141 12500000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630621111/5000000000 : ℝ)^4217 ≤ (5352428795071/12500000000000 : ℝ)^3193 := by
    have hnat : (2630621111 : ℕ)^4217*12500000000000^3193 ≤ 5352428795071^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630621111 5000000000 5352428795071 12500000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094534709/5000000000 : ℝ)^4217 ≤ (13448682904247/100000000000000 : ℝ)^3193 := by
    have hnat : (1094534709 : ℕ)^4217*100000000000000^3193 ≤ 13448682904247^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094534709 5000000000 13448682904247 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213836567/400000000 : ℝ), (2630621111/5000000000 : ℝ), (-1094534709/5000000000 : ℝ)] ![(5466485840141/12500000000000 : ℝ), (5352428795071/12500000000000 : ℝ), (13448682904247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213836567/400000000 : ℝ)|^4217 ≤ (5466485840141/12500000000000 : ℝ)^3193
        have hw : |(213836567/400000000 : ℝ)|=(213836567/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630621111/5000000000 : ℝ)|^4217 ≤ (5352428795071/12500000000000 : ℝ)^3193
        have hw : |(2630621111/5000000000 : ℝ)|=(2630621111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1094534709/5000000000 : ℝ)|^4217 ≤ (13448682904247/100000000000000 : ℝ)^3193
        have hw : |(-1094534709/5000000000 : ℝ)|=(1094534709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s4_3 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4350584783/10000000000 : ℝ)*x 0 + (1053625413/2500000000 : ℝ)*x 1 + (4490937253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350584783/10000000000 : ℝ)^4217 ≤ (6662838774869/20000000000000 : ℝ)^3193 := by
    have hnat : (4350584783 : ℕ)^4217*20000000000000^3193 ≤ 6662838774869^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350584783 10000000000 6662838774869 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053625413/2500000000 : ℝ)^4217 ≤ (31944917287957/100000000000000 : ℝ)^3193 := by
    have hnat : (1053625413 : ℕ)^4217*100000000000000^3193 ≤ 31944917287957^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053625413 2500000000 31944917287957 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490937253/10000000000 : ℝ)^4217 ≤ (34740888826727/100000000000000 : ℝ)^3193 := by
    have hnat : (4490937253 : ℕ)^4217*100000000000000^3193 ≤ 34740888826727^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490937253 10000000000 34740888826727 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350584783/10000000000 : ℝ), (1053625413/2500000000 : ℝ), (4490937253/10000000000 : ℝ)] ![(6662838774869/20000000000000 : ℝ), (31944917287957/100000000000000 : ℝ), (34740888826727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350584783/10000000000 : ℝ)|^4217 ≤ (6662838774869/20000000000000 : ℝ)^3193
        have hw : |(4350584783/10000000000 : ℝ)|=(4350584783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053625413/2500000000 : ℝ)|^4217 ≤ (31944917287957/100000000000000 : ℝ)^3193
        have hw : |(1053625413/2500000000 : ℝ)|=(1053625413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490937253/10000000000 : ℝ)|^4217 ≤ (34740888826727/100000000000000 : ℝ)^3193
        have hw : |(4490937253/10000000000 : ℝ)|=(4490937253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s4_4 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2119874433/10000000000 : ℝ)*x 0 + (164425617/312500000 : ℝ)*x 1 + (5397160589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119874433/10000000000 : ℝ)^4217 ≤ (103120913391/800000000000 : ℝ)^3193 := by
    have hnat : (2119874433 : ℕ)^4217*800000000000^3193 ≤ 103120913391^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119874433 10000000000 103120913391 800000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164425617/312500000 : ℝ)^4217 ≤ (42823488290401/100000000000000 : ℝ)^3193 := by
    have hnat : (164425617 : ℕ)^4217*100000000000000^3193 ≤ 42823488290401^3193*312500000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164425617 312500000 42823488290401 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397160589/10000000000 : ℝ)^4217 ≤ (8857279504961/20000000000000 : ℝ)^3193 := by
    have hnat : (5397160589 : ℕ)^4217*20000000000000^3193 ≤ 8857279504961^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397160589 10000000000 8857279504961 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2119874433/10000000000 : ℝ), (164425617/312500000 : ℝ), (5397160589/10000000000 : ℝ)] ![(103120913391/800000000000 : ℝ), (42823488290401/100000000000000 : ℝ), (8857279504961/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2119874433/10000000000 : ℝ)|^4217 ≤ (103120913391/800000000000 : ℝ)^3193
        have hw : |(-2119874433/10000000000 : ℝ)|=(2119874433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164425617/312500000 : ℝ)|^4217 ≤ (42823488290401/100000000000000 : ℝ)^3193
        have hw : |(164425617/312500000 : ℝ)|=(164425617/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397160589/10000000000 : ℝ)|^4217 ≤ (8857279504961/20000000000000 : ℝ)^3193
        have hw : |(5397160589/10000000000 : ℝ)|=(5397160589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s4_5 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531114143/1000000000 : ℝ)*x 0 + (-1026575477/5000000000 : ℝ)*x 1 + (539716063/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531114143/1000000000 : ℝ)^4217 ≤ (2167829878439/5000000000000 : ℝ)^3193 := by
    have hnat : (531114143 : ℕ)^4217*5000000000000^3193 ≤ 2167829878439^3193*1000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531114143 1000000000 2167829878439 5000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026575477/5000000000 : ℝ)^4217 ≤ (12357004438179/100000000000000 : ℝ)^3193 := by
    have hnat : (1026575477 : ℕ)^4217*100000000000000^3193 ≤ 12357004438179^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026575477 5000000000 12357004438179 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539716063/1000000000 : ℝ)^4217 ≤ (44286397969123/100000000000000 : ℝ)^3193 := by
    have hnat : (539716063 : ℕ)^4217*100000000000000^3193 ≤ 44286397969123^3193*1000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539716063 1000000000 44286397969123 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531114143/1000000000 : ℝ), (-1026575477/5000000000 : ℝ), (539716063/1000000000 : ℝ)] ![(2167829878439/5000000000000 : ℝ), (12357004438179/100000000000000 : ℝ), (44286397969123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531114143/1000000000 : ℝ)|^4217 ≤ (2167829878439/5000000000000 : ℝ)^3193
        have hw : |(531114143/1000000000 : ℝ)|=(531114143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1026575477/5000000000 : ℝ)|^4217 ≤ (12357004438179/100000000000000 : ℝ)^3193
        have hw : |(-1026575477/5000000000 : ℝ)|=(1026575477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539716063/1000000000 : ℝ)|^4217 ≤ (44286397969123/100000000000000 : ℝ)^3193
        have hw : |(539716063/1000000000 : ℝ)|=(539716063/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s4_6 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062228289/2000000000 : ℝ)*x 0 + (1349290141/2500000000 : ℝ)*x 1 + (-128321939/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062228289/2000000000 : ℝ)^4217 ≤ (86713195461/200000000000 : ℝ)^3193 := by
    have hnat : (1062228289 : ℕ)^4217*200000000000^3193 ≤ 86713195461^3193*2000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062228289 2000000000 86713195461 200000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349290141/2500000000 : ℝ)^4217 ≤ (1107159931347/2500000000000 : ℝ)^3193 := by
    have hnat : (1349290141 : ℕ)^4217*2500000000000^3193 ≤ 1107159931347^3193*2500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349290141 2500000000 1107159931347 2500000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128321939/625000000 : ℝ)^4217 ≤ (12357004994589/100000000000000 : ℝ)^3193 := by
    have hnat : (128321939 : ℕ)^4217*100000000000000^3193 ≤ 12357004994589^3193*625000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128321939 625000000 12357004994589 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062228289/2000000000 : ℝ), (1349290141/2500000000 : ℝ), (-128321939/625000000 : ℝ)] ![(86713195461/200000000000 : ℝ), (1107159931347/2500000000000 : ℝ), (12357004994589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062228289/2000000000 : ℝ)|^4217 ≤ (86713195461/200000000000 : ℝ)^3193
        have hw : |(1062228289/2000000000 : ℝ)|=(1062228289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349290141/2500000000 : ℝ)|^4217 ≤ (1107159931347/2500000000000 : ℝ)^3193
        have hw : |(1349290141/2500000000 : ℝ)|=(1349290141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-128321939/625000000 : ℝ)|^4217 ≤ (12357004994589/100000000000000 : ℝ)^3193
        have hw : |(-128321939/625000000 : ℝ)|=(128321939/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s4_7 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4350597307/10000000000 : ℝ)*x 0 + (2245085731/5000000000 : ℝ)*x 1 + (4215270509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350597307/10000000000 : ℝ)^4217 ≤ (33314320531467/100000000000000 : ℝ)^3193 := by
    have hnat : (4350597307 : ℕ)^4217*100000000000000^3193 ≤ 33314320531467^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350597307 10000000000 33314320531467 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245085731/5000000000 : ℝ)^4217 ≤ (8683266305037/25000000000000 : ℝ)^3193 := by
    have hnat : (2245085731 : ℕ)^4217*25000000000000^3193 ≤ 8683266305037^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245085731 5000000000 8683266305037 25000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4215270509/10000000000 : ℝ)^4217 ≤ (31952614234999/100000000000000 : ℝ)^3193 := by
    have hnat : (4215270509 : ℕ)^4217*100000000000000^3193 ≤ 31952614234999^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215270509 10000000000 31952614234999 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350597307/10000000000 : ℝ), (2245085731/5000000000 : ℝ), (4215270509/10000000000 : ℝ)] ![(33314320531467/100000000000000 : ℝ), (8683266305037/25000000000000 : ℝ), (31952614234999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350597307/10000000000 : ℝ)|^4217 ≤ (33314320531467/100000000000000 : ℝ)^3193
        have hw : |(4350597307/10000000000 : ℝ)|=(4350597307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245085731/5000000000 : ℝ)|^4217 ≤ (8683266305037/25000000000000 : ℝ)^3193
        have hw : |(2245085731/5000000000 : ℝ)|=(2245085731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4215270509/10000000000 : ℝ)|^4217 ≤ (31952614234999/100000000000000 : ℝ)^3193
        have hw : |(4215270509/10000000000 : ℝ)|=(4215270509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1241_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7351/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2727/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (227/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7351/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2727/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7351/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2727/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7351/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2727/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7351/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2727/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7351/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2727/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7351/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2727/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2727/25000 : ℝ) ^ (8433/2048 : ℝ) ≤ (10908032504291071/100000000000000000000 : ℝ) := by
    have hpowers : (2727/25000 : ℝ)^8433 ≤ (10908032504291071/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2727 : ℕ)^8433*100000000000000000000^2048 ≤ 10908032504291071^2048*25000^8433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2727 25000 10908032504291071 100000000000000000000 8433 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2727/25000 : ℝ)) (X := (10908032504291071/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7351/50000 : ℝ) ^ (8433/2048 : ℝ) ≤ (18642152121847709/50000000000000000000 : ℝ) := by
    have hpowers : (7351/50000 : ℝ)^8433 ≤ (18642152121847709/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7351 : ℕ)^8433*50000000000000000000^2048 ≤ 18642152121847709^2048*50000^8433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7351 50000 18642152121847709 50000000000000000000 8433 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7351/50000 : ℝ)) (X := (18642152121847709/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010908032504291071/50000000000000000000 : ℝ) ≤ (5000264885637167/5000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (50010908032504291071/50000000000000000000 : ℝ)^2048 ≤ (5000264885637167/5000000000000000 : ℝ)^8433 := by
      have hnat : (50010908032504291071 : ℕ)^2048*5000000000000000^8433 ≤ 5000264885637167^8433*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010908032504291071 50000000000000000000 5000264885637167 5000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000264885637167/5000000000000000 : ℝ)) (X := (50010908032504291071/50000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048192336747986489/100000000000000000000 : ℝ) ≤ (1250146270461307/1250000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (100048192336747986489/100000000000000000000 : ℝ)^2048 ≤ (1250146270461307/1250000000000000 : ℝ)^8433 := by
      have hnat : (100048192336747986489 : ℕ)^2048*1250000000000000^8433 ≤ 1250146270461307^8433*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048192336747986489 100000000000000000000 1250146270461307 1250000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250146270461307/1250000000000000 : ℝ)) (X := (100048192336747986489/100000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018642152121847709/25000000000000000000 : ℝ) ≤ (5000905278053289/5000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (25018642152121847709/25000000000000000000 : ℝ)^2048 ≤ (5000905278053289/5000000000000000 : ℝ)^8433 := by
      have hnat : (25018642152121847709 : ℕ)^2048*5000000000000000^8433 ≤ 5000905278053289^8433*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018642152121847709 25000000000000000000 5000905278053289 5000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000905278053289/5000000000000000 : ℝ)) (X := (25018642152121847709/25000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10908032504291071/100000000000000000000 : ℝ) ≤ ((9482009787816176411/9485000000000000000 : ℝ)+2*(320196208061/189700000000000 : ℝ)*(2727/25000 : ℝ))^(8433/2048 : ℝ) := by
    rw [show (9482009787816176411/9485000000000000000 : ℝ)+2*(320196208061/189700000000000 : ℝ)*(2727/25000 : ℝ)=(5000264885637167/5000000000000000 : ℝ) by norm_num, show 1+2*(10908032504291071/100000000000000000000 : ℝ)=(50010908032504291071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18642152121847709/50000000000000000000 : ℝ)+(10908032504291071/100000000000000000000 : ℝ) ≤ ((9482009787816176411/9485000000000000000 : ℝ)+(320196208061/189700000000000 : ℝ)*((7351/50000 : ℝ)+(2727/25000 : ℝ)))^(8433/2048 : ℝ) := by
    rw [show (9482009787816176411/9485000000000000000 : ℝ)+(320196208061/189700000000000 : ℝ)*((7351/50000 : ℝ)+(2727/25000 : ℝ))=(1250146270461307/1250000000000000 : ℝ) by norm_num, show 1+(18642152121847709/50000000000000000000 : ℝ)+(10908032504291071/100000000000000000000 : ℝ)=(100048192336747986489/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18642152121847709/50000000000000000000 : ℝ) ≤ ((9482009787816176411/9485000000000000000 : ℝ)+2*(320196208061/189700000000000 : ℝ)*(7351/50000 : ℝ))^(8433/2048 : ℝ) := by
    rw [show (9482009787816176411/9485000000000000000 : ℝ)+2*(320196208061/189700000000000 : ℝ)*(7351/50000 : ℝ)=(5000905278053289/5000000000000000 : ℝ) by norm_num, show 1+2*(18642152121847709/50000000000000000000 : ℝ)=(25018642152121847709/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9482009787816176411/9485000000000000000 : ℝ)*(X 1 0+X 2 0)+(320196208061/189700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (2727/25000 : ℝ)) (hi := (7351/50000 : ℝ)) (c := (9482009787816176411/9485000000000000000 : ℝ)) (alpha := (320196208061/189700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9482009787816176411/9485000000000000000 : ℝ)*(X 0 1+X 2 1)+(320196208061/189700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (2727/25000 : ℝ)) (hi := (7351/50000 : ℝ)) (c := (9482009787816176411/9485000000000000000 : ℝ)) (alpha := (320196208061/189700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9482009787816176411/9485000000000000000 : ℝ)*(X 0 2+X 1 2)+(320196208061/189700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (2727/25000 : ℝ)) (hi := (7351/50000 : ℝ)) (c := (9482009787816176411/9485000000000000000 : ℝ)) (alpha := (320196208061/189700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-10599341/50000000 : ℝ)*X 0 0+(674692459/1250000000 : ℝ)*X 0 1+(5261242203/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672957091/5000000000 : ℝ)*X 1 0+(-3420421/15625000 : ℝ)*X 1 1+(5261242199/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213836567/400000000 : ℝ)*X 2 0+(2630621111/5000000000 : ℝ)*X 2 1+(-1094534709/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350584783/10000000000 : ℝ)*X 0 0+(1053625413/2500000000 : ℝ)*X 0 1+(4490937253/10000000000 : ℝ)*X 0 2+(4350584783/10000000000 : ℝ)*X 1 0+(1053625413/2500000000 : ℝ)*X 1 1+(4490937253/10000000000 : ℝ)*X 1 2+(4350584783/10000000000 : ℝ)*X 2 0+(1053625413/2500000000 : ℝ)*X 2 1+(4490937253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2119874433/10000000000 : ℝ)*X 0 0+(164425617/312500000 : ℝ)*X 0 1+(5397160589/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531114143/1000000000 : ℝ)*X 1 0+(-1026575477/5000000000 : ℝ)*X 1 1+(539716063/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062228289/2000000000 : ℝ)*X 2 0+(1349290141/2500000000 : ℝ)*X 2 1+(-128321939/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350597307/10000000000 : ℝ)*X 0 0+(2245085731/5000000000 : ℝ)*X 0 1+(4215270509/10000000000 : ℝ)*X 0 2+(4350597307/10000000000 : ℝ)*X 1 0+(2245085731/5000000000 : ℝ)*X 1 1+(4215270509/10000000000 : ℝ)*X 1 2+(4350597307/10000000000 : ℝ)*X 2 0+(2245085731/5000000000 : ℝ)*X 2 1+(4215270509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64883106994855902241089/9485000000000000000000000000 : ℝ) := by norm_num
    linear_combination (265494609/20000000000000 : ℝ)*(base19) + (1206542611/100000000000000 : ℝ)*(base23) + (59512499/100000000000000 : ℝ)*(lower2) + (156405233/100000000000000 : ℝ)*(upper3) + (52252089/50000000000000 : ℝ)*(upper5) + (5477238194282847/100000000000000 : ℝ)*(major0) + (5477238194282847/100000000000000 : ℝ)*(major1) + (5477238194282847/100000000000000 : ℝ)*(major2) + (1467385720605509/20000000000000 : ℝ)*(sp0) + (36684809171653/500000000000 : ℝ)*(sp1) + (1467392391052207/20000000000000 : ℝ)*(sp2) + (14130840748747/390625000000 : ℝ)*(sp3) + (345587761/1000000000000 : ℝ)*(sp4) + (4441765689/25000000000000 : ℝ)*(sp7) + (904378249685497/25000000000000 : ℝ)*(f.failure) + (1467392632360729/20000000000000 : ℝ)*(f.sum) + (28718586740387/9485000000000000000000000000 : ℝ)*base65 + (6414576895669327883/948500000000000000000000000000000 : ℝ)*base68 + (7261352982430827883/948500000000000000000000000000000 : ℝ)*base70 + (4720860745588672117/948500000000000000000000000000000 : ℝ)*base71 + (46559989214293/9485000000000000000000000000 : ℝ)*base74 + (2818944026883327883/948500000000000000000000000000000 : ℝ)*base76 + (1102236569726172117/948500000000000000000000000000000 : ℝ)*base77 + (517216535025672117/948500000000000000000000000000000 : ℝ)*base79 + (24641360637717/9485000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (8199671/2500000000000000000000 : ℝ)*base89 + (8199671/2500000000000000000000 : ℝ)*base91 + (8199671/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1727025346270795262084650041/237125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (784895581/50000000000000 : ℝ)*(base19) + (400125053/25000000000000 : ℝ)*(base23) + (136167391/100000000000000 : ℝ)*(upper3) + (4977113/25000000000000 : ℝ)*(lower4) + (34871477/20000000000000 : ℝ)*(upper5) + (2753881019107223/50000000000000 : ℝ)*(major0) + (2753881019107223/50000000000000 : ℝ)*(major1) + (2753881019107223/50000000000000 : ℝ)*(major2) + (9073551651/20000000000000 : ℝ)*(sp1) + (2571896229/6250000000000 : ℝ)*(sp2) + (7377850966331117/100000000000000 : ℝ)*(sp4) + (7377804028781699/100000000000000 : ℝ)*(sp5) + (7377808215491241/100000000000000 : ℝ)*(sp6) + (1818836433662457/50000000000000 : ℝ)*(sp7) + (1818836433662457/50000000000000 : ℝ)*(f.failure) + (7377850966331117/100000000000000 : ℝ)*(f.sum) + (4473516571761/9485000000000000000000000000 : ℝ)*base65 + (2148125286559466653/474250000000000000000000000000000 : ℝ)*base67 + (4523391793751716653/474250000000000000000000000000000 : ℝ)*base69 + (3687450554805966653/474250000000000000000000000000000 : ℝ)*base71 + (1233989639577/296406250000000000000000000 : ℝ)*base74 + (3703501303296783347/474250000000000000000000000000000 : ℝ)*base76 + (2731761652779716653/474250000000000000000000000000000 : ℝ)*base77 + (5080364418877533347/474250000000000000000000000000000 : ℝ)*base80 + (9639679541889/2371250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (66847049/5000000000000000000000 : ℝ)*base90 + (66847049/5000000000000000000000 : ℝ)*base92 + (66847049/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1241_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7351/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2727/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1241_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1241_s5_0 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-106015921/500000000 : ℝ)*x 0 + (5392435127/10000000000 : ℝ)*x 1 + (5266050923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106015921/500000000 : ℝ)^4217 ≤ (805854987677/6250000000000 : ℝ)^3193 := by
    have hnat : (106015921 : ℕ)^4217*6250000000000^3193 ≤ 805854987677^3193*500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106015921 500000000 805854987677 6250000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392435127/10000000000 : ℝ)^4217 ≤ (11058798702673/25000000000000 : ℝ)^3193 := by
    have hnat : (5392435127 : ℕ)^4217*25000000000000^3193 ≤ 11058798702673^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392435127 10000000000 11058798702673 25000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266050923/10000000000 : ℝ)^4217 ≤ (42871125376891/100000000000000 : ℝ)^3193 := by
    have hnat : (5266050923 : ℕ)^4217*100000000000000^3193 ≤ 42871125376891^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266050923 10000000000 42871125376891 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106015921/500000000 : ℝ), (5392435127/10000000000 : ℝ), (5266050923/10000000000 : ℝ)] ![(805854987677/6250000000000 : ℝ), (11058798702673/25000000000000 : ℝ), (42871125376891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106015921/500000000 : ℝ)|^4217 ≤ (805854987677/6250000000000 : ℝ)^3193
        have hw : |(-106015921/500000000 : ℝ)|=(106015921/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392435127/10000000000 : ℝ)|^4217 ≤ (11058798702673/25000000000000 : ℝ)^3193
        have hw : |(5392435127/10000000000 : ℝ)|=(5392435127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266050923/10000000000 : ℝ)|^4217 ≤ (42871125376891/100000000000000 : ℝ)^3193
        have hw : |(5266050923/10000000000 : ℝ)|=(5266050923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s5_1 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534462317/1000000000 : ℝ)*x 0 + (-109220779/500000000 : ℝ)*x 1 + (5266050907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534462317/1000000000 : ℝ)^4217 ≤ (21858969680411/50000000000000 : ℝ)^3193 := by
    have hnat : (534462317 : ℕ)^4217*50000000000000^3193 ≤ 21858969680411^3193*1000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534462317 1000000000 21858969680411 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109220779/500000000 : ℝ)^4217 ≤ (13410935419543/100000000000000 : ℝ)^3193 := by
    have hnat : (109220779 : ℕ)^4217*100000000000000^3193 ≤ 13410935419543^3193*500000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109220779 500000000 13410935419543 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266050907/10000000000 : ℝ)^4217 ≤ (42871125204861/100000000000000 : ℝ)^3193 := by
    have hnat : (5266050907 : ℕ)^4217*100000000000000^3193 ≤ 42871125204861^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266050907 10000000000 42871125204861 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534462317/1000000000 : ℝ), (-109220779/500000000 : ℝ), (5266050907/10000000000 : ℝ)] ![(21858969680411/50000000000000 : ℝ), (13410935419543/100000000000000 : ℝ), (42871125204861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534462317/1000000000 : ℝ)|^4217 ≤ (21858969680411/50000000000000 : ℝ)^3193
        have hw : |(534462317/1000000000 : ℝ)|=(534462317/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-109220779/500000000 : ℝ)|^4217 ≤ (13410935419543/100000000000000 : ℝ)^3193
        have hw : |(-109220779/500000000 : ℝ)|=(109220779/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266050907/10000000000 : ℝ)|^4217 ≤ (42871125204861/100000000000000 : ℝ)^3193
        have hw : |(5266050907/10000000000 : ℝ)|=(5266050907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s5_2 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344623073/10000000000 : ℝ)*x 0 + (52660509/100000000 : ℝ)*x 1 + (-2184415717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344623073/10000000000 : ℝ)^4217 ≤ (10929484578231/25000000000000 : ℝ)^3193 := by
    have hnat : (5344623073 : ℕ)^4217*25000000000000^3193 ≤ 10929484578231^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344623073 10000000000 10929484578231 25000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52660509/100000000 : ℝ)^4217 ≤ (21435562564799/50000000000000 : ℝ)^3193 := by
    have hnat : (52660509 : ℕ)^4217*50000000000000^3193 ≤ 21435562564799^3193*100000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52660509 100000000 21435562564799 50000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2184415717/10000000000 : ℝ)^4217 ≤ (1676367066297/12500000000000 : ℝ)^3193 := by
    have hnat : (2184415717 : ℕ)^4217*12500000000000^3193 ≤ 1676367066297^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184415717 10000000000 1676367066297 12500000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344623073/10000000000 : ℝ), (52660509/100000000 : ℝ), (-2184415717/10000000000 : ℝ)] ![(10929484578231/25000000000000 : ℝ), (21435562564799/50000000000000 : ℝ), (1676367066297/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344623073/10000000000 : ℝ)|^4217 ≤ (10929484578231/25000000000000 : ℝ)^3193
        have hw : |(5344623073/10000000000 : ℝ)|=(5344623073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52660509/100000000 : ℝ)|^4217 ≤ (21435562564799/50000000000000 : ℝ)^3193
        have hw : |(52660509/100000000 : ℝ)|=(52660509/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2184415717/10000000000 : ℝ)|^4217 ≤ (1676367066297/12500000000000 : ℝ)^3193
        have hw : |(-2184415717/10000000000 : ℝ)|=(2184415717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s5_3 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4350849921/10000000000 : ℝ)*x 0 + (2112260249/5000000000 : ℝ)*x 1 + (2240425319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350849921/10000000000 : ℝ)^4217 ≤ (8329218820083/25000000000000 : ℝ)^3193 := by
    have hnat : (4350849921 : ℕ)^4217*25000000000000^3193 ≤ 8329218820083^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350849921 10000000000 8329218820083 25000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112260249/5000000000 : ℝ)^4217 ≤ (32045250184849/100000000000000 : ℝ)^3193 := by
    have hnat : (2112260249 : ℕ)^4217*100000000000000^3193 ≤ 32045250184849^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112260249 5000000000 32045250184849 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2240425319/5000000000 : ℝ)^4217 ≤ (8659468629797/25000000000000 : ℝ)^3193 := by
    have hnat : (2240425319 : ℕ)^4217*25000000000000^3193 ≤ 8659468629797^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240425319 5000000000 8659468629797 25000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350849921/10000000000 : ℝ), (2112260249/5000000000 : ℝ), (2240425319/5000000000 : ℝ)] ![(8329218820083/25000000000000 : ℝ), (32045250184849/100000000000000 : ℝ), (8659468629797/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350849921/10000000000 : ℝ)|^4217 ≤ (8329218820083/25000000000000 : ℝ)^3193
        have hw : |(4350849921/10000000000 : ℝ)|=(4350849921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2112260249/5000000000 : ℝ)|^4217 ≤ (32045250184849/100000000000000 : ℝ)^3193
        have hw : |(2112260249/5000000000 : ℝ)|=(2112260249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2240425319/5000000000 : ℝ)|^4217 ≤ (8659468629797/25000000000000 : ℝ)^3193
        have hw : |(2240425319/5000000000 : ℝ)|=(2240425319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s5_4 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1060161687/5000000000 : ℝ)*x 0 + (8426201/16000000 : ℝ)*x 1 + (2696054603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060161687/5000000000 : ℝ)^4217 ≤ (2578743917883/20000000000000 : ℝ)^3193 := by
    have hnat : (1060161687 : ℕ)^4217*20000000000000^3193 ≤ 2578743917883^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060161687 5000000000 2578743917883 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8426201/16000000 : ℝ)^4217 ≤ (42874616569179/100000000000000 : ℝ)^3193 := by
    have hnat : (8426201 : ℕ)^4217*100000000000000^3193 ≤ 42874616569179^3193*16000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8426201 16000000 42874616569179 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696054603/5000000000 : ℝ)^4217 ≤ (44231663826017/100000000000000 : ℝ)^3193 := by
    have hnat : (2696054603 : ℕ)^4217*100000000000000^3193 ≤ 44231663826017^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696054603 5000000000 44231663826017 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1060161687/5000000000 : ℝ), (8426201/16000000 : ℝ), (2696054603/5000000000 : ℝ)] ![(2578743917883/20000000000000 : ℝ), (42874616569179/100000000000000 : ℝ), (44231663826017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1060161687/5000000000 : ℝ)|^4217 ≤ (2578743917883/20000000000000 : ℝ)^3193
        have hw : |(-1060161687/5000000000 : ℝ)|=(1060161687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8426201/16000000 : ℝ)|^4217 ≤ (42874616569179/100000000000000 : ℝ)^3193
        have hw : |(8426201/16000000 : ℝ)|=(8426201/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696054603/5000000000 : ℝ)|^4217 ≤ (44231663826017/100000000000000 : ℝ)^3193
        have hw : |(2696054603/5000000000 : ℝ)|=(2696054603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s5_5 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312378081/10000000000 : ℝ)*x 0 + (-1029178671/5000000000 : ℝ)*x 1 + (2696054603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312378081/10000000000 : ℝ)^4217 ≤ (43369930798947/100000000000000 : ℝ)^3193 := by
    have hnat : (5312378081 : ℕ)^4217*100000000000000^3193 ≤ 43369930798947^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312378081 10000000000 43369930798947 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029178671/5000000000 : ℝ)^4217 ≤ (1549800669737/12500000000000 : ℝ)^3193 := by
    have hnat : (1029178671 : ℕ)^4217*12500000000000^3193 ≤ 1549800669737^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029178671 5000000000 1549800669737 12500000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696054603/5000000000 : ℝ)^4217 ≤ (44231663826017/100000000000000 : ℝ)^3193 := by
    have hnat : (2696054603 : ℕ)^4217*100000000000000^3193 ≤ 44231663826017^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696054603 5000000000 44231663826017 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312378081/10000000000 : ℝ), (-1029178671/5000000000 : ℝ), (2696054603/5000000000 : ℝ)] ![(43369930798947/100000000000000 : ℝ), (1549800669737/12500000000000 : ℝ), (44231663826017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312378081/10000000000 : ℝ)|^4217 ≤ (43369930798947/100000000000000 : ℝ)^3193
        have hw : |(5312378081/10000000000 : ℝ)|=(5312378081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1029178671/5000000000 : ℝ)|^4217 ≤ (1549800669737/12500000000000 : ℝ)^3193
        have hw : |(-1029178671/5000000000 : ℝ)|=(1029178671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696054603/5000000000 : ℝ)|^4217 ≤ (44231663826017/100000000000000 : ℝ)^3193
        have hw : |(2696054603/5000000000 : ℝ)|=(2696054603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s5_6 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33202363/62500000 : ℝ)*x 0 + (5392109207/10000000000 : ℝ)*x 1 + (-1029178671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33202363/62500000 : ℝ)^4217 ≤ (8673986157633/20000000000000 : ℝ)^3193 := by
    have hnat : (33202363 : ℕ)^4217*20000000000000^3193 ≤ 8673986157633^3193*62500000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33202363 62500000 8673986157633 20000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392109207/10000000000 : ℝ)^4217 ≤ (44231663836851/100000000000000 : ℝ)^3193 := by
    have hnat : (5392109207 : ℕ)^4217*100000000000000^3193 ≤ 44231663836851^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392109207 10000000000 44231663836851 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029178671/5000000000 : ℝ)^4217 ≤ (1549800669737/12500000000000 : ℝ)^3193 := by
    have hnat : (1029178671 : ℕ)^4217*12500000000000^3193 ≤ 1549800669737^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029178671 5000000000 1549800669737 12500000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33202363/62500000 : ℝ), (5392109207/10000000000 : ℝ), (-1029178671/5000000000 : ℝ)] ![(8673986157633/20000000000000 : ℝ), (44231663836851/100000000000000 : ℝ), (1549800669737/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33202363/62500000 : ℝ)|^4217 ≤ (8673986157633/20000000000000 : ℝ)^3193
        have hw : |(33202363/62500000 : ℝ)|=(33202363/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392109207/10000000000 : ℝ)|^4217 ≤ (44231663836851/100000000000000 : ℝ)^3193
        have hw : |(5392109207/10000000000 : ℝ)|=(5392109207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1029178671/5000000000 : ℝ)|^4217 ≤ (1549800669737/12500000000000 : ℝ)^3193
        have hw : |(-1029178671/5000000000 : ℝ)|=(1029178671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1241_s5_7 (p : ℝ) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4350859897/10000000000 : ℝ)*x 0 + (2240095947/5000000000 : ℝ)*x 1 + (2112590851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350859897/10000000000 : ℝ)^4217 ≤ (33316976171103/100000000000000 : ℝ)^3193 := by
    have hnat : (4350859897 : ℕ)^4217*100000000000000^3193 ≤ 33316976171103^3193*10000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350859897 10000000000 33316976171103 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2240095947/5000000000 : ℝ)^4217 ≤ (34631149370609/100000000000000 : ℝ)^3193 := by
    have hnat : (2240095947 : ℕ)^4217*100000000000000^3193 ≤ 34631149370609^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240095947 5000000000 34631149370609 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112590851/5000000000 : ℝ)^4217 ≤ (32051874443761/100000000000000 : ℝ)^3193 := by
    have hnat : (2112590851 : ℕ)^4217*100000000000000^3193 ≤ 32051874443761^3193*5000000000^4217 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112590851 5000000000 32051874443761 100000000000000 4217 3193 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4217/1024 : ℝ)) 4217 3193 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350859897/10000000000 : ℝ), (2240095947/5000000000 : ℝ), (2112590851/5000000000 : ℝ)] ![(33316976171103/100000000000000 : ℝ), (34631149370609/100000000000000 : ℝ), (32051874443761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350859897/10000000000 : ℝ)|^4217 ≤ (33316976171103/100000000000000 : ℝ)^3193
        have hw : |(4350859897/10000000000 : ℝ)|=(4350859897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2240095947/5000000000 : ℝ)|^4217 ≤ (34631149370609/100000000000000 : ℝ)^3193
        have hw : |(2240095947/5000000000 : ℝ)|=(2240095947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2112590851/5000000000 : ℝ)|^4217 ≤ (32051874443761/100000000000000 : ℝ)^3193
        have hw : |(2112590851/5000000000 : ℝ)|=(2112590851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1241_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (2863/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1413/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (227/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (227/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (227/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (227/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (227/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (227/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (227/2000 : ℝ) ^ (8433/2048 : ℝ) ≤ (1605792254758547/12500000000000000000 : ℝ) := by
    have hpowers : (227/2000 : ℝ)^8433 ≤ (1605792254758547/12500000000000000000 : ℝ)^2048 := by
      have hnat : (227 : ℕ)^8433*12500000000000000000^2048 ≤ 1605792254758547^2048*2000^8433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        227 2000 1605792254758547 12500000000000000000 8433 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (227/2000 : ℝ)) (X := (1605792254758547/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (8433/2048 : ℝ) ≤ (16331339356987477/50000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^8433 ≤ (16331339356987477/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14237 : ℕ)^8433*50000000000000000000^2048 ≤ 16331339356987477^2048*100000^8433 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 16331339356987477 50000000000000000000 8433 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (16331339356987477/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251605792254758547/6250000000000000000 : ℝ) ≤ (10000623899957399/10000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (6251605792254758547/6250000000000000000 : ℝ)^2048 ≤ (10000623899957399/10000000000000000 : ℝ)^8433 := by
      have hnat : (6251605792254758547 : ℕ)^2048*10000000000000000^8433 ≤ 10000623899957399^8433*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251605792254758547 6250000000000000000 10000623899957399 10000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000623899957399/10000000000000000 : ℝ)) (X := (6251605792254758547/6250000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004550901675204333/10000000000000000000 : ℝ) ≤ (2500276255227217/2500000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (10004550901675204333/10000000000000000000 : ℝ)^2048 ≤ (2500276255227217/2500000000000000 : ℝ)^8433 := by
      have hnat : (10004550901675204333 : ℕ)^2048*2500000000000000^8433 ≤ 2500276255227217^8433*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004550901675204333 10000000000000000000 2500276255227217 2500000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500276255227217/2500000000000000 : ℝ)) (X := (10004550901675204333/10000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016331339356987477/25000000000000000000 : ℝ) ≤ (10001586141860337/10000000000000000 : ℝ) ^ (8433/2048 : ℝ) := by
    have hpowers : (25016331339356987477/25000000000000000000 : ℝ)^2048 ≤ (10001586141860337/10000000000000000 : ℝ)^8433 := by
      have hnat : (25016331339356987477 : ℕ)^2048*10000000000000000^8433 ≤ 10001586141860337^8433*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016331339356987477 25000000000000000000 10001586141860337 10000000000000000 2048 8433 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001586141860337/10000000000000000 : ℝ)) (X := (25016331339356987477/25000000000000000000 : ℝ)) (by norm_num) 8433 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1605792254758547/12500000000000000000 : ℝ) ≤ ((28860879753578664613/28870000000000000000 : ℝ)+2*(481120951469/288700000000000 : ℝ)*(227/2000 : ℝ))^(8433/2048 : ℝ) := by
    rw [show (28860879753578664613/28870000000000000000 : ℝ)+2*(481120951469/288700000000000 : ℝ)*(227/2000 : ℝ)=(10000623899957399/10000000000000000 : ℝ) by norm_num, show 1+2*(1605792254758547/12500000000000000000 : ℝ)=(6251605792254758547/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16331339356987477/50000000000000000000 : ℝ)+(1605792254758547/12500000000000000000 : ℝ) ≤ ((28860879753578664613/28870000000000000000 : ℝ)+(481120951469/288700000000000 : ℝ)*((14237/100000 : ℝ)+(227/2000 : ℝ)))^(8433/2048 : ℝ) := by
    rw [show (28860879753578664613/28870000000000000000 : ℝ)+(481120951469/288700000000000 : ℝ)*((14237/100000 : ℝ)+(227/2000 : ℝ))=(2500276255227217/2500000000000000 : ℝ) by norm_num, show 1+(16331339356987477/50000000000000000000 : ℝ)+(1605792254758547/12500000000000000000 : ℝ)=(10004550901675204333/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16331339356987477/50000000000000000000 : ℝ) ≤ ((28860879753578664613/28870000000000000000 : ℝ)+2*(481120951469/288700000000000 : ℝ)*(14237/100000 : ℝ))^(8433/2048 : ℝ) := by
    rw [show (28860879753578664613/28870000000000000000 : ℝ)+2*(481120951469/288700000000000 : ℝ)*(14237/100000 : ℝ)=(10001586141860337/10000000000000000 : ℝ) by norm_num, show 1+2*(16331339356987477/50000000000000000000 : ℝ)=(25016331339356987477/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28860879753578664613/28870000000000000000 : ℝ)*(X 1 0+X 2 0)+(481120951469/288700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (227/2000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (28860879753578664613/28870000000000000000 : ℝ)) (alpha := (481120951469/288700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28860879753578664613/28870000000000000000 : ℝ)*(X 0 1+X 2 1)+(481120951469/288700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (227/2000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (28860879753578664613/28870000000000000000 : ℝ)) (alpha := (481120951469/288700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28860879753578664613/28870000000000000000 : ℝ)*(X 0 2+X 1 2)+(481120951469/288700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8433/2048 : ℝ)) (lo := (227/2000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (28860879753578664613/28870000000000000000 : ℝ)) (alpha := (481120951469/288700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-106015921/500000000 : ℝ)*X 0 0+(5392435127/10000000000 : ℝ)*X 0 1+(5266050923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534462317/1000000000 : ℝ)*X 1 0+(-109220779/500000000 : ℝ)*X 1 1+(5266050907/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344623073/10000000000 : ℝ)*X 2 0+(52660509/100000000 : ℝ)*X 2 1+(-2184415717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350849921/10000000000 : ℝ)*X 0 0+(2112260249/5000000000 : ℝ)*X 0 1+(2240425319/5000000000 : ℝ)*X 0 2+(4350849921/10000000000 : ℝ)*X 1 0+(2112260249/5000000000 : ℝ)*X 1 1+(2240425319/5000000000 : ℝ)*X 1 2+(4350849921/10000000000 : ℝ)*X 2 0+(2112260249/5000000000 : ℝ)*X 2 1+(2240425319/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1060161687/5000000000 : ℝ)*X 0 0+(8426201/16000000 : ℝ)*X 0 1+(2696054603/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312378081/10000000000 : ℝ)*X 1 0+(-1029178671/5000000000 : ℝ)*X 1 1+(2696054603/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((33202363/62500000 : ℝ)*X 2 0+(5392109207/10000000000 : ℝ)*X 2 1+(-1029178671/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350859897/10000000000 : ℝ)*X 0 0+(2240095947/5000000000 : ℝ)*X 0 1+(2112590851/5000000000 : ℝ)*X 0 2+(4350859897/10000000000 : ℝ)*X 1 0+(2240095947/5000000000 : ℝ)*X 1 1+(2112590851/5000000000 : ℝ)*X 1 2+(4350859897/10000000000 : ℝ)*X 2 0+(2240095947/5000000000 : ℝ)*X 2 1+(2112590851/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1241_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (815287568895205942405553151/72175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (449546769/20000000000000 : ℝ)*(base19) + (9509063/500000000000 : ℝ)*(base23) + (2162613/2000000000000 : ℝ)*(lower2) + (423226389/100000000000000 : ℝ)*(upper3) + (25632957/100000000000000 : ℝ)*(upper5) + (295344543182409/5000000000000 : ℝ)*(major0) + (295344543182409/5000000000000 : ℝ)*(major1) + (295344543182409/5000000000000 : ℝ)*(major2) + (7912448841995361/100000000000000 : ℝ)*(sp0) + (7912496426716369/100000000000000 : ℝ)*(sp1) + (3956248386318807/50000000000000 : ℝ)*(sp2) + (195062327691221/5000000000000 : ℝ)*(sp3) + (49832454853/100000000000000 : ℝ)*(sp4) + (36122488947/100000000000000 : ℝ)*(sp7) + (1950641338156683/50000000000000 : ℝ)*(f.failure) + (3956249337225107/50000000000000 : ℝ)*(f.sum) + (2802926103747/577400000000000000000000000 : ℝ)*base66 + (1559059450888007283/144350000000000000000000000000000 : ℝ)*base68 + (775525812738242717/144350000000000000000000000000000 : ℝ)*base69 + (1160301371425342717/144350000000000000000000000000000 : ℝ)*base71 + (10064478101031/1443500000000000000000000000 : ℝ)*base74 + (3787053154106457283/144350000000000000000000000000000 : ℝ)*base76 + (871626693154857283/144350000000000000000000000000000 : ℝ)*base78 + (2049697685339807283/144350000000000000000000000000000 : ℝ)*base80 + (473321903801/360875000000000000000000000 : ℝ)*base82 + (58583931/5000000000000000000000 : ℝ)*base90 + (58583931/5000000000000000000000 : ℝ)*base92 + (58583931/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5859526301408755794372625167/721750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (364323007/25000000000000 : ℝ)*(base19) + (1582713323/100000000000000 : ℝ)*(base23) + (8177949/5000000000000 : ℝ)*(upper3) + (28865607/50000000000000 : ℝ)*(lower4) + (165964939/100000000000000 : ℝ)*(upper5) + (5937367439399647/100000000000000 : ℝ)*(major0) + (5937367439399647/100000000000000 : ℝ)*(major1) + (5937367439399647/100000000000000 : ℝ)*(major2) + (40294473033/100000000000000 : ℝ)*(sp1) + (10825133163/25000000000000 : ℝ)*(sp2) + (1988330820542237/25000000000000 : ℝ)*(sp4) + (497080095650243/6250000000000 : ℝ)*(sp5) + (3976639199461487/50000000000000 : ℝ)*(sp6) + (245088207875857/6250000000000 : ℝ)*(sp7) + (245088207875857/6250000000000 : ℝ)*(f.failure) + (1988330820542237/25000000000000 : ℝ)*(f.sum) + (131511633219723/14435000000000000000000000000 : ℝ)*base65 + (53774838139991891611/2887000000000000000000000000000000 : ℝ)*base67 + (1667403767483891611/2887000000000000000000000000000000 : ℝ)*base69 + (870799371653891611/2887000000000000000000000000000000 : ℝ)*base71 + (145679100992423/14435000000000000000000000000 : ℝ)*base73 + (13961553043006891611/2887000000000000000000000000000000 : ℝ)*base75 + (50080476603167891611/2887000000000000000000000000000000 : ℝ)*base77 + (17401594515274108389/2887000000000000000000000000000000 : ℝ)*base80 + (13792724102477/14435000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (10160849/625000000000000000000 : ℝ)*base90 + (10160849/625000000000000000000 : ℝ)*base92 + (10160849/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1241_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2863/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1413/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1241_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1241_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8113/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1899/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2863/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1413/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1241_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1241_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1241_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8433/2048 : ℝ) ≤ p) (hpb : p ≤ (4217/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151408943/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8113/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1899/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2863/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1413/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1241_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
