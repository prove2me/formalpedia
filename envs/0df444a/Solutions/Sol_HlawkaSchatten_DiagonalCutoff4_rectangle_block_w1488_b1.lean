-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1488_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:14:57.648292+00:00
-- url     : https://prove2.me/submissions/369095a9-5f72-4de8-a9eb-268887119778

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
theorem support_rectangle_w1488_s3_0 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-118962583/625000000 : ℝ)*x 0 + (5440676749/10000000000 : ℝ)*x 1 + (1303115779/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (118962583/625000000 : ℝ)^4473 ≤ (5815601375549/50000000000000 : ℝ)^3449 := by
    have hnat : (118962583 : ℕ)^4473*50000000000000^3449 ≤ 5815601375549^3449*625000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118962583 625000000 5815601375549 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440676749/10000000000 : ℝ)^4473 ≤ (45411818921781/100000000000000 : ℝ)^3449 := by
    have hnat : (5440676749 : ℕ)^4473*100000000000000^3449 ≤ 45411818921781^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440676749 10000000000 45411818921781 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303115779/2500000000 : ℝ)^4473 ≤ (21478489157897/50000000000000 : ℝ)^3449 := by
    have hnat : (1303115779 : ℕ)^4473*50000000000000^3449 ≤ 21478489157897^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303115779 2500000000 21478489157897 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-118962583/625000000 : ℝ), (5440676749/10000000000 : ℝ), (1303115779/2500000000 : ℝ)] ![(5815601375549/50000000000000 : ℝ), (45411818921781/100000000000000 : ℝ), (21478489157897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-118962583/625000000 : ℝ)|^4473 ≤ (5815601375549/50000000000000 : ℝ)^3449
        have hw : |(-118962583/625000000 : ℝ)|=(118962583/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440676749/10000000000 : ℝ)|^4473 ≤ (45411818921781/100000000000000 : ℝ)^3449
        have hw : |(5440676749/10000000000 : ℝ)|=(5440676749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303115779/2500000000 : ℝ)|^4473 ≤ (21478489157897/50000000000000 : ℝ)^3449
        have hw : |(1303115779/2500000000 : ℝ)|=(1303115779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s3_1 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535401119/1000000000 : ℝ)*x 0 + (-2020444129/10000000000 : ℝ)*x 1 + (2606231587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535401119/1000000000 : ℝ)^4473 ≤ (22237952214969/50000000000000 : ℝ)^3449 := by
    have hnat : (535401119 : ℕ)^4473*50000000000000^3449 ≤ 22237952214969^3449*1000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535401119 1000000000 22237952214969 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2020444129/10000000000 : ℝ)^4473 ≤ (12567116614281/100000000000000 : ℝ)^3449 := by
    have hnat : (2020444129 : ℕ)^4473*100000000000000^3449 ≤ 12567116614281^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020444129 10000000000 12567116614281 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2606231587/5000000000 : ℝ)^4473 ≤ (21478489467849/50000000000000 : ℝ)^3449 := by
    have hnat : (2606231587 : ℕ)^4473*50000000000000^3449 ≤ 21478489467849^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606231587 5000000000 21478489467849 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535401119/1000000000 : ℝ), (-2020444129/10000000000 : ℝ), (2606231587/5000000000 : ℝ)] ![(22237952214969/50000000000000 : ℝ), (12567116614281/100000000000000 : ℝ), (21478489467849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535401119/1000000000 : ℝ)|^4473 ≤ (22237952214969/50000000000000 : ℝ)^3449
        have hw : |(535401119/1000000000 : ℝ)|=(535401119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2020444129/10000000000 : ℝ)|^4473 ≤ (12567116614281/100000000000000 : ℝ)^3449
        have hw : |(-2020444129/10000000000 : ℝ)|=(2020444129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2606231587/5000000000 : ℝ)|^4473 ≤ (21478489467849/50000000000000 : ℝ)^3449
        have hw : |(2606231587/5000000000 : ℝ)|=(2606231587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s3_2 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354011103/10000000000 : ℝ)*x 0 + (260623167/500000000 : ℝ)*x 1 + (-80817761/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354011103/10000000000 : ℝ)^4473 ≤ (8895180698531/20000000000000 : ℝ)^3449 := by
    have hnat : (5354011103 : ℕ)^4473*20000000000000^3449 ≤ 8895180698531^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354011103 10000000000 8895180698531 20000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260623167/500000000 : ℝ)^4473 ≤ (8591396141981/20000000000000 : ℝ)^3449 := by
    have hnat : (260623167 : ℕ)^4473*20000000000000^3449 ≤ 8591396141981^3449*500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260623167 500000000 8591396141981 20000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80817761/400000000 : ℝ)^4473 ≤ (12567115775347/100000000000000 : ℝ)^3449 := by
    have hnat : (80817761 : ℕ)^4473*100000000000000^3449 ≤ 12567115775347^3449*400000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80817761 400000000 12567115775347 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354011103/10000000000 : ℝ), (260623167/500000000 : ℝ), (-80817761/400000000 : ℝ)] ![(8895180698531/20000000000000 : ℝ), (8591396141981/20000000000000 : ℝ), (12567115775347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354011103/10000000000 : ℝ)|^4473 ≤ (8895180698531/20000000000000 : ℝ)^3449
        have hw : |(5354011103/10000000000 : ℝ)|=(5354011103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260623167/500000000 : ℝ)|^4473 ≤ (8591396141981/20000000000000 : ℝ)^3449
        have hw : |(260623167/500000000 : ℝ)|=(260623167/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-80817761/400000000 : ℝ)|^4473 ≤ (12567115775347/100000000000000 : ℝ)^3449
        have hw : |(-80817761/400000000 : ℝ)|=(80817761/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s3_3 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4280669599/10000000000 : ℝ)*x 0 + (1008209677/2500000000 : ℝ)*x 1 + (1135398143/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4280669599/10000000000 : ℝ)^4473 ≤ (33274259553303/100000000000000 : ℝ)^3449 := by
    have hnat : (4280669599 : ℕ)^4473*100000000000000^3449 ≤ 33274259553303^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4280669599 10000000000 33274259553303 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1008209677/2500000000 : ℝ)^4473 ≤ (6159530882391/20000000000000 : ℝ)^3449 := by
    have hnat : (1008209677 : ℕ)^4473*20000000000000^3449 ≤ 6159530882391^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008209677 2500000000 6159530882391 20000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135398143/2500000000 : ℝ)^4473 ≤ (35928086023613/100000000000000 : ℝ)^3449 := by
    have hnat : (1135398143 : ℕ)^4473*100000000000000^3449 ≤ 35928086023613^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135398143 2500000000 35928086023613 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4280669599/10000000000 : ℝ), (1008209677/2500000000 : ℝ), (1135398143/2500000000 : ℝ)] ![(33274259553303/100000000000000 : ℝ), (6159530882391/20000000000000 : ℝ), (35928086023613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4280669599/10000000000 : ℝ)|^4473 ≤ (33274259553303/100000000000000 : ℝ)^3449
        have hw : |(4280669599/10000000000 : ℝ)|=(4280669599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1008209677/2500000000 : ℝ)|^4473 ≤ (6159530882391/20000000000000 : ℝ)^3449
        have hw : |(1008209677/2500000000 : ℝ)|=(1008209677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1135398143/2500000000 : ℝ)|^4473 ≤ (35928086023613/100000000000000 : ℝ)^3449
        have hw : |(1135398143/2500000000 : ℝ)|=(1135398143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s3_4 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-951717181/5000000000 : ℝ)*x 0 + (1303418939/2500000000 : ℝ)*x 1 + (1359863793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (951717181/5000000000 : ℝ)^4473 ≤ (11631464546639/100000000000000 : ℝ)^3449 := by
    have hnat : (951717181 : ℕ)^4473*100000000000000^3449 ≤ 11631464546639^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      951717181 5000000000 11631464546639 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303418939/2500000000 : ℝ)^4473 ≤ (21484969729673/50000000000000 : ℝ)^3449 := by
    have hnat : (1303418939 : ℕ)^4473*50000000000000^3449 ≤ 21484969729673^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303418939 2500000000 21484969729673 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359863793/2500000000 : ℝ)^4473 ≤ (45398595981137/100000000000000 : ℝ)^3449 := by
    have hnat : (1359863793 : ℕ)^4473*100000000000000^3449 ≤ 45398595981137^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359863793 2500000000 45398595981137 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-951717181/5000000000 : ℝ), (1303418939/2500000000 : ℝ), (1359863793/2500000000 : ℝ)] ![(11631464546639/100000000000000 : ℝ), (21484969729673/50000000000000 : ℝ), (45398595981137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-951717181/5000000000 : ℝ)|^4473 ≤ (11631464546639/100000000000000 : ℝ)^3449
        have hw : |(-951717181/5000000000 : ℝ)|=(951717181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303418939/2500000000 : ℝ)|^4473 ≤ (21484969729673/50000000000000 : ℝ)^3449
        have hw : |(1303418939/2500000000 : ℝ)|=(1303418939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359863793/2500000000 : ℝ)|^4473 ≤ (45398595981137/100000000000000 : ℝ)^3449
        have hw : |(1359863793/2500000000 : ℝ)|=(1359863793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s3_5 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294326993/10000000000 : ℝ)*x 0 + (-1793452131/10000000000 : ℝ)*x 1 + (5439455407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294326993/10000000000 : ℝ)^4473 ≤ (43833971878823/100000000000000 : ℝ)^3449 := by
    have hnat : (5294326993 : ℕ)^4473*100000000000000^3449 ≤ 43833971878823^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294326993 10000000000 43833971878823 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1793452131/10000000000 : ℝ)^4473 ≤ (5383714796153/50000000000000 : ℝ)^3449 := by
    have hnat : (1793452131 : ℕ)^4473*50000000000000^3449 ≤ 5383714796153^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793452131 10000000000 5383714796153 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439455407/10000000000 : ℝ)^4473 ≤ (22699299262403/50000000000000 : ℝ)^3449 := by
    have hnat : (5439455407 : ℕ)^4473*50000000000000^3449 ≤ 22699299262403^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439455407 10000000000 22699299262403 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294326993/10000000000 : ℝ), (-1793452131/10000000000 : ℝ), (5439455407/10000000000 : ℝ)] ![(43833971878823/100000000000000 : ℝ), (5383714796153/50000000000000 : ℝ), (22699299262403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294326993/10000000000 : ℝ)|^4473 ≤ (43833971878823/100000000000000 : ℝ)^3449
        have hw : |(5294326993/10000000000 : ℝ)|=(5294326993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1793452131/10000000000 : ℝ)|^4473 ≤ (5383714796153/50000000000000 : ℝ)^3449
        have hw : |(-1793452131/10000000000 : ℝ)|=(1793452131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439455407/10000000000 : ℝ)|^4473 ≤ (22699299262403/50000000000000 : ℝ)^3449
        have hw : |(5439455407/10000000000 : ℝ)|=(5439455407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s3_6 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294327113/10000000000 : ℝ)*x 0 + (5439455287/10000000000 : ℝ)*x 1 + (-1793452131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294327113/10000000000 : ℝ)^4473 ≤ (4383397316733/10000000000000 : ℝ)^3449 := by
    have hnat : (5294327113 : ℕ)^4473*10000000000000^3449 ≤ 4383397316733^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294327113 10000000000 4383397316733 10000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439455287/10000000000 : ℝ)^4473 ≤ (45398597225911/100000000000000 : ℝ)^3449 := by
    have hnat : (5439455287 : ℕ)^4473*100000000000000^3449 ≤ 45398597225911^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439455287 10000000000 45398597225911 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1793452131/10000000000 : ℝ)^4473 ≤ (5383714796153/50000000000000 : ℝ)^3449 := by
    have hnat : (1793452131 : ℕ)^4473*50000000000000^3449 ≤ 5383714796153^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793452131 10000000000 5383714796153 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294327113/10000000000 : ℝ), (5439455287/10000000000 : ℝ), (-1793452131/10000000000 : ℝ)] ![(4383397316733/10000000000000 : ℝ), (45398597225911/100000000000000 : ℝ), (5383714796153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294327113/10000000000 : ℝ)|^4473 ≤ (4383397316733/10000000000000 : ℝ)^3449
        have hw : |(5294327113/10000000000 : ℝ)|=(5294327113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439455287/10000000000 : ℝ)|^4473 ≤ (45398597225911/100000000000000 : ℝ)^3449
        have hw : |(5439455287/10000000000 : ℝ)|=(5439455287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1793452131/10000000000 : ℝ)|^4473 ≤ (5383714796153/50000000000000 : ℝ)^3449
        have hw : |(-1793452131/10000000000 : ℝ)|=(1793452131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s3_7 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4280744241/10000000000 : ℝ)*x 0 + (4538889889/10000000000 : ℝ)*x 1 + (4035561929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4280744241/10000000000 : ℝ)^4473 ≤ (1663750600957/5000000000000 : ℝ)^3449 := by
    have hnat : (4280744241 : ℕ)^4473*5000000000000^3449 ≤ 1663750600957^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4280744241 10000000000 1663750600957 5000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4538889889/10000000000 : ℝ)^4473 ≤ (4487544993913/12500000000000 : ℝ)^3449 := by
    have hnat : (4538889889 : ℕ)^4473*12500000000000^3449 ≤ 4487544993913^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4538889889 10000000000 4487544993913 12500000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4035561929/10000000000 : ℝ)^4473 ≤ (30824628011469/100000000000000 : ℝ)^3449 := by
    have hnat : (4035561929 : ℕ)^4473*100000000000000^3449 ≤ 30824628011469^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035561929 10000000000 30824628011469 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4280744241/10000000000 : ℝ), (4538889889/10000000000 : ℝ), (4035561929/10000000000 : ℝ)] ![(1663750600957/5000000000000 : ℝ), (4487544993913/12500000000000 : ℝ), (30824628011469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4280744241/10000000000 : ℝ)|^4473 ≤ (1663750600957/5000000000000 : ℝ)^3449
        have hw : |(4280744241/10000000000 : ℝ)|=(4280744241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4538889889/10000000000 : ℝ)|^4473 ≤ (4487544993913/12500000000000 : ℝ)^3449
        have hw : |(4538889889/10000000000 : ℝ)|=(4538889889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4035561929/10000000000 : ℝ)|^4473 ≤ (30824628011469/100000000000000 : ℝ)^3449
        have hw : |(4035561929/10000000000 : ℝ)|=(4035561929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1488_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3219/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10737/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15567/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3219/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3219/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3219/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3219/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3219/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3219/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10253/100000 : ℝ) ^ (4471/1024 : ℝ) ≤ (1199793873413037/25000000000000000000 : ℝ) := by
    have hpowers : (10253/100000 : ℝ)^4471 ≤ (1199793873413037/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10253 : ℕ)^4471*25000000000000000000^1024 ≤ 1199793873413037^1024*100000^4471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10253 100000 1199793873413037 25000000000000000000 4471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10253/100000 : ℝ)) (X := (1199793873413037/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3219/20000 : ℝ) ^ (4471/1024 : ℝ) ≤ (6875043971586807/20000000000000000000 : ℝ) := by
    have hpowers : (3219/20000 : ℝ)^4471 ≤ (6875043971586807/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3219 : ℕ)^4471*20000000000000000000^1024 ≤ 6875043971586807^1024*20000^4471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3219 20000 6875043971586807 20000000000000000000 4471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3219/20000 : ℝ)) (X := (6875043971586807/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501199793873413037/12500000000000000000 : ℝ) ≤ (2000043964874829/2000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (12501199793873413037/12500000000000000000 : ℝ)^1024 ≤ (2000043964874829/2000000000000000 : ℝ)^4471 := by
      have hnat : (12501199793873413037 : ℕ)^1024*2000000000000000^4471 ≤ 2000043964874829^4471*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501199793873413037 12500000000000000000 2000043964874829 2000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000043964874829/2000000000000000 : ℝ)) (X := (12501199793873413037/12500000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039174395351586183/100000000000000000000 : ℝ) ≤ (10000897081737707/10000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (100039174395351586183/100000000000000000000 : ℝ)^1024 ≤ (10000897081737707/10000000000000000 : ℝ)^4471 := by
      have hnat : (100039174395351586183 : ℕ)^1024*10000000000000000^4471 ≤ 10000897081737707^4471*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039174395351586183 100000000000000000000 10000897081737707 10000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000897081737707/10000000000000000 : ℝ)) (X := (100039174395351586183/100000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006875043971586807/10000000000000000000 : ℝ) ≤ (10001574339101269/10000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (10006875043971586807/10000000000000000000 : ℝ)^1024 ≤ (10001574339101269/10000000000000000 : ℝ)^4471 := by
      have hnat : (10006875043971586807 : ℕ)^1024*10000000000000000^4471 ≤ 10001574339101269^4471*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006875043971586807 10000000000000000000 10001574339101269 10000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001574339101269/10000000000000000 : ℝ)) (X := (10006875043971586807/10000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1199793873413037/25000000000000000000 : ℝ) ≤ ((29203698187248276359/29210000000000000000 : ℝ)+2*(338628681781/292100000000000 : ℝ)*(10253/100000 : ℝ))^(4471/1024 : ℝ) := by
    rw [show (29203698187248276359/29210000000000000000 : ℝ)+2*(338628681781/292100000000000 : ℝ)*(10253/100000 : ℝ)=(2000043964874829/2000000000000000 : ℝ) by norm_num, show 1+2*(1199793873413037/25000000000000000000 : ℝ)=(12501199793873413037/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6875043971586807/20000000000000000000 : ℝ)+(1199793873413037/25000000000000000000 : ℝ) ≤ ((29203698187248276359/29210000000000000000 : ℝ)+(338628681781/292100000000000 : ℝ)*((3219/20000 : ℝ)+(10253/100000 : ℝ)))^(4471/1024 : ℝ) := by
    rw [show (29203698187248276359/29210000000000000000 : ℝ)+(338628681781/292100000000000 : ℝ)*((3219/20000 : ℝ)+(10253/100000 : ℝ))=(10000897081737707/10000000000000000 : ℝ) by norm_num, show 1+(6875043971586807/20000000000000000000 : ℝ)+(1199793873413037/25000000000000000000 : ℝ)=(100039174395351586183/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6875043971586807/20000000000000000000 : ℝ) ≤ ((29203698187248276359/29210000000000000000 : ℝ)+2*(338628681781/292100000000000 : ℝ)*(3219/20000 : ℝ))^(4471/1024 : ℝ) := by
    rw [show (29203698187248276359/29210000000000000000 : ℝ)+2*(338628681781/292100000000000 : ℝ)*(3219/20000 : ℝ)=(10001574339101269/10000000000000000 : ℝ) by norm_num, show 1+2*(6875043971586807/20000000000000000000 : ℝ)=(10006875043971586807/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29203698187248276359/29210000000000000000 : ℝ)*(X 1 0+X 2 0)+(338628681781/292100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (10253/100000 : ℝ)) (hi := (3219/20000 : ℝ)) (c := (29203698187248276359/29210000000000000000 : ℝ)) (alpha := (338628681781/292100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29203698187248276359/29210000000000000000 : ℝ)*(X 0 1+X 2 1)+(338628681781/292100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (10253/100000 : ℝ)) (hi := (3219/20000 : ℝ)) (c := (29203698187248276359/29210000000000000000 : ℝ)) (alpha := (338628681781/292100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29203698187248276359/29210000000000000000 : ℝ)*(X 0 2+X 1 2)+(338628681781/292100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (10253/100000 : ℝ)) (hi := (3219/20000 : ℝ)) (c := (29203698187248276359/29210000000000000000 : ℝ)) (alpha := (338628681781/292100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-118962583/625000000 : ℝ)*X 0 0+(5440676749/10000000000 : ℝ)*X 0 1+(1303115779/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535401119/1000000000 : ℝ)*X 1 0+(-2020444129/10000000000 : ℝ)*X 1 1+(2606231587/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354011103/10000000000 : ℝ)*X 2 0+(260623167/500000000 : ℝ)*X 2 1+(-80817761/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4280669599/10000000000 : ℝ)*X 0 0+(1008209677/2500000000 : ℝ)*X 0 1+(1135398143/2500000000 : ℝ)*X 0 2+(4280669599/10000000000 : ℝ)*X 1 0+(1008209677/2500000000 : ℝ)*X 1 1+(1135398143/2500000000 : ℝ)*X 1 2+(4280669599/10000000000 : ℝ)*X 2 0+(1008209677/2500000000 : ℝ)*X 2 1+(1135398143/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-951717181/5000000000 : ℝ)*X 0 0+(1303418939/2500000000 : ℝ)*X 0 1+(1359863793/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294326993/10000000000 : ℝ)*X 1 0+(-1793452131/10000000000 : ℝ)*X 1 1+(5439455407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294327113/10000000000 : ℝ)*X 2 0+(5439455287/10000000000 : ℝ)*X 2 1+(-1793452131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4280744241/10000000000 : ℝ)*X 0 0+(4538889889/10000000000 : ℝ)*X 0 1+(4035561929/10000000000 : ℝ)*X 0 2+(4280744241/10000000000 : ℝ)*X 1 0+(4538889889/10000000000 : ℝ)*X 1 1+(4035561929/10000000000 : ℝ)*X 1 2+(4280744241/10000000000 : ℝ)*X 2 0+(4538889889/10000000000 : ℝ)*X 2 1+(4035561929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (877627996220965416817412931/182562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (729011779/50000000000000 : ℝ)*(base19) + (1181293403/100000000000000 : ℝ)*(base23) + (201777061/100000000000000 : ℝ)*(upper3) + (3438721/3125000000000 : ℝ)*(upper4) + (139355071/100000000000000 : ℝ)*(upper5) + (396719432146603/12500000000000 : ℝ)*(major0) + (396719432146603/12500000000000 : ℝ)*(major1) + (396719432146603/12500000000000 : ℝ)*(major2) + (2190941010988257/50000000000000 : ℝ)*(sp0) + (4381903545908557/100000000000000 : ℝ)*(sp1) + (547737977829839/12500000000000 : ℝ)*(sp2) + (1965595828720059/100000000000000 : ℝ)*(sp3) + (22981955601/100000000000000 : ℝ)*(sp4) + (9921450993/100000000000000 : ℝ)*(sp7) + (491401437542763/25000000000000 : ℝ)*(f.failure) + (876381000786423/20000000000000 : ℝ)*(f.sum) + (10242834335511/3651250000000000000000000000 : ℝ)*base65 + (2247679023560016523/365125000000000000000000000000000 : ℝ)*base68 + (1588988904728766523/365125000000000000000000000000000 : ℝ)*base70 + (179823651920858477/365125000000000000000000000000000 : ℝ)*base71 + (262982981317/1825625000000000000000000000 : ℝ)*base74 + (3252828449249016523/365125000000000000000000000000000 : ℝ)*base76 + (2403118518917608477/365125000000000000000000000000000 : ℝ)*base77 + (1962456422397266523/365125000000000000000000000000000 : ℝ)*base80 + (63610042734681/14605000000000000000000000000 : ℝ)*base82 + (9336013/1250000000000000000000 : ℝ)*base90 + (9336013/1250000000000000000000 : ℝ)*base92 + (9336013/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2219107062492646703757783261/365125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (733106693/100000000000000 : ℝ)*(base19) + (1053361819/100000000000000 : ℝ)*(base23) + (30409853/25000000000000 : ℝ)*(upper3) + (19023041/20000000000000 : ℝ)*(lower4) + (19239271/20000000000000 : ℝ)*(upper5) + (1603969120703393/50000000000000 : ℝ)*(major0) + (1603969120703393/50000000000000 : ℝ)*(major1) + (1603969120703393/50000000000000 : ℝ)*(major2) + (3488897093/25000000000000 : ℝ)*(sp1) + (3504522769/20000000000000 : ℝ)*(sp2) + (4429100065550763/100000000000000 : ℝ)*(sp4) + (2214542688427849/50000000000000 : ℝ)*(sp5) + (4429081489575099/100000000000000 : ℝ)*(sp6) + (993388107337003/50000000000000 : ℝ)*(sp7) + (993388107337003/50000000000000 : ℝ)*(f.failure) + (4429100065550763/100000000000000 : ℝ)*(f.sum) + (5651882477833/7302500000000000000000000000 : ℝ)*base65 + (4600294439125286087/1460500000000000000000000000000000 : ℝ)*base67 + (14987181810278713913/1460500000000000000000000000000000 : ℝ)*base70 + (6346315290293713913/1460500000000000000000000000000000 : ℝ)*base72 + (1770722992263/7302500000000000000000000000 : ℝ)*base73 + (4571736441947713913/1460500000000000000000000000000000 : ℝ)*base76 + (2092961645887713913/1460500000000000000000000000000000 : ℝ)*base78 + (12688577152417213913/1460500000000000000000000000000000 : ℝ)*base80 + (12849178284767/7302500000000000000000000000 : ℝ)*base82 + (3109747/2500000000000000000000 : ℝ)*base89 + (3109747/2500000000000000000000 : ℝ)*base91 + (3109747/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1488_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3219/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10737/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15567/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1488_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1488_s4_0 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1903977791/10000000000 : ℝ)*x 0 + (5436935867/10000000000 : ℝ)*x 1 + (5215823727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1903977791/10000000000 : ℝ)^4473 ≤ (181808928641/1562500000000 : ℝ)^3449 := by
    have hnat : (1903977791 : ℕ)^4473*1562500000000^3449 ≤ 181808928641^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903977791 10000000000 181808928641 1562500000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436935867/10000000000 : ℝ)^4473 ≤ (45371328588723/100000000000000 : ℝ)^3449 := by
    have hnat : (5436935867 : ℕ)^4473*100000000000000^3449 ≤ 45371328588723^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436935867 10000000000 45371328588723 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215823727/10000000000 : ℝ)^4473 ≤ (42992899962371/100000000000000 : ℝ)^3449 := by
    have hnat : (5215823727 : ℕ)^4473*100000000000000^3449 ≤ 42992899962371^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215823727 10000000000 42992899962371 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1903977791/10000000000 : ℝ), (5436935867/10000000000 : ℝ), (5215823727/10000000000 : ℝ)] ![(181808928641/1562500000000 : ℝ), (45371328588723/100000000000000 : ℝ), (42992899962371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1903977791/10000000000 : ℝ)|^4473 ≤ (181808928641/1562500000000 : ℝ)^3449
        have hw : |(-1903977791/10000000000 : ℝ)|=(1903977791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436935867/10000000000 : ℝ)|^4473 ≤ (45371328588723/100000000000000 : ℝ)^3449
        have hw : |(5436935867/10000000000 : ℝ)|=(5436935867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215823727/10000000000 : ℝ)|^4473 ≤ (42992899962371/100000000000000 : ℝ)^3449
        have hw : |(5215823727/10000000000 : ℝ)|=(5215823727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s4_1 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83641221/156250000 : ℝ)*x 0 + (-1008645841/5000000000 : ℝ)*x 1 + (41726579/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83641221/156250000 : ℝ)^4473 ≤ (44465421736827/100000000000000 : ℝ)^3449 := by
    have hnat : (83641221 : ℕ)^4473*100000000000000^3449 ≤ 44465421736827^3449*156250000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83641221 156250000 44465421736827 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1008645841/5000000000 : ℝ)^4473 ≤ (6270846372203/50000000000000 : ℝ)^3449 := by
    have hnat : (1008645841 : ℕ)^4473*50000000000000^3449 ≤ 6270846372203^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008645841 5000000000 6270846372203 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41726579/80000000 : ℝ)^4473 ≤ (4299288550943/10000000000000 : ℝ)^3449 := by
    have hnat : (41726579 : ℕ)^4473*10000000000000^3449 ≤ 4299288550943^3449*80000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41726579 80000000 4299288550943 10000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83641221/156250000 : ℝ), (-1008645841/5000000000 : ℝ), (41726579/80000000 : ℝ)] ![(44465421736827/100000000000000 : ℝ), (6270846372203/50000000000000 : ℝ), (4299288550943/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83641221/156250000 : ℝ)|^4473 ≤ (44465421736827/100000000000000 : ℝ)^3449
        have hw : |(83641221/156250000 : ℝ)|=(83641221/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1008645841/5000000000 : ℝ)|^4473 ≤ (6270846372203/50000000000000 : ℝ)^3449
        have hw : |(-1008645841/5000000000 : ℝ)|=(1008645841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41726579/80000000 : ℝ)|^4473 ≤ (4299288550943/10000000000000 : ℝ)^3449
        have hw : |(41726579/80000000 : ℝ)|=(41726579/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s4_2 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338259357/2500000000 : ℝ)*x 0 + (521582333/1000000000 : ℝ)*x 1 + (-2017291373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338259357/2500000000 : ℝ)^4473 ≤ (11116353505879/25000000000000 : ℝ)^3449 := by
    have hnat : (1338259357 : ℕ)^4473*25000000000000^3449 ≤ 11116353505879^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338259357 2500000000 11116353505879 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521582333/1000000000 : ℝ)^4473 ≤ (42992895718423/100000000000000 : ℝ)^3449 := by
    have hnat : (521582333 : ℕ)^4473*100000000000000^3449 ≤ 42992895718423^3449*1000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521582333 1000000000 42992895718423 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2017291373/10000000000 : ℝ)^4473 ≤ (12541690252959/100000000000000 : ℝ)^3449 := by
    have hnat : (2017291373 : ℕ)^4473*100000000000000^3449 ≤ 12541690252959^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017291373 10000000000 12541690252959 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338259357/2500000000 : ℝ), (521582333/1000000000 : ℝ), (-2017291373/10000000000 : ℝ)] ![(11116353505879/25000000000000 : ℝ), (42992895718423/100000000000000 : ℝ), (12541690252959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338259357/2500000000 : ℝ)|^4473 ≤ (11116353505879/25000000000000 : ℝ)^3449
        have hw : |(1338259357/2500000000 : ℝ)|=(1338259357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521582333/1000000000 : ℝ)|^4473 ≤ (42992895718423/100000000000000 : ℝ)^3449
        have hw : |(521582333/1000000000 : ℝ)|=(521582333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2017291373/10000000000 : ℝ)|^4473 ≤ (12541690252959/100000000000000 : ℝ)^3449
        have hw : |(-2017291373/10000000000 : ℝ)|=(2017291373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s4_3 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214051357/500000000 : ℝ)*x 0 + (4040710767/10000000000 : ℝ)*x 1 + (4533637759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214051357/500000000 : ℝ)^4473 ≤ (16638931979347/50000000000000 : ℝ)^3449 := by
    have hnat : (214051357 : ℕ)^4473*50000000000000^3449 ≤ 16638931979347^3449*500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214051357 500000000 16638931979347 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4040710767/10000000000 : ℝ)^4473 ≤ (30875642199999/100000000000000 : ℝ)^3449 := by
    have hnat : (4040710767 : ℕ)^4473*100000000000000^3449 ≤ 30875642199999^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4040710767 10000000000 30875642199999 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4533637759/10000000000 : ℝ)^4473 ≤ (1792324691537/5000000000000 : ℝ)^3449 := by
    have hnat : (4533637759 : ℕ)^4473*5000000000000^3449 ≤ 1792324691537^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533637759 10000000000 1792324691537 5000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214051357/500000000 : ℝ), (4040710767/10000000000 : ℝ), (4533637759/10000000000 : ℝ)] ![(16638931979347/50000000000000 : ℝ), (30875642199999/100000000000000 : ℝ), (1792324691537/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214051357/500000000 : ℝ)|^4473 ≤ (16638931979347/50000000000000 : ℝ)^3449
        have hw : |(214051357/500000000 : ℝ)|=(214051357/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4040710767/10000000000 : ℝ)|^4473 ≤ (30875642199999/100000000000000 : ℝ)^3449
        have hw : |(4040710767/10000000000 : ℝ)|=(4040710767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4533637759/10000000000 : ℝ)|^4473 ≤ (1792324691537/5000000000000 : ℝ)^3449
        have hw : |(4533637759/10000000000 : ℝ)|=(4533637759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s4_4 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-952004249/5000000000 : ℝ)*x 0 + (130424031/250000000 : ℝ)*x 1 + (543578973/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (952004249/5000000000 : ℝ)^4473 ≤ (727250925553/6250000000000 : ℝ)^3449 := by
    have hnat : (952004249 : ℕ)^4473*6250000000000^3449 ≤ 727250925553^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952004249 5000000000 727250925553 6250000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130424031/250000000 : ℝ)^4473 ≤ (43005060421331/100000000000000 : ℝ)^3449 := by
    have hnat : (130424031 : ℕ)^4473*100000000000000^3449 ≤ 43005060421331^3449*250000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130424031 250000000 43005060421331 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543578973/1000000000 : ℝ)^4473 ≤ (45358924755121/100000000000000 : ℝ)^3449 := by
    have hnat : (543578973 : ℕ)^4473*100000000000000^3449 ≤ 45358924755121^3449*1000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543578973 1000000000 45358924755121 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-952004249/5000000000 : ℝ), (130424031/250000000 : ℝ), (543578973/1000000000 : ℝ)] ![(727250925553/6250000000000 : ℝ), (43005060421331/100000000000000 : ℝ), (45358924755121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-952004249/5000000000 : ℝ)|^4473 ≤ (727250925553/6250000000000 : ℝ)^3449
        have hw : |(-952004249/5000000000 : ℝ)|=(952004249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130424031/250000000 : ℝ)|^4473 ≤ (43005060421331/100000000000000 : ℝ)^3449
        have hw : |(130424031/250000000 : ℝ)|=(130424031/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543578973/1000000000 : ℝ)|^4473 ≤ (45358924755121/100000000000000 : ℝ)^3449
        have hw : |(543578973/1000000000 : ℝ)|=(543578973/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s4_5 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165475399/312500000 : ℝ)*x 0 + (-179732471/1000000000 : ℝ)*x 1 + (2717894863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165475399/312500000 : ℝ)^4473 ≤ (4384348318083/10000000000000 : ℝ)^3449 := by
    have hnat : (165475399 : ℕ)^4473*10000000000000^3449 ≤ 4384348318083^3449*312500000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165475399 312500000 4384348318083 10000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179732471/1000000000 : ℝ)^4473 ≤ (5398796046981/50000000000000 : ℝ)^3449 := by
    have hnat : (179732471 : ℕ)^4473*50000000000000^3449 ≤ 5398796046981^3449*1000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179732471 1000000000 5398796046981 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717894863/5000000000 : ℝ)^4473 ≤ (45358924711833/100000000000000 : ℝ)^3449 := by
    have hnat : (2717894863 : ℕ)^4473*100000000000000^3449 ≤ 45358924711833^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717894863 5000000000 45358924711833 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165475399/312500000 : ℝ), (-179732471/1000000000 : ℝ), (2717894863/5000000000 : ℝ)] ![(4384348318083/10000000000000 : ℝ), (5398796046981/50000000000000 : ℝ), (45358924711833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165475399/312500000 : ℝ)|^4473 ≤ (4384348318083/10000000000000 : ℝ)^3449
        have hw : |(165475399/312500000 : ℝ)|=(165475399/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-179732471/1000000000 : ℝ)|^4473 ≤ (5398796046981/50000000000000 : ℝ)^3449
        have hw : |(-179732471/1000000000 : ℝ)|=(179732471/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717894863/5000000000 : ℝ)|^4473 ≤ (45358924711833/100000000000000 : ℝ)^3449
        have hw : |(2717894863/5000000000 : ℝ)|=(2717894863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s4_6 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647606381/5000000000 : ℝ)*x 0 + (5435789729/10000000000 : ℝ)*x 1 + (-359464943/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647606381/5000000000 : ℝ)^4473 ≤ (21921741558201/50000000000000 : ℝ)^3449 := by
    have hnat : (2647606381 : ℕ)^4473*50000000000000^3449 ≤ 21921741558201^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647606381 5000000000 21921741558201 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435789729/10000000000 : ℝ)^4473 ≤ (45358924744299/100000000000000 : ℝ)^3449 := by
    have hnat : (5435789729 : ℕ)^4473*100000000000000^3449 ≤ 45358924744299^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435789729 10000000000 45358924744299 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (359464943/2000000000 : ℝ)^4473 ≤ (5398796066459/50000000000000 : ℝ)^3449 := by
    have hnat : (359464943 : ℕ)^4473*50000000000000^3449 ≤ 5398796066459^3449*2000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359464943 2000000000 5398796066459 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647606381/5000000000 : ℝ), (5435789729/10000000000 : ℝ), (-359464943/2000000000 : ℝ)] ![(21921741558201/50000000000000 : ℝ), (45358924744299/100000000000000 : ℝ), (5398796066459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647606381/5000000000 : ℝ)|^4473 ≤ (21921741558201/50000000000000 : ℝ)^3449
        have hw : |(2647606381/5000000000 : ℝ)|=(2647606381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435789729/10000000000 : ℝ)|^4473 ≤ (45358924744299/100000000000000 : ℝ)^3449
        have hw : |(5435789729/10000000000 : ℝ)|=(5435789729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-359464943/2000000000 : ℝ)|^4473 ≤ (5398796066459/50000000000000 : ℝ)^3449
        have hw : |(-359464943/2000000000 : ℝ)|=(359464943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s4_7 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (856219219/2000000000 : ℝ)*x 0 + (2265549581/5000000000 : ℝ)*x 1 + (4043267011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (856219219/2000000000 : ℝ)^4473 ≤ (33278559110997/100000000000000 : ℝ)^3449 := by
    have hnat : (856219219 : ℕ)^4473*100000000000000^3449 ≤ 33278559110997^3449*2000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856219219 2000000000 33278559110997 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2265549581/5000000000 : ℝ)^4473 ≤ (35820464486519/100000000000000 : ℝ)^3449 := by
    have hnat : (2265549581 : ℕ)^4473*100000000000000^3449 ≤ 35820464486519^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265549581 5000000000 35820464486519 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4043267011/10000000000 : ℝ)^4473 ≤ (15450488194959/50000000000000 : ℝ)^3449 := by
    have hnat : (4043267011 : ℕ)^4473*50000000000000^3449 ≤ 15450488194959^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4043267011 10000000000 15450488194959 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(856219219/2000000000 : ℝ), (2265549581/5000000000 : ℝ), (4043267011/10000000000 : ℝ)] ![(33278559110997/100000000000000 : ℝ), (35820464486519/100000000000000 : ℝ), (15450488194959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(856219219/2000000000 : ℝ)|^4473 ≤ (33278559110997/100000000000000 : ℝ)^3449
        have hw : |(856219219/2000000000 : ℝ)|=(856219219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2265549581/5000000000 : ℝ)|^4473 ≤ (35820464486519/100000000000000 : ℝ)^3449
        have hw : |(2265549581/5000000000 : ℝ)|=(2265549581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4043267011/10000000000 : ℝ)|^4473 ≤ (15450488194959/50000000000000 : ℝ)^3449
        have hw : |(4043267011/10000000000 : ℝ)|=(4043267011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1488_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15567/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10737/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10809/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15567/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10737/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15567/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10737/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15567/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10737/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15567/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10737/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15567/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10737/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15567/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10737/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10737/100000 : ℝ) ^ (4471/1024 : ℝ) ≤ (1173979587786117/20000000000000000000 : ℝ) := by
    have hpowers : (10737/100000 : ℝ)^4471 ≤ (1173979587786117/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10737 : ℕ)^4471*20000000000000000000^1024 ≤ 1173979587786117^1024*100000^4471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10737 100000 1173979587786117 20000000000000000000 4471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10737/100000 : ℝ)) (X := (1173979587786117/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15567/100000 : ℝ) ^ (4471/1024 : ℝ) ≤ (29716407835612129/100000000000000000000 : ℝ) := by
    have hpowers : (15567/100000 : ℝ)^4471 ≤ (29716407835612129/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15567 : ℕ)^4471*100000000000000000000^1024 ≤ 29716407835612129^1024*100000^4471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15567 100000 29716407835612129 100000000000000000000 4471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15567/100000 : ℝ)) (X := (29716407835612129/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001173979587786117/10000000000000000000 : ℝ) ≤ (10000268866181629/10000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (10001173979587786117/10000000000000000000 : ℝ)^1024 ≤ (10000268866181629/10000000000000000 : ℝ)^4471 := by
      have hnat : (10001173979587786117 : ℕ)^1024*10000000000000000^4471 ≤ 10000268866181629^4471*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001173979587786117 10000000000000000000 10000268866181629 10000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000268866181629/10000000000000000 : ℝ)) (X := (10001173979587786117/10000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017793152887271357/50000000000000000000 : ℝ) ≤ (10000814926846047/10000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (50017793152887271357/50000000000000000000 : ℝ)^1024 ≤ (10000814926846047/10000000000000000 : ℝ)^4471 := by
      have hnat : (50017793152887271357 : ℕ)^1024*10000000000000000^4471 ≤ 10000814926846047^4471*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017793152887271357 50000000000000000000 10000814926846047 10000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000814926846047/10000000000000000 : ℝ)) (X := (50017793152887271357/50000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029716407835612129/50000000000000000000 : ℝ) ≤ (2000272197502093/2000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (50029716407835612129/50000000000000000000 : ℝ)^1024 ≤ (2000272197502093/2000000000000000 : ℝ)^4471 := by
      have hnat : (50029716407835612129 : ℕ)^1024*2000000000000000^4471 ≤ 2000272197502093^4471*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029716407835612129 50000000000000000000 2000272197502093 2000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000272197502093/2000000000000000 : ℝ)) (X := (50029716407835612129/50000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1173979587786117/20000000000000000000 : ℝ) ≤ ((8048262086158259323/8050000000000000000 : ℝ)+2*(273030332209/241500000000000 : ℝ)*(10737/100000 : ℝ))^(4471/1024 : ℝ) := by
    rw [show (8048262086158259323/8050000000000000000 : ℝ)+2*(273030332209/241500000000000 : ℝ)*(10737/100000 : ℝ)=(10000268866181629/10000000000000000 : ℝ) by norm_num, show 1+2*(1173979587786117/20000000000000000000 : ℝ)=(10001173979587786117/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29716407835612129/100000000000000000000 : ℝ)+(1173979587786117/20000000000000000000 : ℝ) ≤ ((8048262086158259323/8050000000000000000 : ℝ)+(273030332209/241500000000000 : ℝ)*((15567/100000 : ℝ)+(10737/100000 : ℝ)))^(4471/1024 : ℝ) := by
    rw [show (8048262086158259323/8050000000000000000 : ℝ)+(273030332209/241500000000000 : ℝ)*((15567/100000 : ℝ)+(10737/100000 : ℝ))=(10000814926846047/10000000000000000 : ℝ) by norm_num, show 1+(29716407835612129/100000000000000000000 : ℝ)+(1173979587786117/20000000000000000000 : ℝ)=(50017793152887271357/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29716407835612129/100000000000000000000 : ℝ) ≤ ((8048262086158259323/8050000000000000000 : ℝ)+2*(273030332209/241500000000000 : ℝ)*(15567/100000 : ℝ))^(4471/1024 : ℝ) := by
    rw [show (8048262086158259323/8050000000000000000 : ℝ)+2*(273030332209/241500000000000 : ℝ)*(15567/100000 : ℝ)=(2000272197502093/2000000000000000 : ℝ) by norm_num, show 1+2*(29716407835612129/100000000000000000000 : ℝ)=(50029716407835612129/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8048262086158259323/8050000000000000000 : ℝ)*(X 1 0+X 2 0)+(273030332209/241500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (10737/100000 : ℝ)) (hi := (15567/100000 : ℝ)) (c := (8048262086158259323/8050000000000000000 : ℝ)) (alpha := (273030332209/241500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8048262086158259323/8050000000000000000 : ℝ)*(X 0 1+X 2 1)+(273030332209/241500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (10737/100000 : ℝ)) (hi := (15567/100000 : ℝ)) (c := (8048262086158259323/8050000000000000000 : ℝ)) (alpha := (273030332209/241500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8048262086158259323/8050000000000000000 : ℝ)*(X 0 2+X 1 2)+(273030332209/241500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (10737/100000 : ℝ)) (hi := (15567/100000 : ℝ)) (c := (8048262086158259323/8050000000000000000 : ℝ)) (alpha := (273030332209/241500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1903977791/10000000000 : ℝ)*X 0 0+(5436935867/10000000000 : ℝ)*X 0 1+(5215823727/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83641221/156250000 : ℝ)*X 1 0+(-1008645841/5000000000 : ℝ)*X 1 1+(41726579/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338259357/2500000000 : ℝ)*X 2 0+(521582333/1000000000 : ℝ)*X 2 1+(-2017291373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((214051357/500000000 : ℝ)*X 0 0+(4040710767/10000000000 : ℝ)*X 0 1+(4533637759/10000000000 : ℝ)*X 0 2+(214051357/500000000 : ℝ)*X 1 0+(4040710767/10000000000 : ℝ)*X 1 1+(4533637759/10000000000 : ℝ)*X 1 2+(214051357/500000000 : ℝ)*X 2 0+(4040710767/10000000000 : ℝ)*X 2 1+(4533637759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-952004249/5000000000 : ℝ)*X 0 0+(130424031/250000000 : ℝ)*X 0 1+(543578973/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165475399/312500000 : ℝ)*X 1 0+(-179732471/1000000000 : ℝ)*X 1 1+(2717894863/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647606381/5000000000 : ℝ)*X 2 0+(5435789729/10000000000 : ℝ)*X 2 1+(-359464943/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((856219219/2000000000 : ℝ)*X 0 0+(2265549581/5000000000 : ℝ)*X 0 1+(4043267011/10000000000 : ℝ)*X 0 2+(856219219/2000000000 : ℝ)*X 1 0+(2265549581/5000000000 : ℝ)*X 1 1+(4043267011/10000000000 : ℝ)*X 1 2+(856219219/2000000000 : ℝ)*X 2 0+(2265549581/5000000000 : ℝ)*X 2 1+(4043267011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1349413654467190531284845713/201250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (899018609/100000000000000 : ℝ)*(base19) + (188044199/100000000000000 : ℝ)*(base23) + (157157/195312500000 : ℝ)*(lower3) + (60138177/100000000000000 : ℝ)*(upper4) + (3275653182830977/100000000000000 : ℝ)*(major0) + (3275653182830977/100000000000000 : ℝ)*(major1) + (3275653182830977/100000000000000 : ℝ)*(major2) + (4522591952099159/100000000000000 : ℝ)*(sp0) + (70665413543481/1562500000000 : ℝ)*(sp1) + (2261293880113167/50000000000000 : ℝ)*(sp2) + (2028707038656599/100000000000000 : ℝ)*(sp3) + (4586297767/100000000000000 : ℝ)*(sp5) + (4003828627/100000000000000 : ℝ)*(sp6) + (357570041/5000000000000 : ℝ)*(sp7) + (2028714190057419/100000000000000 : ℝ)*(f.failure) + (4522591952099159/100000000000000 : ℝ)*(f.sum) + (21731032907033/3018750000000000000000000000 : ℝ)*base66 + (968885070351377959/345000000000000000000000000000000 : ℝ)*base67 + (2000483743808622041/345000000000000000000000000000000 : ℝ)*base70 + (2167940001818622041/345000000000000000000000000000000 : ℝ)*base72 + (5843267204483/3018750000000000000000000000 : ℝ)*base74 + (5560327689713622041/345000000000000000000000000000000 : ℝ)*base76 + (3141448848848622041/345000000000000000000000000000000 : ℝ)*base78 + (3437699344898622041/345000000000000000000000000000000 : ℝ)*base80 + (45783650082857/12075000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (25005331/5000000000000000000000 : ℝ)*base89 + (25005331/5000000000000000000000 : ℝ)*base91 + (25005331/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2194937969350333184171126313/402500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (912947401/100000000000000 : ℝ)*(base19) + (49004783/5000000000000 : ℝ)*(base23) + (22574067/20000000000000 : ℝ)*(upper3) + (8332363/25000000000000 : ℝ)*(lower4) + (28340489/25000000000000 : ℝ)*(upper5) + (3309836839328377/100000000000000 : ℝ)*(major0) + (3309836839328377/100000000000000 : ℝ)*(major1) + (3309836839328377/100000000000000 : ℝ)*(major2) + (6864431/50000000000 : ℝ)*(sp1) + (1823540877/12500000000000 : ℝ)*(sp2) + (2284894151050511/50000000000000 : ℝ)*(sp4) + (4569773660291621/100000000000000 : ℝ)*(sp5) + (4569772733678347/100000000000000 : ℝ)*(sp6) + (2049885194780327/100000000000000 : ℝ)*(sp7) + (2049885194780327/100000000000000 : ℝ)*(f.failure) + (2284894151050511/50000000000000 : ℝ)*(f.sum) + (3614354685691/6037500000000000000000000000 : ℝ)*base66 + (359926449032203759/345000000000000000000000000000000 : ℝ)*base67 + (1634354125002796241/345000000000000000000000000000000 : ℝ)*base70 + (411816264077203759/345000000000000000000000000000000 : ℝ)*base71 + (3293337496993/12075000000000000000000000000 : ℝ)*base73 + (831481091172796241/345000000000000000000000000000000 : ℝ)*base76 + (4057408381152796241/345000000000000000000000000000000 : ℝ)*base78 + (1156691468202796241/345000000000000000000000000000000 : ℝ)*base80 + (9823902492493/12075000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (9665423/5000000000000000000000 : ℝ)*base89 + (9665423/5000000000000000000000 : ℝ)*base91 + (9665423/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1488_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15567/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10737/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10809/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1488_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1488_s5_0 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-190405461/1000000000 : ℝ)*x 0 + (2718218953/5000000000 : ℝ)*x 1 + (5216270897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (190405461/1000000000 : ℝ)^4473 ≤ (232727605659/2000000000000 : ℝ)^3449 := by
    have hnat : (190405461 : ℕ)^4473*2000000000000^3449 ≤ 232727605659^3449*1000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190405461 1000000000 232727605659 2000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718218953/5000000000 : ℝ)^4473 ≤ (45365939412117/100000000000000 : ℝ)^3449 := by
    have hnat : (2718218953 : ℕ)^4473*100000000000000^3449 ≤ 45365939412117^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718218953 5000000000 45365939412117 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216270897/10000000000 : ℝ)^4473 ≤ (21498840145343/50000000000000 : ℝ)^3449 := by
    have hnat : (5216270897 : ℕ)^4473*50000000000000^3449 ≤ 21498840145343^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216270897 10000000000 21498840145343 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-190405461/1000000000 : ℝ), (2718218953/5000000000 : ℝ), (5216270897/10000000000 : ℝ)] ![(232727605659/2000000000000 : ℝ), (45365939412117/100000000000000 : ℝ), (21498840145343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-190405461/1000000000 : ℝ)|^4473 ≤ (232727605659/2000000000000 : ℝ)^3449
        have hw : |(-190405461/1000000000 : ℝ)|=(190405461/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718218953/5000000000 : ℝ)|^4473 ≤ (45365939412117/100000000000000 : ℝ)^3449
        have hw : |(2718218953/5000000000 : ℝ)|=(2718218953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216270897/10000000000 : ℝ)|^4473 ≤ (21498840145343/50000000000000 : ℝ)^3449
        have hw : |(5216270897/10000000000 : ℝ)|=(5216270897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s5_1 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676453991/5000000000 : ℝ)*x 0 + (-2016870321/10000000000 : ℝ)*x 1 + (2608135669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676453991/5000000000 : ℝ)^4473 ≤ (1389500610479/3125000000000 : ℝ)^3449 := by
    have hnat : (2676453991 : ℕ)^4473*3125000000000^3449 ≤ 1389500610479^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676453991 5000000000 1389500610479 3125000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2016870321/10000000000 : ℝ)^4473 ≤ (1567286930421/12500000000000 : ℝ)^3449 := by
    have hnat : (2016870321 : ℕ)^4473*12500000000000^3449 ≤ 1567286930421^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016870321 10000000000 1567286930421 12500000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608135669/5000000000 : ℝ)^4473 ≤ (10749421251279/25000000000000 : ℝ)^3449 := by
    have hnat : (2608135669 : ℕ)^4473*25000000000000^3449 ≤ 10749421251279^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608135669 5000000000 10749421251279 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676453991/5000000000 : ℝ), (-2016870321/10000000000 : ℝ), (2608135669/5000000000 : ℝ)] ![(1389500610479/3125000000000 : ℝ), (1567286930421/12500000000000 : ℝ), (10749421251279/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676453991/5000000000 : ℝ)|^4473 ≤ (1389500610479/3125000000000 : ℝ)^3449
        have hw : |(2676453991/5000000000 : ℝ)|=(2676453991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2016870321/10000000000 : ℝ)|^4473 ≤ (1567286930421/12500000000000 : ℝ)^3449
        have hw : |(-2016870321/10000000000 : ℝ)|=(2016870321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608135669/5000000000 : ℝ)|^4473 ≤ (10749421251279/25000000000000 : ℝ)^3449
        have hw : |(2608135669/5000000000 : ℝ)|=(2608135669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s5_2 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4181959/7812500 : ℝ)*x 0 + (1043254377/2000000000 : ℝ)*x 1 + (-1008435107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4181959/7812500 : ℝ)^4473 ≤ (44464014558339/100000000000000 : ℝ)^3449 := by
    have hnat : (4181959 : ℕ)^4473*100000000000000^3449 ≤ 44464014558339^3449*7812500^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4181959 7812500 44464014558339 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043254377/2000000000 : ℝ)^4473 ≤ (42997690852719/100000000000000 : ℝ)^3449 := by
    have hnat : (1043254377 : ℕ)^4473*100000000000000^3449 ≤ 42997690852719^3449*2000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043254377 2000000000 42997690852719 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1008435107/5000000000 : ℝ)^4473 ≤ (12538294580687/100000000000000 : ℝ)^3449 := by
    have hnat : (1008435107 : ℕ)^4473*100000000000000^3449 ≤ 12538294580687^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008435107 5000000000 12538294580687 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4181959/7812500 : ℝ), (1043254377/2000000000 : ℝ), (-1008435107/5000000000 : ℝ)] ![(44464014558339/100000000000000 : ℝ), (42997690852719/100000000000000 : ℝ), (12538294580687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4181959/7812500 : ℝ)|^4473 ≤ (44464014558339/100000000000000 : ℝ)^3449
        have hw : |(4181959/7812500 : ℝ)|=(4181959/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043254377/2000000000 : ℝ)|^4473 ≤ (42997690852719/100000000000000 : ℝ)^3449
        have hw : |(1043254377/2000000000 : ℝ)|=(1043254377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1008435107/5000000000 : ℝ)|^4473 ≤ (12538294580687/100000000000000 : ℝ)^3449
        have hw : |(-1008435107/5000000000 : ℝ)|=(1008435107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s5_3 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070268769/2500000000 : ℝ)*x 0 + (80835239/200000000 : ℝ)*x 1 + (4532574689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070268769/2500000000 : ℝ)^4473 ≤ (1663917360647/5000000000000 : ℝ)^3449 := by
    have hnat : (1070268769 : ℕ)^4473*5000000000000^3449 ≤ 1663917360647^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070268769 2500000000 1663917360647 5000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80835239/200000000 : ℝ)^4473 ≤ (30886059592743/100000000000000 : ℝ)^3449 := by
    have hnat : (80835239 : ℕ)^4473*100000000000000^3449 ≤ 30886059592743^3449*200000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80835239 200000000 30886059592743 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4532574689/10000000000 : ℝ)^4473 ≤ (8958898295693/25000000000000 : ℝ)^3449 := by
    have hnat : (4532574689 : ℕ)^4473*25000000000000^3449 ≤ 8958898295693^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532574689 10000000000 8958898295693 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070268769/2500000000 : ℝ), (80835239/200000000 : ℝ), (4532574689/10000000000 : ℝ)] ![(1663917360647/5000000000000 : ℝ), (30886059592743/100000000000000 : ℝ), (8958898295693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070268769/2500000000 : ℝ)|^4473 ≤ (1663917360647/5000000000000 : ℝ)^3449
        have hw : |(1070268769/2500000000 : ℝ)|=(1070268769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80835239/200000000 : ℝ)|^4473 ≤ (30886059592743/100000000000000 : ℝ)^3449
        have hw : |(80835239/200000000 : ℝ)|=(80835239/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4532574689/10000000000 : ℝ)|^4473 ≤ (8958898295693/25000000000000 : ℝ)^3449
        have hw : |(4532574689/10000000000 : ℝ)|=(4532574689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s5_4 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-4760211/25000000 : ℝ)*x 0 + (65217503/125000000 : ℝ)*x 1 + (1358825113/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4760211/25000000 : ℝ)^4473 ≤ (5818308196839/50000000000000 : ℝ)^3449 := by
    have hnat : (4760211 : ℕ)^4473*50000000000000^3449 ≤ 5818308196839^3449*25000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4760211 25000000 5818308196839 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65217503/125000000 : ℝ)^4473 ≤ (43009753713609/100000000000000 : ℝ)^3449 := by
    have hnat : (65217503 : ℕ)^4473*100000000000000^3449 ≤ 43009753713609^3449*125000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65217503 125000000 43009753713609 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358825113/2500000000 : ℝ)^4473 ≤ (11338407470093/25000000000000 : ℝ)^3449 := by
    have hnat : (1358825113 : ℕ)^4473*25000000000000^3449 ≤ 11338407470093^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358825113 2500000000 11338407470093 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4760211/25000000 : ℝ), (65217503/125000000 : ℝ), (1358825113/2500000000 : ℝ)] ![(5818308196839/50000000000000 : ℝ), (43009753713609/100000000000000 : ℝ), (11338407470093/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4760211/25000000 : ℝ)|^4473 ≤ (5818308196839/50000000000000 : ℝ)^3449
        have hw : |(-4760211/25000000 : ℝ)|=(4760211/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65217503/125000000 : ℝ)|^4473 ≤ (43009753713609/100000000000000 : ℝ)^3449
        have hw : |(65217503/125000000 : ℝ)|=(65217503/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358825113/2500000000 : ℝ)|^4473 ≤ (11338407470093/25000000000000 : ℝ)^3449
        have hw : |(1358825113/2500000000 : ℝ)|=(1358825113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s5_5 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105906617/200000000 : ℝ)*x 0 + (-1797841533/10000000000 : ℝ)*x 1 + (1358825113/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105906617/200000000 : ℝ)^4473 ≤ (43844751161043/100000000000000 : ℝ)^3449 := by
    have hnat : (105906617 : ℕ)^4473*100000000000000^3449 ≤ 43844751161043^3449*200000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105906617 200000000 43844751161043 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1797841533/10000000000 : ℝ)^4473 ≤ (5400809476583/50000000000000 : ℝ)^3449 := by
    have hnat : (1797841533 : ℕ)^4473*50000000000000^3449 ≤ 5400809476583^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797841533 10000000000 5400809476583 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358825113/2500000000 : ℝ)^4473 ≤ (11338407470093/25000000000000 : ℝ)^3449 := by
    have hnat : (1358825113 : ℕ)^4473*25000000000000^3449 ≤ 11338407470093^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358825113 2500000000 11338407470093 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105906617/200000000 : ℝ), (-1797841533/10000000000 : ℝ), (1358825113/2500000000 : ℝ)] ![(43844751161043/100000000000000 : ℝ), (5400809476583/50000000000000 : ℝ), (11338407470093/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105906617/200000000 : ℝ)|^4473 ≤ (43844751161043/100000000000000 : ℝ)^3449
        have hw : |(105906617/200000000 : ℝ)|=(105906617/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1797841533/10000000000 : ℝ)|^4473 ≤ (5400809476583/50000000000000 : ℝ)^3449
        have hw : |(-1797841533/10000000000 : ℝ)|=(1797841533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358825113/2500000000 : ℝ)|^4473 ≤ (11338407470093/25000000000000 : ℝ)^3449
        have hw : |(1358825113/2500000000 : ℝ)|=(1358825113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s5_6 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105906617/200000000 : ℝ)*x 0 + (1358825113/2500000000 : ℝ)*x 1 + (-1797841533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105906617/200000000 : ℝ)^4473 ≤ (43844751161043/100000000000000 : ℝ)^3449 := by
    have hnat : (105906617 : ℕ)^4473*100000000000000^3449 ≤ 43844751161043^3449*200000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105906617 200000000 43844751161043 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358825113/2500000000 : ℝ)^4473 ≤ (11338407470093/25000000000000 : ℝ)^3449 := by
    have hnat : (1358825113 : ℕ)^4473*25000000000000^3449 ≤ 11338407470093^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358825113 2500000000 11338407470093 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1797841533/10000000000 : ℝ)^4473 ≤ (5400809476583/50000000000000 : ℝ)^3449 := by
    have hnat : (1797841533 : ℕ)^4473*50000000000000^3449 ≤ 5400809476583^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797841533 10000000000 5400809476583 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105906617/200000000 : ℝ), (1358825113/2500000000 : ℝ), (-1797841533/10000000000 : ℝ)] ![(43844751161043/100000000000000 : ℝ), (11338407470093/25000000000000 : ℝ), (5400809476583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105906617/200000000 : ℝ)|^4473 ≤ (43844751161043/100000000000000 : ℝ)^3449
        have hw : |(105906617/200000000 : ℝ)|=(105906617/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358825113/2500000000 : ℝ)|^4473 ≤ (11338407470093/25000000000000 : ℝ)^3449
        have hw : |(1358825113/2500000000 : ℝ)|=(1358825113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1797841533/10000000000 : ℝ)|^4473 ≤ (5400809476583/50000000000000 : ℝ)^3449
        have hw : |(-1797841533/10000000000 : ℝ)|=(1797841533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s5_7 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4281142249/10000000000 : ℝ)*x 0 + (4530058847/10000000000 : ℝ)*x 1 + (4044296091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4281142249/10000000000 : ℝ)^4473 ≤ (33279024402673/100000000000000 : ℝ)^3449 := by
    have hnat : (4281142249 : ℕ)^4473*100000000000000^3449 ≤ 33279024402673^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4281142249 10000000000 33279024402673 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4530058847/10000000000 : ℝ)^4473 ≤ (17904899466399/50000000000000 : ℝ)^3449 := by
    have hnat : (4530058847 : ℕ)^4473*50000000000000^3449 ≤ 17904899466399^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530058847 10000000000 17904899466399 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4044296091/10000000000 : ℝ)^4473 ≤ (15455588322459/50000000000000 : ℝ)^3449 := by
    have hnat : (4044296091 : ℕ)^4473*50000000000000^3449 ≤ 15455588322459^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4044296091 10000000000 15455588322459 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4281142249/10000000000 : ℝ), (4530058847/10000000000 : ℝ), (4044296091/10000000000 : ℝ)] ![(33279024402673/100000000000000 : ℝ), (17904899466399/50000000000000 : ℝ), (15455588322459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4281142249/10000000000 : ℝ)|^4473 ≤ (33279024402673/100000000000000 : ℝ)^3449
        have hw : |(4281142249/10000000000 : ℝ)|=(4281142249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4530058847/10000000000 : ℝ)|^4473 ≤ (17904899466399/50000000000000 : ℝ)^3449
        have hw : |(4530058847/10000000000 : ℝ)|=(4530058847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4044296091/10000000000 : ℝ)|^4473 ≤ (15455588322459/50000000000000 : ℝ)^3449
        have hw : |(4044296091/10000000000 : ℝ)|=(4044296091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1488_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10809/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5409/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15479/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10809/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10809/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10809/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10809/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10809/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10809/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10809/100000 : ℝ) ^ (4471/1024 : ℝ) ≤ (3021855964291741/50000000000000000000 : ℝ) := by
    have hpowers : (10809/100000 : ℝ)^4471 ≤ (3021855964291741/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10809 : ℕ)^4471*50000000000000000000^1024 ≤ 3021855964291741^1024*100000^4471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10809 100000 3021855964291741 50000000000000000000 4471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10809/100000 : ℝ)) (X := (3021855964291741/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4471/1024 : ℝ) ≤ (14535876550224573/50000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4471 ≤ (14535876550224573/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4471*50000000000000000000^1024 ≤ 14535876550224573^1024*100000^4471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 14535876550224573 50000000000000000000 4471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (14535876550224573/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003021855964291741/25000000000000000000 : ℝ) ≤ (10000276827227441/10000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (25003021855964291741/25000000000000000000 : ℝ)^1024 ≤ (10000276827227441/10000000000000000 : ℝ)^4471 := by
      have hnat : (25003021855964291741 : ℕ)^1024*10000000000000000^4471 ≤ 10000276827227441^4471*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003021855964291741 25000000000000000000 10000276827227441 10000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000276827227441/10000000000000000 : ℝ)) (X := (25003021855964291741/25000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008778866257258157/25000000000000000000 : ℝ) ≤ (1000080414604623/1000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (25008778866257258157/25000000000000000000 : ℝ)^1024 ≤ (1000080414604623/1000000000000000 : ℝ)^4471 := by
      have hnat : (25008778866257258157 : ℕ)^1024*1000000000000000^4471 ≤ 1000080414604623^4471*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008778866257258157 25000000000000000000 1000080414604623 1000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000080414604623/1000000000000000 : ℝ)) (X := (25008778866257258157/25000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014535876550224573/25000000000000000000 : ℝ) ≤ (10001331464865019/10000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (25014535876550224573/25000000000000000000 : ℝ)^1024 ≤ (10001331464865019/10000000000000000 : ℝ)^4471 := by
      have hnat : (25014535876550224573 : ℕ)^1024*10000000000000000^4471 ≤ 10001331464865019^4471*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014535876550224573 25000000000000000000 10001331464865019 10000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001331464865019/10000000000000000 : ℝ)) (X := (25014535876550224573/25000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3021855964291741/50000000000000000000 : ℝ) ≤ ((2599438665177769071/2600000000000000000 : ℝ)+2*(527318818789/468000000000000 : ℝ)*(10809/100000 : ℝ))^(4471/1024 : ℝ) := by
    rw [show (2599438665177769071/2600000000000000000 : ℝ)+2*(527318818789/468000000000000 : ℝ)*(10809/100000 : ℝ)=(10000276827227441/10000000000000000 : ℝ) by norm_num, show 1+2*(3021855964291741/50000000000000000000 : ℝ)=(25003021855964291741/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14535876550224573/50000000000000000000 : ℝ)+(3021855964291741/50000000000000000000 : ℝ) ≤ ((2599438665177769071/2600000000000000000 : ℝ)+(527318818789/468000000000000 : ℝ)*((15489/100000 : ℝ)+(10809/100000 : ℝ)))^(4471/1024 : ℝ) := by
    rw [show (2599438665177769071/2600000000000000000 : ℝ)+(527318818789/468000000000000 : ℝ)*((15489/100000 : ℝ)+(10809/100000 : ℝ))=(1000080414604623/1000000000000000 : ℝ) by norm_num, show 1+(14535876550224573/50000000000000000000 : ℝ)+(3021855964291741/50000000000000000000 : ℝ)=(25008778866257258157/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14535876550224573/50000000000000000000 : ℝ) ≤ ((2599438665177769071/2600000000000000000 : ℝ)+2*(527318818789/468000000000000 : ℝ)*(15489/100000 : ℝ))^(4471/1024 : ℝ) := by
    rw [show (2599438665177769071/2600000000000000000 : ℝ)+2*(527318818789/468000000000000 : ℝ)*(15489/100000 : ℝ)=(10001331464865019/10000000000000000 : ℝ) by norm_num, show 1+2*(14535876550224573/50000000000000000000 : ℝ)=(25014535876550224573/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2599438665177769071/2600000000000000000 : ℝ)*(X 1 0+X 2 0)+(527318818789/468000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (10809/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (2599438665177769071/2600000000000000000 : ℝ)) (alpha := (527318818789/468000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2599438665177769071/2600000000000000000 : ℝ)*(X 0 1+X 2 1)+(527318818789/468000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (10809/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (2599438665177769071/2600000000000000000 : ℝ)) (alpha := (527318818789/468000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2599438665177769071/2600000000000000000 : ℝ)*(X 0 2+X 1 2)+(527318818789/468000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (10809/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (2599438665177769071/2600000000000000000 : ℝ)) (alpha := (527318818789/468000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-190405461/1000000000 : ℝ)*X 0 0+(2718218953/5000000000 : ℝ)*X 0 1+(5216270897/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676453991/5000000000 : ℝ)*X 1 0+(-2016870321/10000000000 : ℝ)*X 1 1+(2608135669/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((4181959/7812500 : ℝ)*X 2 0+(1043254377/2000000000 : ℝ)*X 2 1+(-1008435107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1070268769/2500000000 : ℝ)*X 0 0+(80835239/200000000 : ℝ)*X 0 1+(4532574689/10000000000 : ℝ)*X 0 2+(1070268769/2500000000 : ℝ)*X 1 0+(80835239/200000000 : ℝ)*X 1 1+(4532574689/10000000000 : ℝ)*X 1 2+(1070268769/2500000000 : ℝ)*X 2 0+(80835239/200000000 : ℝ)*X 2 1+(4532574689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-4760211/25000000 : ℝ)*X 0 0+(65217503/125000000 : ℝ)*X 0 1+(1358825113/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((105906617/200000000 : ℝ)*X 1 0+(-1797841533/10000000000 : ℝ)*X 1 1+(1358825113/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((105906617/200000000 : ℝ)*X 2 0+(1358825113/2500000000 : ℝ)*X 2 1+(-1797841533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4281142249/10000000000 : ℝ)*X 0 0+(4530058847/10000000000 : ℝ)*X 0 1+(4044296091/10000000000 : ℝ)*X 0 2+(4281142249/10000000000 : ℝ)*X 1 0+(4530058847/10000000000 : ℝ)*X 1 1+(4044296091/10000000000 : ℝ)*X 1 2+(4281142249/10000000000 : ℝ)*X 2 0+(4530058847/10000000000 : ℝ)*X 2 1+(4044296091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4121998816537953533822424229/390000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77175581/3125000000000 : ℝ)*(base19) + (1912998367/100000000000000 : ℝ)*(base23) + (148333039/50000000000000 : ℝ)*(upper3) + (17621677/20000000000000 : ℝ)*(upper4) + (54099827/25000000000000 : ℝ)*(upper5) + (3289788465441937/100000000000000 : ℝ)*(major0) + (3289788465441937/100000000000000 : ℝ)*(major1) + (3289788465441937/100000000000000 : ℝ)*(major2) + (283878651787389/6250000000000 : ℝ)*(sp0) + (4542105497472619/100000000000000 : ℝ)*(sp1) + (1135526513523211/25000000000000 : ℝ)*(sp2) + (2037452518646541/100000000000000 : ℝ)*(sp3) + (49538492987/100000000000000 : ℝ)*(sp4) + (125725301/781250000000 : ℝ)*(sp7) + (2037468611485069/100000000000000 : ℝ)*(f.failure) + (4542107967091211/100000000000000 : ℝ)*(f.sum) + (120874936291093/23400000000000000000000000000 : ℝ)*base65 + (8528583785180975257/2340000000000000000000000000000000 : ℝ)*base68 + (3030388415240975257/2340000000000000000000000000000000 : ℝ)*base70 + (10256576572220975257/2340000000000000000000000000000000 : ℝ)*base72 + (21096732173507/23400000000000000000000000000 : ℝ)*base74 + (7552384993040975257/2340000000000000000000000000000000 : ℝ)*base76 + (6405502903700975257/2340000000000000000000000000000000 : ℝ)*base78 + (13973518356620975257/2340000000000000000000000000000000 : ℝ)*base80 + (24441663518893/23400000000000000000000000000 : ℝ)*base81 + (290181/5000000000000000000000 : ℝ)*base89 + (290181/5000000000000000000000 : ℝ)*base91 + (290181/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (188505917571720628913255687/19500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (159532591/10000000000000 : ℝ)*(base19) + (216441943/12500000000000 : ℝ)*(base23) + (24954367/12500000000000 : ℝ)*(upper3) + (61554823/100000000000000 : ℝ)*(lower4) + (9955953/5000000000000 : ℝ)*(upper5) + (332393686900567/10000000000000 : ℝ)*(major0) + (332393686900567/10000000000000 : ℝ)*(major1) + (332393686900567/10000000000000 : ℝ)*(major2) + (24133020543/100000000000000 : ℝ)*(sp1) + (25969493463/100000000000000 : ℝ)*(sp2) + (4589255632812443/100000000000000 : ℝ)*(sp4) + (4589229904465989/100000000000000 : ℝ)*(sp5) + (917845586356687/20000000000000 : ℝ)*(sp6) + (41172355659331/2000000000000 : ℝ)*(sp7) + (41172355659331/2000000000000 : ℝ)*(f.failure) + (4589255632812443/100000000000000 : ℝ)*(f.sum) + (4971866941637/2340000000000000000000000000 : ℝ)*base66 + (301819455127180687/234000000000000000000000000000000 : ℝ)*base68 + (1378481633728819313/234000000000000000000000000000000 : ℝ)*base69 + (1304461457368819313/234000000000000000000000000000000 : ℝ)*base71 + (5781180886037/2340000000000000000000000000 : ℝ)*base74 + (4378993591444819313/234000000000000000000000000000000 : ℝ)*base75 + (1576866325012819313/234000000000000000000000000000000 : ℝ)*base77 + (592852856002819313/234000000000000000000000000000000 : ℝ)*base79 + (1497396828943/2340000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (534581/100000000000000000000 : ℝ)*base90 + (534581/100000000000000000000 : ℝ)*base92 + (534581/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1488_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10809/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5409/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1488_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1488_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3219/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5409/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1488_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1488_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1488_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3219/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5409/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1488_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
