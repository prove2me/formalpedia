-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1387_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:24:57.13023+00:00
-- url     : https://prove2.me/submissions/0bdf753a-1045-4c8e-a0a2-3c17d95a3158

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
theorem support_rectangle_w1387_s3_0 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1002185093/5000000000 : ℝ)*x 0 + (5421762403/10000000000 : ℝ)*x 1 + (2617700877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1002185093/5000000000 : ℝ)^4347 ≤ (3053646475347/25000000000000 : ℝ)^3323 := by
    have hnat : (1002185093 : ℕ)^4347*25000000000000^3323 ≤ 3053646475347^3323*5000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002185093 5000000000 3053646475347 25000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421762403/10000000000 : ℝ)^4347 ≤ (44896704789047/100000000000000 : ℝ)^3323 := by
    have hnat : (5421762403 : ℕ)^4347*100000000000000^3323 ≤ 44896704789047^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421762403 10000000000 44896704789047 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2617700877/5000000000 : ℝ)^4347 ≤ (42888709299173/100000000000000 : ℝ)^3323 := by
    have hnat : (2617700877 : ℕ)^4347*100000000000000^3323 ≤ 42888709299173^3323*5000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617700877 5000000000 42888709299173 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1002185093/5000000000 : ℝ), (5421762403/10000000000 : ℝ), (2617700877/5000000000 : ℝ)] ![(3053646475347/25000000000000 : ℝ), (44896704789047/100000000000000 : ℝ), (42888709299173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1002185093/5000000000 : ℝ)|^4347 ≤ (3053646475347/25000000000000 : ℝ)^3323
        have hw : |(-1002185093/5000000000 : ℝ)|=(1002185093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421762403/10000000000 : ℝ)|^4347 ≤ (44896704789047/100000000000000 : ℝ)^3323
        have hw : |(5421762403/10000000000 : ℝ)|=(5421762403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2617700877/5000000000 : ℝ)|^4347 ≤ (42888709299173/100000000000000 : ℝ)^3323
        have hw : |(2617700877/5000000000 : ℝ)|=(2617700877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s3_1 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668887019/1250000000 : ℝ)*x 0 + (-2099513317/10000000000 : ℝ)*x 1 + (104708039/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668887019/1250000000 : ℝ)^4347 ≤ (4413274647979/10000000000000 : ℝ)^3323 := by
    have hnat : (668887019 : ℕ)^4347*10000000000000^3323 ≤ 4413274647979^3323*1250000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668887019 1250000000 4413274647979 10000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2099513317/10000000000 : ℝ)^4347 ≤ (12978542107953/100000000000000 : ℝ)^3323 := by
    have hnat : (2099513317 : ℕ)^4347*100000000000000^3323 ≤ 12978542107953^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099513317 10000000000 12978542107953 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104708039/200000000 : ℝ)^4347 ≤ (42888711399603/100000000000000 : ℝ)^3323 := by
    have hnat : (104708039 : ℕ)^4347*100000000000000^3323 ≤ 42888711399603^3323*200000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104708039 200000000 42888711399603 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668887019/1250000000 : ℝ), (-2099513317/10000000000 : ℝ), (104708039/200000000 : ℝ)] ![(4413274647979/10000000000000 : ℝ), (12978542107953/100000000000000 : ℝ), (42888711399603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668887019/1250000000 : ℝ)|^4347 ≤ (4413274647979/10000000000000 : ℝ)^3323
        have hw : |(668887019/1250000000 : ℝ)|=(668887019/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2099513317/10000000000 : ℝ)|^4347 ≤ (12978542107953/100000000000000 : ℝ)^3323
        have hw : |(-2099513317/10000000000 : ℝ)|=(2099513317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104708039/200000000 : ℝ)|^4347 ≤ (42888711399603/100000000000000 : ℝ)^3323
        have hw : |(104708039/200000000 : ℝ)|=(104708039/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s3_2 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351096161/10000000000 : ℝ)*x 0 + (2617700983/5000000000 : ℝ)*x 1 + (-2099513283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351096161/10000000000 : ℝ)^4347 ≤ (4413274657689/10000000000000 : ℝ)^3323 := by
    have hnat : (5351096161 : ℕ)^4347*10000000000000^3323 ≤ 4413274657689^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351096161 10000000000 4413274657689 10000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617700983/5000000000 : ℝ)^4347 ≤ (42888711571067/100000000000000 : ℝ)^3323 := by
    have hnat : (2617700983 : ℕ)^4347*100000000000000^3323 ≤ 42888711571067^3323*5000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617700983 5000000000 42888711571067 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2099513283/10000000000 : ℝ)^4347 ≤ (811158864563/6250000000000 : ℝ)^3323 := by
    have hnat : (2099513283 : ℕ)^4347*6250000000000^3323 ≤ 811158864563^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099513283 10000000000 811158864563 6250000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351096161/10000000000 : ℝ), (2617700983/5000000000 : ℝ), (-2099513283/10000000000 : ℝ)] ![(4413274657689/10000000000000 : ℝ), (42888711571067/100000000000000 : ℝ), (811158864563/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351096161/10000000000 : ℝ)|^4347 ≤ (4413274657689/10000000000000 : ℝ)^3323
        have hw : |(5351096161/10000000000 : ℝ)|=(5351096161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2617700983/5000000000 : ℝ)|^4347 ≤ (42888711571067/100000000000000 : ℝ)^3323
        have hw : |(2617700983/5000000000 : ℝ)|=(2617700983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2099513283/10000000000 : ℝ)|^4347 ≤ (811158864563/6250000000000 : ℝ)^3323
        have hw : |(-2099513283/10000000000 : ℝ)|=(2099513283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s3_3 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2157083237/5000000000 : ℝ)*x 0 + (4119865789/10000000000 : ℝ)*x 1 + (4516829033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157083237/5000000000 : ℝ)^4347 ≤ (33295723081867/100000000000000 : ℝ)^3323 := by
    have hnat : (2157083237 : ℕ)^4347*100000000000000^3323 ≤ 33295723081867^3323*5000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157083237 5000000000 33295723081867 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4119865789/10000000000 : ℝ)^4347 ≤ (7836953333937/25000000000000 : ℝ)^3323 := by
    have hnat : (4119865789 : ℕ)^4347*25000000000000^3323 ≤ 7836953333937^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4119865789 10000000000 7836953333937 25000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4516829033/10000000000 : ℝ)^4347 ≤ (883911589091/2500000000000 : ℝ)^3323 := by
    have hnat : (4516829033 : ℕ)^4347*2500000000000^3323 ≤ 883911589091^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516829033 10000000000 883911589091 2500000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157083237/5000000000 : ℝ), (4119865789/10000000000 : ℝ), (4516829033/10000000000 : ℝ)] ![(33295723081867/100000000000000 : ℝ), (7836953333937/25000000000000 : ℝ), (883911589091/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157083237/5000000000 : ℝ)|^4347 ≤ (33295723081867/100000000000000 : ℝ)^3323
        have hw : |(2157083237/5000000000 : ℝ)|=(2157083237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4119865789/10000000000 : ℝ)|^4347 ≤ (7836953333937/25000000000000 : ℝ)^3323
        have hw : |(4119865789/10000000000 : ℝ)|=(4119865789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4516829033/10000000000 : ℝ)|^4347 ≤ (883911589091/2500000000000 : ℝ)^3323
        have hw : |(4516829033/10000000000 : ℝ)|=(4516829033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s3_4 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2004387539/10000000000 : ℝ)*x 0 + (209446403/400000000 : ℝ)*x 1 + (5420999407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2004387539/10000000000 : ℝ)^4347 ≤ (6107362118701/50000000000000 : ℝ)^3323 := by
    have hnat : (2004387539 : ℕ)^4347*50000000000000^3323 ≤ 6107362118701^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004387539 10000000000 6107362118701 50000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209446403/400000000 : ℝ)^4347 ≤ (42896836014299/100000000000000 : ℝ)^3323 := by
    have hnat : (209446403 : ℕ)^4347*100000000000000^3323 ≤ 42896836014299^3323*400000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209446403 400000000 42896836014299 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420999407/10000000000 : ℝ)^4347 ≤ (44888439726811/100000000000000 : ℝ)^3323 := by
    have hnat : (5420999407 : ℕ)^4347*100000000000000^3323 ≤ 44888439726811^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420999407 10000000000 44888439726811 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2004387539/10000000000 : ℝ), (209446403/400000000 : ℝ), (5420999407/10000000000 : ℝ)] ![(6107362118701/50000000000000 : ℝ), (42896836014299/100000000000000 : ℝ), (44888439726811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2004387539/10000000000 : ℝ)|^4347 ≤ (6107362118701/50000000000000 : ℝ)^3323
        have hw : |(-2004387539/10000000000 : ℝ)|=(2004387539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209446403/400000000 : ℝ)|^4347 ≤ (42896836014299/100000000000000 : ℝ)^3323
        have hw : |(209446403/400000000 : ℝ)|=(209446403/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420999407/10000000000 : ℝ)|^4347 ≤ (44888439726811/100000000000000 : ℝ)^3323
        have hw : |(5420999407/10000000000 : ℝ)|=(5420999407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s3_5 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060570851/2000000000 : ℝ)*x 0 + (-382783161/2000000000 : ℝ)*x 1 + (271049989/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060570851/2000000000 : ℝ)^4347 ≤ (5451624195393/12500000000000 : ℝ)^3323 := by
    have hnat : (1060570851 : ℕ)^4347*12500000000000^3323 ≤ 5451624195393^3323*2000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060570851 2000000000 5451624195393 12500000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (382783161/2000000000 : ℝ)^4347 ≤ (2299712531501/20000000000000 : ℝ)^3323 := by
    have hnat : (382783161 : ℕ)^4347*20000000000000^3323 ≤ 2299712531501^3323*2000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382783161 2000000000 2299712531501 20000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271049989/500000000 : ℝ)^4347 ≤ (44888443767201/100000000000000 : ℝ)^3323 := by
    have hnat : (271049989 : ℕ)^4347*100000000000000^3323 ≤ 44888443767201^3323*500000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271049989 500000000 44888443767201 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060570851/2000000000 : ℝ), (-382783161/2000000000 : ℝ), (271049989/500000000 : ℝ)] ![(5451624195393/12500000000000 : ℝ), (2299712531501/20000000000000 : ℝ), (44888443767201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060570851/2000000000 : ℝ)|^4347 ≤ (5451624195393/12500000000000 : ℝ)^3323
        have hw : |(1060570851/2000000000 : ℝ)|=(1060570851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-382783161/2000000000 : ℝ)|^4347 ≤ (2299712531501/20000000000000 : ℝ)^3323
        have hw : |(-382783161/2000000000 : ℝ)|=(382783161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271049989/500000000 : ℝ)|^4347 ≤ (44888443767201/100000000000000 : ℝ)^3323
        have hw : |(271049989/500000000 : ℝ)|=(271049989/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s3_6 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132571373/250000000 : ℝ)*x 0 + (677624929/1250000000 : ℝ)*x 1 + (-956957687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132571373/250000000 : ℝ)^4347 ≤ (21806500358887/50000000000000 : ℝ)^3323 := by
    have hnat : (132571373 : ℕ)^4347*50000000000000^3323 ≤ 21806500358887^3323*250000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132571373 250000000 21806500358887 50000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677624929/1250000000 : ℝ)^4347 ≤ (8977687999523/20000000000000 : ℝ)^3323 := by
    have hnat : (677624929 : ℕ)^4347*20000000000000^3323 ≤ 8977687999523^3323*1250000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677624929 1250000000 8977687999523 20000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (956957687/5000000000 : ℝ)^4347 ≤ (11498559270177/100000000000000 : ℝ)^3323 := by
    have hnat : (956957687 : ℕ)^4347*100000000000000^3323 ≤ 11498559270177^3323*5000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956957687 5000000000 11498559270177 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132571373/250000000 : ℝ), (677624929/1250000000 : ℝ), (-956957687/5000000000 : ℝ)] ![(21806500358887/50000000000000 : ℝ), (8977687999523/20000000000000 : ℝ), (11498559270177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132571373/250000000 : ℝ)|^4347 ≤ (21806500358887/50000000000000 : ℝ)^3323
        have hw : |(132571373/250000000 : ℝ)|=(132571373/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677624929/1250000000 : ℝ)|^4347 ≤ (8977687999523/20000000000000 : ℝ)^3323
        have hw : |(677624929/1250000000 : ℝ)|=(677624929/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-956957687/5000000000 : ℝ)|^4347 ≤ (11498559270177/100000000000000 : ℝ)^3323
        have hw : |(-956957687/5000000000 : ℝ)|=(956957687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s3_7 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (172568127/400000000 : ℝ)*x 0 + (4515214469/10000000000 : ℝ)*x 1 + (4121489361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172568127/400000000 : ℝ)^4347 ≤ (4162011702117/12500000000000 : ℝ)^3323 := by
    have hnat : (172568127 : ℕ)^4347*12500000000000^3323 ≤ 4162011702117^3323*400000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172568127 400000000 4162011702117 12500000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4515214469/10000000000 : ℝ)^4347 ≤ (4417491443493/12500000000000 : ℝ)^3323 := by
    have hnat : (4515214469 : ℕ)^4347*12500000000000^3323 ≤ 4417491443493^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515214469 10000000000 4417491443493 12500000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4121489361/10000000000 : ℝ)^4347 ≤ (7840993706479/25000000000000 : ℝ)^3323 := by
    have hnat : (4121489361 : ℕ)^4347*25000000000000^3323 ≤ 7840993706479^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4121489361 10000000000 7840993706479 25000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172568127/400000000 : ℝ), (4515214469/10000000000 : ℝ), (4121489361/10000000000 : ℝ)] ![(4162011702117/12500000000000 : ℝ), (4417491443493/12500000000000 : ℝ), (7840993706479/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172568127/400000000 : ℝ)|^4347 ≤ (4162011702117/12500000000000 : ℝ)^3323
        have hw : |(172568127/400000000 : ℝ)|=(172568127/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4515214469/10000000000 : ℝ)|^4347 ≤ (4417491443493/12500000000000 : ℝ)^3323
        have hw : |(4515214469/10000000000 : ℝ)|=(4515214469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4121489361/10000000000 : ℝ)|^4347 ≤ (7840993706479/25000000000000 : ℝ)^3323
        have hw : |(4121489361/10000000000 : ℝ)|=(4121489361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1387_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156504483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15937/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2533/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11027/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3743/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15937/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2533/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15937/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2533/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15937/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2533/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15937/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2533/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15937/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2533/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15937/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2533/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2533/25000 : ℝ) ^ (2173/512 : ℝ) ≤ (3013009693454853/50000000000000000000 : ℝ) := by
    have hpowers : (2533/25000 : ℝ)^2173 ≤ (3013009693454853/50000000000000000000 : ℝ)^512 := by
      have hnat : (2533 : ℕ)^2173*50000000000000000000^512 ≤ 3013009693454853^512*25000^2173 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2533 25000 3013009693454853 50000000000000000000 2173 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2533/25000 : ℝ)) (X := (3013009693454853/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2173 512 (by norm_num) hpowers
    exact h
  have hpowhi : (15937/100000 : ℝ) ^ (2173/512 : ℝ) ≤ (41200390536202601/100000000000000000000 : ℝ) := by
    have hpowers : (15937/100000 : ℝ)^2173 ≤ (41200390536202601/100000000000000000000 : ℝ)^512 := by
      have hnat : (15937 : ℕ)^2173*100000000000000000000^512 ≤ 41200390536202601^512*100000^2173 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15937 100000 41200390536202601 100000000000000000000 2173 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15937/100000 : ℝ)) (X := (41200390536202601/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2173 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003013009693454853/25000000000000000000 : ℝ) ≤ (2500070988951239/2500000000000000 : ℝ) ^ (2173/512 : ℝ) := by
    have hpowers : (25003013009693454853/25000000000000000000 : ℝ)^512 ≤ (2500070988951239/2500000000000000 : ℝ)^2173 := by
      have hnat : (25003013009693454853 : ℕ)^512*2500000000000000^2173 ≤ 2500070988951239^2173*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003013009693454853 25000000000000000000 2500070988951239 2500000000000000 512 2173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500070988951239/2500000000000000 : ℝ)) (X := (25003013009693454853/25000000000000000000 : ℝ)) (by norm_num) 2173 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047226409923112307/100000000000000000000 : ℝ) ≤ (2500278135742531/2500000000000000 : ℝ) ^ (2173/512 : ℝ) := by
    have hpowers : (100047226409923112307/100000000000000000000 : ℝ)^512 ≤ (2500278135742531/2500000000000000 : ℝ)^2173 := by
      have hnat : (100047226409923112307 : ℕ)^512*2500000000000000^2173 ≤ 2500278135742531^2173*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047226409923112307 100000000000000000000 2500278135742531 2500000000000000 512 2173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500278135742531/2500000000000000 : ℝ)) (X := (100047226409923112307/100000000000000000000 : ℝ)) (by norm_num) 2173 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50041200390536202601/50000000000000000000 : ℝ) ≤ (2500485282533823/2500000000000000 : ℝ) ^ (2173/512 : ℝ) := by
    have hpowers : (50041200390536202601/50000000000000000000 : ℝ)^512 ≤ (2500485282533823/2500000000000000 : ℝ)^2173 := by
      have hnat : (50041200390536202601 : ℕ)^512*2500000000000000^2173 ≤ 2500485282533823^2173*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50041200390536202601 50000000000000000000 2500485282533823 2500000000000000 512 2173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500485282533823/2500000000000000 : ℝ)) (X := (50041200390536202601/50000000000000000000 : ℝ)) (by norm_num) 2173 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3013009693454853/50000000000000000000 : ℝ) ≤ ((14508714468283201307/14512500000000000000 : ℝ)+2*(51786697823/36281250000000 : ℝ)*(2533/25000 : ℝ))^(2173/512 : ℝ) := by
    rw [show (14508714468283201307/14512500000000000000 : ℝ)+2*(51786697823/36281250000000 : ℝ)*(2533/25000 : ℝ)=(2500070988951239/2500000000000000 : ℝ) by norm_num, show 1+2*(3013009693454853/50000000000000000000 : ℝ)=(25003013009693454853/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(41200390536202601/100000000000000000000 : ℝ)+(3013009693454853/50000000000000000000 : ℝ) ≤ ((14508714468283201307/14512500000000000000 : ℝ)+(51786697823/36281250000000 : ℝ)*((15937/100000 : ℝ)+(2533/25000 : ℝ)))^(2173/512 : ℝ) := by
    rw [show (14508714468283201307/14512500000000000000 : ℝ)+(51786697823/36281250000000 : ℝ)*((15937/100000 : ℝ)+(2533/25000 : ℝ))=(2500278135742531/2500000000000000 : ℝ) by norm_num, show 1+(41200390536202601/100000000000000000000 : ℝ)+(3013009693454853/50000000000000000000 : ℝ)=(100047226409923112307/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(41200390536202601/100000000000000000000 : ℝ) ≤ ((14508714468283201307/14512500000000000000 : ℝ)+2*(51786697823/36281250000000 : ℝ)*(15937/100000 : ℝ))^(2173/512 : ℝ) := by
    rw [show (14508714468283201307/14512500000000000000 : ℝ)+2*(51786697823/36281250000000 : ℝ)*(15937/100000 : ℝ)=(2500485282533823/2500000000000000 : ℝ) by norm_num, show 1+2*(41200390536202601/100000000000000000000 : ℝ)=(50041200390536202601/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14508714468283201307/14512500000000000000 : ℝ)*(X 1 0+X 2 0)+(51786697823/36281250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2173/512 : ℝ)) (lo := (2533/25000 : ℝ)) (hi := (15937/100000 : ℝ)) (c := (14508714468283201307/14512500000000000000 : ℝ)) (alpha := (51786697823/36281250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14508714468283201307/14512500000000000000 : ℝ)*(X 0 1+X 2 1)+(51786697823/36281250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2173/512 : ℝ)) (lo := (2533/25000 : ℝ)) (hi := (15937/100000 : ℝ)) (c := (14508714468283201307/14512500000000000000 : ℝ)) (alpha := (51786697823/36281250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14508714468283201307/14512500000000000000 : ℝ)*(X 0 2+X 1 2)+(51786697823/36281250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2173/512 : ℝ)) (lo := (2533/25000 : ℝ)) (hi := (15937/100000 : ℝ)) (c := (14508714468283201307/14512500000000000000 : ℝ)) (alpha := (51786697823/36281250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1002185093/5000000000 : ℝ)*X 0 0+(5421762403/10000000000 : ℝ)*X 0 1+(2617700877/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668887019/1250000000 : ℝ)*X 1 0+(-2099513317/10000000000 : ℝ)*X 1 1+(104708039/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351096161/10000000000 : ℝ)*X 2 0+(2617700983/5000000000 : ℝ)*X 2 1+(-2099513283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2157083237/5000000000 : ℝ)*X 0 0+(4119865789/10000000000 : ℝ)*X 0 1+(4516829033/10000000000 : ℝ)*X 0 2+(2157083237/5000000000 : ℝ)*X 1 0+(4119865789/10000000000 : ℝ)*X 1 1+(4516829033/10000000000 : ℝ)*X 1 2+(2157083237/5000000000 : ℝ)*X 2 0+(4119865789/10000000000 : ℝ)*X 2 1+(4516829033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2004387539/10000000000 : ℝ)*X 0 0+(209446403/400000000 : ℝ)*X 0 1+(5420999407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060570851/2000000000 : ℝ)*X 1 0+(-382783161/2000000000 : ℝ)*X 1 1+(271049989/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132571373/250000000 : ℝ)*X 2 0+(677624929/1250000000 : ℝ)*X 2 1+(-956957687/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((172568127/400000000 : ℝ)*X 0 0+(4515214469/10000000000 : ℝ)*X 0 1+(4121489361/10000000000 : ℝ)*X 0 2+(172568127/400000000 : ℝ)*X 1 0+(4515214469/10000000000 : ℝ)*X 1 1+(4121489361/10000000000 : ℝ)*X 1 2+(172568127/400000000 : ℝ)*X 2 0+(4515214469/10000000000 : ℝ)*X 2 1+(4121489361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (996077678271702404719942093/120937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (256981713/20000000000000 : ℝ)*(base19) + (254752071/25000000000000 : ℝ)*(base23) + (147115193/100000000000000 : ℝ)*(lower2) + (215941737/100000000000000 : ℝ)*(upper3) + (48470643/100000000000000 : ℝ)*(upper5) + (1971284378051199/50000000000000 : ℝ)*(major0) + (1971284378051199/50000000000000 : ℝ)*(major1) + (3942568756102399/100000000000000 : ℝ)*(major2) + (5365969119165587/100000000000000 : ℝ)*(sp0) + (1073198970358003/20000000000000 : ℝ)*(sp1) + (670749389711287/12500000000000 : ℝ)*(sp2) + (1259565667125341/50000000000000 : ℝ)*(sp3) + (27017532993/100000000000000 : ℝ)*(sp4) + (9766712157/100000000000000 : ℝ)*(sp7) + (2519141100962839/100000000000000 : ℝ)*(f.failure) + (268299806834929/5000000000000 : ℝ)*(f.sum) + (74608275755549/14512500000000000000000000000 : ℝ)*base65 + (4956973603034257907/725625000000000000000000000000000 : ℝ)*base68 + (570504932379235493/1451250000000000000000000000000000 : ℝ)*base69 + (1828193437544257907/725625000000000000000000000000000 : ℝ)*base72 + (7037204096747/1814062500000000000000000000 : ℝ)*base74 + (3303395787197014507/1451250000000000000000000000000000 : ℝ)*base76 + (225480901893714031/241875000000000000000000000000000 : ℝ)*base77 + (1120662865428785969/241875000000000000000000000000000 : ℝ)*base80 + (27499762359163/9675000000000000000000000000 : ℝ)*base81 + (119907237/10000000000000000000000 : ℝ)*base89 + (119907237/10000000000000000000000 : ℝ)*base91 + (19907237/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (671571662146273047613/161250000000000000000000000 : ℝ) := by norm_num
    linear_combination (705386277/100000000000000 : ℝ)*(base19) + (336990069/20000000000000 : ℝ)*(base23) + (138422499/50000000000000 : ℝ)*(upper3) + (54023483/100000000000000 : ℝ)*(lower4) + (113264953/100000000000000 : ℝ)*(upper5) + (794995076573189/20000000000000 : ℝ)*(major0) + (794995076573189/20000000000000 : ℝ)*(major1) + (794995076573189/20000000000000 : ℝ)*(major2) + (6679718061/50000000000000 : ℝ)*(sp1) + (8815164011/25000000000000 : ℝ)*(sp2) + (1352525752333893/25000000000000 : ℝ)*(sp4) + (5410088944513173/100000000000000 : ℝ)*(sp5) + (169064564491537/3125000000000 : ℝ)*(sp6) + (158740476098133/6250000000000 : ℝ)*(sp7) + (158740476098133/6250000000000 : ℝ)*(f.failure) + (1352525752333893/25000000000000 : ℝ)*(f.sum) + (12969627462077/1451250000000000000000000000 : ℝ)*base66 + (730795133461758023/290250000000000000000000000000000 : ℝ)*base67 + (1822122339241758023/290250000000000000000000000000000 : ℝ)*base69 + (3342715625899991977/290250000000000000000000000000000 : ℝ)*base72 + (18012296589113/5805000000000000000000000000 : ℝ)*base74 + (143509635292758023/290250000000000000000000000000000 : ℝ)*base75 + (1787332257526241977/290250000000000000000000000000000 : ℝ)*base78 + (165937492741241977/290250000000000000000000000000000 : ℝ)*base80 + (9638401868987/1451250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (6180239/625000000000000000000 : ℝ)*base89 + (6180239/625000000000000000000 : ℝ)*base91 + (6180239/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1387_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156504483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15937/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2533/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11027/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3743/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1387_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1387_s4_0 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2005511229/10000000000 : ℝ)*x 0 + (108244853/200000000 : ℝ)*x 1 + (131104273/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2005511229/10000000000 : ℝ)^4347 ≤ (12223682943611/100000000000000 : ℝ)^3323 := by
    have hnat : (2005511229 : ℕ)^4347*100000000000000^3323 ≤ 12223682943611^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005511229 10000000000 12223682943611 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108244853/200000000 : ℝ)^4347 ≤ (22396804442799/50000000000000 : ℝ)^3323 := by
    have hnat : (108244853 : ℕ)^4347*50000000000000^3323 ≤ 22396804442799^3323*200000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108244853 200000000 22396804442799 50000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131104273/250000000 : ℝ)^4347 ≤ (42982708156907/100000000000000 : ℝ)^3323 := by
    have hnat : (131104273 : ℕ)^4347*100000000000000^3323 ≤ 42982708156907^3323*250000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131104273 250000000 42982708156907 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2005511229/10000000000 : ℝ), (108244853/200000000 : ℝ), (131104273/250000000 : ℝ)] ![(12223682943611/100000000000000 : ℝ), (22396804442799/50000000000000 : ℝ), (42982708156907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2005511229/10000000000 : ℝ)|^4347 ≤ (12223682943611/100000000000000 : ℝ)^3323
        have hw : |(-2005511229/10000000000 : ℝ)|=(2005511229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108244853/200000000 : ℝ)|^4347 ≤ (22396804442799/50000000000000 : ℝ)^3323
        have hw : |(108244853/200000000 : ℝ)|=(108244853/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131104273/250000000 : ℝ)|^4347 ≤ (42982708156907/100000000000000 : ℝ)^3323
        have hw : |(131104273/250000000 : ℝ)|=(131104273/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s4_1 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348652987/10000000000 : ℝ)*x 0 + (-2091143873/10000000000 : ℝ)*x 1 + (1048834171/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348652987/10000000000 : ℝ)^4347 ≤ (1764255570051/4000000000000 : ℝ)^3323 := by
    have hnat : (5348652987 : ℕ)^4347*4000000000000^3323 ≤ 1764255570051^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348652987 10000000000 1764255570051 4000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2091143873/10000000000 : ℝ)^4347 ≤ (1613862909341/12500000000000 : ℝ)^3323 := by
    have hnat : (2091143873 : ℕ)^4347*12500000000000^3323 ≤ 1613862909341^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091143873 10000000000 1613862909341 12500000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048834171/2000000000 : ℝ)^4347 ≤ (5372838432497/12500000000000 : ℝ)^3323 := by
    have hnat : (1048834171 : ℕ)^4347*12500000000000^3323 ≤ 5372838432497^3323*2000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048834171 2000000000 5372838432497 12500000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348652987/10000000000 : ℝ), (-2091143873/10000000000 : ℝ), (1048834171/2000000000 : ℝ)] ![(1764255570051/4000000000000 : ℝ), (1613862909341/12500000000000 : ℝ), (5372838432497/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348652987/10000000000 : ℝ)|^4347 ≤ (1764255570051/4000000000000 : ℝ)^3323
        have hw : |(5348652987/10000000000 : ℝ)|=(5348652987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2091143873/10000000000 : ℝ)|^4347 ≤ (1613862909341/12500000000000 : ℝ)^3323
        have hw : |(-2091143873/10000000000 : ℝ)|=(2091143873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048834171/2000000000 : ℝ)|^4347 ≤ (5372838432497/12500000000000 : ℝ)^3323
        have hw : |(1048834171/2000000000 : ℝ)|=(1048834171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s4_2 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348652889/10000000000 : ℝ)*x 0 + (1048834197/2000000000 : ℝ)*x 1 + (-2091143831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348652889/10000000000 : ℝ)^4347 ≤ (44106388194111/100000000000000 : ℝ)^3323 := by
    have hnat : (5348652889 : ℕ)^4347*100000000000000^3323 ≤ 44106388194111^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348652889 10000000000 44106388194111 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048834197/2000000000 : ℝ)^4347 ≤ (21491354426919/50000000000000 : ℝ)^3323 := by
    have hnat : (1048834197 : ℕ)^4347*50000000000000^3323 ≤ 21491354426919^3323*2000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048834197 2000000000 21491354426919 50000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2091143831/10000000000 : ℝ)^4347 ≤ (3227725733877/25000000000000 : ℝ)^3323 := by
    have hnat : (2091143831 : ℕ)^4347*25000000000000^3323 ≤ 3227725733877^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091143831 10000000000 3227725733877 25000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348652889/10000000000 : ℝ), (1048834197/2000000000 : ℝ), (-2091143831/10000000000 : ℝ)] ![(44106388194111/100000000000000 : ℝ), (21491354426919/50000000000000 : ℝ), (3227725733877/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348652889/10000000000 : ℝ)|^4347 ≤ (44106388194111/100000000000000 : ℝ)^3323
        have hw : |(5348652889/10000000000 : ℝ)|=(5348652889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048834197/2000000000 : ℝ)|^4347 ≤ (21491354426919/50000000000000 : ℝ)^3323
        have hw : |(1048834197/2000000000 : ℝ)|=(1048834197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2091143831/10000000000 : ℝ)|^4347 ≤ (3227725733877/25000000000000 : ℝ)^3323
        have hw : |(-2091143831/10000000000 : ℝ)|=(2091143831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s4_3 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2157430551/5000000000 : ℝ)*x 0 + (4139258797/10000000000 : ℝ)*x 1 + (449726643/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157430551/5000000000 : ℝ)^4347 ≤ (6660547248897/20000000000000 : ℝ)^3323 := by
    have hnat : (2157430551 : ℕ)^4347*20000000000000^3323 ≤ 6660547248897^3323*5000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157430551 5000000000 6660547248897 20000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4139258797/10000000000 : ℝ)^4347 ≤ (7885246223837/25000000000000 : ℝ)^3323 := by
    have hnat : (4139258797 : ℕ)^4347*25000000000000^3323 ≤ 7885246223837^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139258797 10000000000 7885246223837 25000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449726643/1000000000 : ℝ)^4347 ≤ (17578139425687/50000000000000 : ℝ)^3323 := by
    have hnat : (449726643 : ℕ)^4347*50000000000000^3323 ≤ 17578139425687^3323*1000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449726643 1000000000 17578139425687 50000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157430551/5000000000 : ℝ), (4139258797/10000000000 : ℝ), (449726643/1000000000 : ℝ)] ![(6660547248897/20000000000000 : ℝ), (7885246223837/25000000000000 : ℝ), (17578139425687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157430551/5000000000 : ℝ)|^4347 ≤ (6660547248897/20000000000000 : ℝ)^3323
        have hw : |(2157430551/5000000000 : ℝ)|=(2157430551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4139258797/10000000000 : ℝ)|^4347 ≤ (7885246223837/25000000000000 : ℝ)^3323
        have hw : |(4139258797/10000000000 : ℝ)|=(4139258797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449726643/1000000000 : ℝ)|^4347 ≤ (17578139425687/50000000000000 : ℝ)^3323
        have hw : |(449726643/1000000000 : ℝ)|=(449726643/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s4_4 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1002761899/5000000000 : ℝ)*x 0 + (2622393973/5000000000 : ℝ)*x 1 + (2705811157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1002761899/5000000000 : ℝ)^4347 ≤ (12223783159693/100000000000000 : ℝ)^3323 := by
    have hnat : (1002761899 : ℕ)^4347*100000000000000^3323 ≤ 12223783159693^3323*5000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002761899 5000000000 12223783159693 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622393973/5000000000 : ℝ)^4347 ≤ (42989324036209/100000000000000 : ℝ)^3323 := by
    have hnat : (2622393973 : ℕ)^4347*100000000000000^3323 ≤ 42989324036209^3323*5000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622393973 5000000000 42989324036209 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705811157/5000000000 : ℝ)^4347 ≤ (44786892781659/100000000000000 : ℝ)^3323 := by
    have hnat : (2705811157 : ℕ)^4347*100000000000000^3323 ≤ 44786892781659^3323*5000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705811157 5000000000 44786892781659 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1002761899/5000000000 : ℝ), (2622393973/5000000000 : ℝ), (2705811157/5000000000 : ℝ)] ![(12223783159693/100000000000000 : ℝ), (42989324036209/100000000000000 : ℝ), (44786892781659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1002761899/5000000000 : ℝ)|^4347 ≤ (12223783159693/100000000000000 : ℝ)^3323
        have hw : |(-1002761899/5000000000 : ℝ)|=(1002761899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622393973/5000000000 : ℝ)|^4347 ≤ (42989324036209/100000000000000 : ℝ)^3323
        have hw : |(2622393973/5000000000 : ℝ)|=(2622393973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705811157/5000000000 : ℝ)|^4347 ≤ (44786892781659/100000000000000 : ℝ)^3323
        have hw : |(2705811157/5000000000 : ℝ)|=(2705811157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s4_5 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305145491/10000000000 : ℝ)*x 0 + (-1923692567/10000000000 : ℝ)*x 1 + (67645279/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305145491/10000000000 : ℝ)^4347 ≤ (43637646248801/100000000000000 : ℝ)^3323 := by
    have hnat : (5305145491 : ℕ)^4347*100000000000000^3323 ≤ 43637646248801^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305145491 10000000000 43637646248801 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1923692567/10000000000 : ℝ)^4347 ≤ (231509217781/2000000000000 : ℝ)^3323 := by
    have hnat : (1923692567 : ℕ)^4347*2000000000000^3323 ≤ 231509217781^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923692567 10000000000 231509217781 2000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67645279/125000000 : ℝ)^4347 ≤ (44786892846617/100000000000000 : ℝ)^3323 := by
    have hnat : (67645279 : ℕ)^4347*100000000000000^3323 ≤ 44786892846617^3323*125000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67645279 125000000 44786892846617 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305145491/10000000000 : ℝ), (-1923692567/10000000000 : ℝ), (67645279/125000000 : ℝ)] ![(43637646248801/100000000000000 : ℝ), (231509217781/2000000000000 : ℝ), (44786892846617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305145491/10000000000 : ℝ)|^4347 ≤ (43637646248801/100000000000000 : ℝ)^3323
        have hw : |(5305145491/10000000000 : ℝ)|=(5305145491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1923692567/10000000000 : ℝ)|^4347 ≤ (231509217781/2000000000000 : ℝ)^3323
        have hw : |(-1923692567/10000000000 : ℝ)|=(1923692567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67645279/125000000 : ℝ)|^4347 ≤ (44786892846617/100000000000000 : ℝ)^3323
        have hw : |(67645279/125000000 : ℝ)|=(67645279/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s4_6 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331571593/625000000 : ℝ)*x 0 + (1352905579/2500000000 : ℝ)*x 1 + (-60115393/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331571593/625000000 : ℝ)^4347 ≤ (43637646216521/100000000000000 : ℝ)^3323 := by
    have hnat : (331571593 : ℕ)^4347*100000000000000^3323 ≤ 43637646216521^3323*625000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331571593 625000000 43637646216521 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352905579/2500000000 : ℝ)^4347 ≤ (2799180800207/6250000000000 : ℝ)^3323 := by
    have hnat : (1352905579 : ℕ)^4347*6250000000000^3323 ≤ 2799180800207^3323*2500000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352905579 2500000000 2799180800207 6250000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60115393/312500000 : ℝ)^4347 ≤ (5787730479947/50000000000000 : ℝ)^3323 := by
    have hnat : (60115393 : ℕ)^4347*50000000000000^3323 ≤ 5787730479947^3323*312500000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60115393 312500000 5787730479947 50000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331571593/625000000 : ℝ), (1352905579/2500000000 : ℝ), (-60115393/312500000 : ℝ)] ![(43637646216521/100000000000000 : ℝ), (2799180800207/6250000000000 : ℝ), (5787730479947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331571593/625000000 : ℝ)|^4347 ≤ (43637646216521/100000000000000 : ℝ)^3323
        have hw : |(331571593/625000000 : ℝ)|=(331571593/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352905579/2500000000 : ℝ)|^4347 ≤ (2799180800207/6250000000000 : ℝ)^3323
        have hw : |(1352905579/2500000000 : ℝ)|=(1352905579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-60115393/312500000 : ℝ)|^4347 ≤ (5787730479947/50000000000000 : ℝ)^3323
        have hw : |(-60115393/312500000 : ℝ)|=(60115393/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s4_7 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33710061/78125000 : ℝ)*x 0 + (4495952121/10000000000 : ℝ)*x 1 + (103514499/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33710061/78125000 : ℝ)^4347 ≤ (2081437867677/6250000000000 : ℝ)^3323 := by
    have hnat : (33710061 : ℕ)^4347*6250000000000^3323 ≤ 2081437867677^3323*78125000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33710061 78125000 2081437867677 6250000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4495952121/10000000000 : ℝ)^4347 ≤ (1757141954579/5000000000000 : ℝ)^3323 := by
    have hnat : (4495952121 : ℕ)^4347*5000000000000^3323 ≤ 1757141954579^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495952121 10000000000 1757141954579 5000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103514499/250000000 : ℝ)^4347 ≤ (31554155015199/100000000000000 : ℝ)^3323 := by
    have hnat : (103514499 : ℕ)^4347*100000000000000^3323 ≤ 31554155015199^3323*250000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103514499 250000000 31554155015199 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33710061/78125000 : ℝ), (4495952121/10000000000 : ℝ), (103514499/250000000 : ℝ)] ![(2081437867677/6250000000000 : ℝ), (1757141954579/5000000000000 : ℝ), (31554155015199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33710061/78125000 : ℝ)|^4347 ≤ (2081437867677/6250000000000 : ℝ)^3323
        have hw : |(33710061/78125000 : ℝ)|=(33710061/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4495952121/10000000000 : ℝ)|^4347 ≤ (1757141954579/5000000000000 : ℝ)^3323
        have hw : |(4495952121/10000000000 : ℝ)|=(4495952121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103514499/250000000 : ℝ)|^4347 ≤ (31554155015199/100000000000000 : ℝ)^3323
        have hw : |(103514499/250000000 : ℝ)|=(103514499/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1387_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156504483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3743/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11027/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5607/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14773/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3743/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11027/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3743/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11027/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3743/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11027/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3743/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11027/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3743/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11027/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3743/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11027/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11027/100000 : ℝ) ^ (2173/512 : ℝ) ≤ (2157716844371269/25000000000000000000 : ℝ) := by
    have hpowers : (11027/100000 : ℝ)^2173 ≤ (2157716844371269/25000000000000000000 : ℝ)^512 := by
      have hnat : (11027 : ℕ)^2173*25000000000000000000^512 ≤ 2157716844371269^512*100000^2173 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11027 100000 2157716844371269 25000000000000000000 2173 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11027/100000 : ℝ)) (X := (2157716844371269/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2173 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3743/25000 : ℝ) ^ (2173/512 : ℝ) ≤ (31606148275019981/100000000000000000000 : ℝ) := by
    have hpowers : (3743/25000 : ℝ)^2173 ≤ (31606148275019981/100000000000000000000 : ℝ)^512 := by
      have hnat : (3743 : ℕ)^2173*100000000000000000000^512 ≤ 31606148275019981^512*25000^2173 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3743 25000 31606148275019981 100000000000000000000 2173 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3743/25000 : ℝ)) (X := (31606148275019981/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2173 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502157716844371269/12500000000000000000 : ℝ) ≤ (1250050836546171/1250000000000000 : ℝ) ^ (2173/512 : ℝ) := by
    have hpowers : (12502157716844371269/12500000000000000000 : ℝ)^512 ≤ (1250050836546171/1250000000000000 : ℝ)^2173 := by
      have hnat : (12502157716844371269 : ℕ)^512*1250000000000000^2173 ≤ 1250050836546171^2173*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502157716844371269 12500000000000000000 1250050836546171 1250000000000000 512 2173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250050836546171/1250000000000000 : ℝ)) (X := (12502157716844371269/12500000000000000000 : ℝ)) (by norm_num) 2173 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040237015652505057/100000000000000000000 : ℝ) ≤ (5000473957308911/5000000000000000 : ℝ) ^ (2173/512 : ℝ) := by
    have hpowers : (100040237015652505057/100000000000000000000 : ℝ)^512 ≤ (5000473957308911/5000000000000000 : ℝ)^2173 := by
      have hnat : (100040237015652505057 : ℕ)^512*5000000000000000^2173 ≤ 5000473957308911^2173*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040237015652505057 100000000000000000000 5000473957308911 5000000000000000 512 2173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000473957308911/5000000000000000 : ℝ)) (X := (100040237015652505057/100000000000000000000 : ℝ)) (by norm_num) 2173 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031606148275019981/50000000000000000000 : ℝ) ≤ (2500372284216569/2500000000000000 : ℝ) ^ (2173/512 : ℝ) := by
    have hpowers : (50031606148275019981/50000000000000000000 : ℝ)^512 ≤ (2500372284216569/2500000000000000 : ℝ)^2173 := by
      have hnat : (50031606148275019981 : ℕ)^512*2500000000000000^2173 ≤ 2500372284216569^2173*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031606148275019981 50000000000000000000 2500372284216569 2500000000000000 512 2173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500372284216569/2500000000000000 : ℝ)) (X := (50031606148275019981/50000000000000000000 : ℝ)) (by norm_num) 2173 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2157716844371269/25000000000000000000 : ℝ) ≤ ((9859917071482438061/9862500000000000000 : ℝ)+2*(270611124227/197250000000000 : ℝ)*(11027/100000 : ℝ))^(2173/512 : ℝ) := by
    rw [show (9859917071482438061/9862500000000000000 : ℝ)+2*(270611124227/197250000000000 : ℝ)*(11027/100000 : ℝ)=(1250050836546171/1250000000000000 : ℝ) by norm_num, show 1+2*(2157716844371269/25000000000000000000 : ℝ)=(12502157716844371269/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31606148275019981/100000000000000000000 : ℝ)+(2157716844371269/25000000000000000000 : ℝ) ≤ ((9859917071482438061/9862500000000000000 : ℝ)+(270611124227/197250000000000 : ℝ)*((3743/25000 : ℝ)+(11027/100000 : ℝ)))^(2173/512 : ℝ) := by
    rw [show (9859917071482438061/9862500000000000000 : ℝ)+(270611124227/197250000000000 : ℝ)*((3743/25000 : ℝ)+(11027/100000 : ℝ))=(5000473957308911/5000000000000000 : ℝ) by norm_num, show 1+(31606148275019981/100000000000000000000 : ℝ)+(2157716844371269/25000000000000000000 : ℝ)=(100040237015652505057/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31606148275019981/100000000000000000000 : ℝ) ≤ ((9859917071482438061/9862500000000000000 : ℝ)+2*(270611124227/197250000000000 : ℝ)*(3743/25000 : ℝ))^(2173/512 : ℝ) := by
    rw [show (9859917071482438061/9862500000000000000 : ℝ)+2*(270611124227/197250000000000 : ℝ)*(3743/25000 : ℝ)=(2500372284216569/2500000000000000 : ℝ) by norm_num, show 1+2*(31606148275019981/100000000000000000000 : ℝ)=(50031606148275019981/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9859917071482438061/9862500000000000000 : ℝ)*(X 1 0+X 2 0)+(270611124227/197250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2173/512 : ℝ)) (lo := (11027/100000 : ℝ)) (hi := (3743/25000 : ℝ)) (c := (9859917071482438061/9862500000000000000 : ℝ)) (alpha := (270611124227/197250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9859917071482438061/9862500000000000000 : ℝ)*(X 0 1+X 2 1)+(270611124227/197250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2173/512 : ℝ)) (lo := (11027/100000 : ℝ)) (hi := (3743/25000 : ℝ)) (c := (9859917071482438061/9862500000000000000 : ℝ)) (alpha := (270611124227/197250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9859917071482438061/9862500000000000000 : ℝ)*(X 0 2+X 1 2)+(270611124227/197250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2173/512 : ℝ)) (lo := (11027/100000 : ℝ)) (hi := (3743/25000 : ℝ)) (c := (9859917071482438061/9862500000000000000 : ℝ)) (alpha := (270611124227/197250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2005511229/10000000000 : ℝ)*X 0 0+(108244853/200000000 : ℝ)*X 0 1+(131104273/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348652987/10000000000 : ℝ)*X 1 0+(-2091143873/10000000000 : ℝ)*X 1 1+(1048834171/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348652889/10000000000 : ℝ)*X 2 0+(1048834197/2000000000 : ℝ)*X 2 1+(-2091143831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2157430551/5000000000 : ℝ)*X 0 0+(4139258797/10000000000 : ℝ)*X 0 1+(449726643/1000000000 : ℝ)*X 0 2+(2157430551/5000000000 : ℝ)*X 1 0+(4139258797/10000000000 : ℝ)*X 1 1+(449726643/1000000000 : ℝ)*X 1 2+(2157430551/5000000000 : ℝ)*X 2 0+(4139258797/10000000000 : ℝ)*X 2 1+(449726643/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1002761899/5000000000 : ℝ)*X 0 0+(2622393973/5000000000 : ℝ)*X 0 1+(2705811157/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305145491/10000000000 : ℝ)*X 1 0+(-1923692567/10000000000 : ℝ)*X 1 1+(67645279/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331571593/625000000 : ℝ)*X 2 0+(1352905579/2500000000 : ℝ)*X 2 1+(-60115393/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((33710061/78125000 : ℝ)*X 0 0+(4495952121/10000000000 : ℝ)*X 0 1+(103514499/250000000 : ℝ)*X 0 2+(33710061/78125000 : ℝ)*X 1 0+(4495952121/10000000000 : ℝ)*X 1 1+(103514499/250000000 : ℝ)*X 1 2+(33710061/78125000 : ℝ)*X 2 0+(4495952121/10000000000 : ℝ)*X 2 1+(103514499/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79740788020345546477788861/8218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (986543601/50000000000000 : ℝ)*(base19) + (1711873329/100000000000000 : ℝ)*(base23) + (81404989/100000000000000 : ℝ)*(lower2) + (51557287/25000000000000 : ℝ)*(upper3) + (25359951/20000000000000 : ℝ)*(upper5) + (437159998670301/10000000000000 : ℝ)*(major0) + (437159998670301/10000000000000 : ℝ)*(major1) + (437159998670301/10000000000000 : ℝ)*(major2) + (594988362749443/10000000000000 : ℝ)*(sp0) + (5949923067194869/100000000000000 : ℝ)*(sp1) + (2974961664204371/50000000000000 : ℝ)*(sp2) + (558650960715477/20000000000000 : ℝ)*(sp3) + (1035319691/2500000000000 : ℝ)*(sp4) + (9903068259/50000000000000 : ℝ)*(sp7) + (1396637304856951/50000000000000 : ℝ)*(f.failure) + (5949925040282071/100000000000000 : ℝ)*(f.sum) + (1147698407281/328750000000000000000000000 : ℝ)*base66 + (42789681109766213/32875000000000000000000000000000 : ℝ)*base68 + (323047475709891213/32875000000000000000000000000000 : ℝ)*base70 + (201444005510016213/32875000000000000000000000000000 : ℝ)*base72 + (1767972184327/657500000000000000000000000 : ℝ)*base74 + (282938938010516213/32875000000000000000000000000000 : ℝ)*base76 + (262644744626858787/32875000000000000000000000000000 : ℝ)*base77 + (36330530308516213/32875000000000000000000000000000 : ℝ)*base80 + (1066637991673/164375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (5211333/5000000000000000000000 : ℝ)*base89 + (5211333/5000000000000000000000 : ℝ)*base91 + (5211333/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10435768711336982546458969/2054687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (870853793/100000000000000 : ℝ)*(base19) + (186897963/20000000000000 : ℝ)*(base23) + (52512133/50000000000000 : ℝ)*(upper3) + (15869583/50000000000000 : ℝ)*(lower4) + (21181539/20000000000000 : ℝ)*(upper5) + (55049496874271/1250000000000 : ℝ)*(major0) + (55049496874271/1250000000000 : ℝ)*(major1) + (55049496874271/1250000000000 : ℝ)*(major2) + (1780532203/10000000000000 : ℝ)*(sp1) + (2335388793/12500000000000 : ℝ)*(sp2) + (2996984074074279/50000000000000 : ℝ)*(sp4) + (2996974735986367/50000000000000 : ℝ)*(sp5) + (2996974265274199/50000000000000 : ℝ)*(sp6) + (1406975591217307/50000000000000 : ℝ)*(sp7) + (1406975591217307/50000000000000 : ℝ)*(f.failure) + (2996984074074279/50000000000000 : ℝ)*(f.sum) + (5443559969021/986250000000000000000000000 : ℝ)*base65 + (41239776065657427/4109375000000000000000000000000 : ℝ)*base67 + (38790550635436323/4109375000000000000000000000000 : ℝ)*base70 + (34255342785938677/4109375000000000000000000000000 : ℝ)*base71 + (9485021377237/1972500000000000000000000000 : ℝ)*base73 + (2223422332842573/4109375000000000000000000000000 : ℝ)*base76 + (34891202669251177/4109375000000000000000000000000 : ℝ)*base77 + (63112595399719927/4109375000000000000000000000000 : ℝ)*base79 + (1002374723927/493125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (27312719/5000000000000000000000 : ℝ)*base90 + (27312719/5000000000000000000000 : ℝ)*base92 + (27312719/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1387_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156504483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3743/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11027/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1387_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1387_s5_0 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1002847219/5000000000 : ℝ)*x 0 + (676330793/1250000000 : ℝ)*x 1 + (5245646439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1002847219/5000000000 : ℝ)^4347 ≤ (1528142967293/12500000000000 : ℝ)^3323 := by
    have hnat : (1002847219 : ℕ)^4347*12500000000000^3323 ≤ 1528142967293^3323*5000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002847219 5000000000 1528142967293 12500000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676330793/1250000000 : ℝ)^4347 ≤ (44776326865681/100000000000000 : ℝ)^3323 := by
    have hnat : (676330793 : ℕ)^4347*100000000000000^3323 ≤ 44776326865681^3323*1250000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676330793 1250000000 44776326865681 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245646439/10000000000 : ℝ)^4347 ≤ (5374816171651/12500000000000 : ℝ)^3323 := by
    have hnat : (5245646439 : ℕ)^4347*12500000000000^3323 ≤ 5374816171651^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245646439 10000000000 5374816171651 12500000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1002847219/5000000000 : ℝ), (676330793/1250000000 : ℝ), (5245646439/10000000000 : ℝ)] ![(1528142967293/12500000000000 : ℝ), (44776326865681/100000000000000 : ℝ), (5374816171651/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1002847219/5000000000 : ℝ)|^4347 ≤ (1528142967293/12500000000000 : ℝ)^3323
        have hw : |(-1002847219/5000000000 : ℝ)|=(1002847219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676330793/1250000000 : ℝ)|^4347 ≤ (44776326865681/100000000000000 : ℝ)^3323
        have hw : |(676330793/1250000000 : ℝ)|=(676330793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245646439/10000000000 : ℝ)|^4347 ≤ (5374816171651/12500000000000 : ℝ)^3323
        have hw : |(5245646439/10000000000 : ℝ)|=(5245646439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s5_1 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534824217/1000000000 : ℝ)*x 0 + (-417946687/2000000000 : ℝ)*x 1 + (5245646451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534824217/1000000000 : ℝ)^4347 ≤ (44101957660501/100000000000000 : ℝ)^3323 := by
    have hnat : (534824217 : ℕ)^4347*100000000000000^3323 ≤ 44101957660501^3323*1000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534824217 1000000000 44101957660501 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417946687/2000000000 : ℝ)^4347 ≤ (12899512825029/100000000000000 : ℝ)^3323 := by
    have hnat : (417946687 : ℕ)^4347*100000000000000^3323 ≤ 12899512825029^3323*2000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417946687 2000000000 12899512825029 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245646451/10000000000 : ℝ)^4347 ≤ (42998529501883/100000000000000 : ℝ)^3323 := by
    have hnat : (5245646451 : ℕ)^4347*100000000000000^3323 ≤ 42998529501883^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245646451 10000000000 42998529501883 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534824217/1000000000 : ℝ), (-417946687/2000000000 : ℝ), (5245646451/10000000000 : ℝ)] ![(44101957660501/100000000000000 : ℝ), (12899512825029/100000000000000 : ℝ), (42998529501883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534824217/1000000000 : ℝ)|^4347 ≤ (44101957660501/100000000000000 : ℝ)^3323
        have hw : |(534824217/1000000000 : ℝ)|=(534824217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-417946687/2000000000 : ℝ)|^4347 ≤ (12899512825029/100000000000000 : ℝ)^3323
        have hw : |(-417946687/2000000000 : ℝ)|=(417946687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245646451/10000000000 : ℝ)|^4347 ≤ (42998529501883/100000000000000 : ℝ)^3323
        have hw : |(5245646451/10000000000 : ℝ)|=(5245646451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s5_2 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348242177/10000000000 : ℝ)*x 0 + (5245646441/10000000000 : ℝ)*x 1 + (-2089733439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348242177/10000000000 : ℝ)^4347 ≤ (44101957736011/100000000000000 : ℝ)^3323 := by
    have hnat : (5348242177 : ℕ)^4347*100000000000000^3323 ≤ 44101957736011^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348242177 10000000000 44101957736011 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245646441/10000000000 : ℝ)^4347 ≤ (21499264697327/50000000000000 : ℝ)^3323 := by
    have hnat : (5245646441 : ℕ)^4347*50000000000000^3323 ≤ 21499264697327^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245646441 10000000000 21499264697327 50000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2089733439/10000000000 : ℝ)^4347 ≤ (12899512857329/100000000000000 : ℝ)^3323 := by
    have hnat : (2089733439 : ℕ)^4347*100000000000000^3323 ≤ 12899512857329^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089733439 10000000000 12899512857329 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348242177/10000000000 : ℝ), (5245646441/10000000000 : ℝ), (-2089733439/10000000000 : ℝ)] ![(44101957736011/100000000000000 : ℝ), (21499264697327/50000000000000 : ℝ), (12899512857329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348242177/10000000000 : ℝ)|^4347 ≤ (44101957736011/100000000000000 : ℝ)^3323
        have hw : |(5348242177/10000000000 : ℝ)|=(5348242177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245646441/10000000000 : ℝ)|^4347 ≤ (21499264697327/50000000000000 : ℝ)^3323
        have hw : |(5245646441/10000000000 : ℝ)|=(5245646441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2089733439/10000000000 : ℝ)|^4347 ≤ (12899512857329/100000000000000 : ℝ)^3323
        have hw : |(-2089733439/10000000000 : ℝ)|=(2089733439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s5_3 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4314970857/10000000000 : ℝ)*x 0 + (4142516891/10000000000 : ℝ)*x 1 + (898796289/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314970857/10000000000 : ℝ)^4347 ≤ (33303844394133/100000000000000 : ℝ)^3323 := by
    have hnat : (4314970857 : ℕ)^4347*100000000000000^3323 ≤ 33303844394133^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314970857 10000000000 33303844394133 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4142516891/10000000000 : ℝ)^4347 ≤ (31573465808961/100000000000000 : ℝ)^3323 := by
    have hnat : (4142516891 : ℕ)^4347*100000000000000^3323 ≤ 31573465808961^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4142516891 10000000000 31573465808961 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898796289/2000000000 : ℝ)^4347 ≤ (35122689773233/100000000000000 : ℝ)^3323 := by
    have hnat : (898796289 : ℕ)^4347*100000000000000^3323 ≤ 35122689773233^3323*2000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898796289 2000000000 35122689773233 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314970857/10000000000 : ℝ), (4142516891/10000000000 : ℝ), (898796289/2000000000 : ℝ)] ![(33303844394133/100000000000000 : ℝ), (31573465808961/100000000000000 : ℝ), (35122689773233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314970857/10000000000 : ℝ)|^4347 ≤ (33303844394133/100000000000000 : ℝ)^3323
        have hw : |(4314970857/10000000000 : ℝ)|=(4314970857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4142516891/10000000000 : ℝ)|^4347 ≤ (31573465808961/100000000000000 : ℝ)^3323
        have hw : |(4142516891/10000000000 : ℝ)|=(4142516891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898796289/2000000000 : ℝ)|^4347 ≤ (35122689773233/100000000000000 : ℝ)^3323
        have hw : |(898796289/2000000000 : ℝ)|=(898796289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s5_4 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2005706259/10000000000 : ℝ)*x 0 + (13115603/25000000 : ℝ)*x 1 + (1082009701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2005706259/10000000000 : ℝ)^4347 ≤ (6112618996533/50000000000000 : ℝ)^3323 := by
    have hnat : (2005706259 : ℕ)^4347*50000000000000^3323 ≤ 6112618996533^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005706259 10000000000 6112618996533 50000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13115603/25000000 : ℝ)^4347 ≤ (537561338391/1250000000000 : ℝ)^3323 := by
    have hnat : (13115603 : ℕ)^4347*1250000000000^3323 ≤ 537561338391^3323*25000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13115603 25000000 537561338391 1250000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082009701/2000000000 : ℝ)^4347 ≤ (44769854911053/100000000000000 : ℝ)^3323 := by
    have hnat : (1082009701 : ℕ)^4347*100000000000000^3323 ≤ 44769854911053^3323*2000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082009701 2000000000 44769854911053 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2005706259/10000000000 : ℝ), (13115603/25000000 : ℝ), (1082009701/2000000000 : ℝ)] ![(6112618996533/50000000000000 : ℝ), (537561338391/1250000000000 : ℝ), (44769854911053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2005706259/10000000000 : ℝ)|^4347 ≤ (6112618996533/50000000000000 : ℝ)^3323
        have hw : |(-2005706259/10000000000 : ℝ)|=(2005706259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13115603/25000000 : ℝ)|^4347 ≤ (537561338391/1250000000000 : ℝ)^3323
        have hw : |(13115603/25000000 : ℝ)|=(13115603/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082009701/2000000000 : ℝ)|^4347 ≤ (44769854911053/100000000000000 : ℝ)^3323
        have hw : |(1082009701/2000000000 : ℝ)|=(1082009701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s5_5 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061105967/2000000000 : ℝ)*x 0 + (-1925331381/10000000000 : ℝ)*x 1 + (5410048551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061105967/2000000000 : ℝ)^4347 ≤ (43641781941593/100000000000000 : ℝ)^3323 := by
    have hnat : (1061105967 : ℕ)^4347*100000000000000^3323 ≤ 43641781941593^3323*2000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061105967 2000000000 43641781941593 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1925331381/10000000000 : ℝ)^4347 ≤ (2897090659449/25000000000000 : ℝ)^3323 := by
    have hnat : (1925331381 : ℕ)^4347*25000000000000^3323 ≤ 2897090659449^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925331381 10000000000 2897090659449 25000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410048551/10000000000 : ℝ)^4347 ≤ (44769855409021/100000000000000 : ℝ)^3323 := by
    have hnat : (5410048551 : ℕ)^4347*100000000000000^3323 ≤ 44769855409021^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410048551 10000000000 44769855409021 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061105967/2000000000 : ℝ), (-1925331381/10000000000 : ℝ), (5410048551/10000000000 : ℝ)] ![(43641781941593/100000000000000 : ℝ), (2897090659449/25000000000000 : ℝ), (44769855409021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061105967/2000000000 : ℝ)|^4347 ≤ (43641781941593/100000000000000 : ℝ)^3323
        have hw : |(1061105967/2000000000 : ℝ)|=(1061105967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1925331381/10000000000 : ℝ)|^4347 ≤ (2897090659449/25000000000000 : ℝ)^3323
        have hw : |(-1925331381/10000000000 : ℝ)|=(1925331381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410048551/10000000000 : ℝ)|^4347 ≤ (44769855409021/100000000000000 : ℝ)^3323
        have hw : |(5410048551/10000000000 : ℝ)|=(5410048551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s5_6 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326382457/2500000000 : ℝ)*x 0 + (2705024293/5000000000 : ℝ)*x 1 + (-1925331343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326382457/2500000000 : ℝ)^4347 ≤ (43641781866269/100000000000000 : ℝ)^3323 := by
    have hnat : (1326382457 : ℕ)^4347*100000000000000^3323 ≤ 43641781866269^3323*2500000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326382457 2500000000 43641781866269 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705024293/5000000000 : ℝ)^4347 ≤ (4476985578791/10000000000000 : ℝ)^3323 := by
    have hnat : (2705024293 : ℕ)^4347*10000000000000^3323 ≤ 4476985578791^3323*5000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705024293 5000000000 4476985578791 10000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1925331343/10000000000 : ℝ)^4347 ≤ (11588362338597/100000000000000 : ℝ)^3323 := by
    have hnat : (1925331343 : ℕ)^4347*100000000000000^3323 ≤ 11588362338597^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925331343 10000000000 11588362338597 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326382457/2500000000 : ℝ), (2705024293/5000000000 : ℝ), (-1925331343/10000000000 : ℝ)] ![(43641781866269/100000000000000 : ℝ), (4476985578791/10000000000000 : ℝ), (11588362338597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326382457/2500000000 : ℝ)|^4347 ≤ (43641781866269/100000000000000 : ℝ)^3323
        have hw : |(1326382457/2500000000 : ℝ)|=(1326382457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705024293/5000000000 : ℝ)|^4347 ≤ (4476985578791/10000000000000 : ℝ)^3323
        have hw : |(2705024293/5000000000 : ℝ)|=(2705024293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1925331343/10000000000 : ℝ)|^4347 ≤ (11588362338597/100000000000000 : ℝ)^3323
        have hw : |(-1925331343/10000000000 : ℝ)|=(1925331343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1387_s5_7 (p : ℝ) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (431499607/1000000000 : ℝ)*x 0 + (2246357327/5000000000 : ℝ)*x 1 + (4143790227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431499607/1000000000 : ℝ)^4347 ≤ (33304098960319/100000000000000 : ℝ)^3323 := by
    have hnat : (431499607 : ℕ)^4347*100000000000000^3323 ≤ 33304098960319^3323*1000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431499607 1000000000 33304098960319 100000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246357327/5000000000 : ℝ)^4347 ≤ (1404389552607/4000000000000 : ℝ)^3323 := by
    have hnat : (2246357327 : ℕ)^4347*4000000000000^3323 ≤ 1404389552607^3323*5000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246357327 5000000000 1404389552607 4000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4143790227/10000000000 : ℝ)^4347 ≤ (7896540554109/25000000000000 : ℝ)^3323 := by
    have hnat : (4143790227 : ℕ)^4347*25000000000000^3323 ≤ 7896540554109^3323*10000000000^4347 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143790227 10000000000 7896540554109 25000000000000 4347 3323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4347/1024 : ℝ)) 4347 3323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431499607/1000000000 : ℝ), (2246357327/5000000000 : ℝ), (4143790227/10000000000 : ℝ)] ![(33304098960319/100000000000000 : ℝ), (1404389552607/4000000000000 : ℝ), (7896540554109/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431499607/1000000000 : ℝ)|^4347 ≤ (33304098960319/100000000000000 : ℝ)^3323
        have hw : |(431499607/1000000000 : ℝ)|=(431499607/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246357327/5000000000 : ℝ)|^4347 ≤ (1404389552607/4000000000000 : ℝ)^3323
        have hw : |(2246357327/5000000000 : ℝ)|=(2246357327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4143790227/10000000000 : ℝ)|^4347 ≤ (7896540554109/25000000000000 : ℝ)^3323
        have hw : |(4143790227/10000000000 : ℝ)|=(4143790227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1387_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156504483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5623/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (737/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5607/50000 : ℝ) ^ (2173/512 : ℝ) ≤ (9269368639884581/100000000000000000000 : ℝ) := by
    have hpowers : (5607/50000 : ℝ)^2173 ≤ (9269368639884581/100000000000000000000 : ℝ)^512 := by
      have hnat : (5607 : ℕ)^2173*100000000000000000000^512 ≤ 9269368639884581^512*50000^2173 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5607 50000 9269368639884581 100000000000000000000 2173 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5607/50000 : ℝ)) (X := (9269368639884581/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2173 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14773/100000 : ℝ) ^ (2173/512 : ℝ) ≤ (29861275898370071/100000000000000000000 : ℝ) := by
    have hpowers : (14773/100000 : ℝ)^2173 ≤ (29861275898370071/100000000000000000000 : ℝ)^512 := by
      have hnat : (14773 : ℕ)^2173*100000000000000000000^512 ≤ 29861275898370071^512*100000^2173 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14773 100000 29861275898370071 100000000000000000000 2173 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14773/100000 : ℝ)) (X := (29861275898370071/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2173 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009269368639884581/50000000000000000000 : ℝ) ≤ (10000436776853791/10000000000000000 : ℝ) ^ (2173/512 : ℝ) := by
    have hpowers : (50009269368639884581/50000000000000000000 : ℝ)^512 ≤ (10000436776853791/10000000000000000 : ℝ)^2173 := by
      have hnat : (50009269368639884581 : ℕ)^512*10000000000000000^2173 ≤ 10000436776853791^2173*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009269368639884581 50000000000000000000 10000436776853791 10000000000000000 512 2173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000436776853791/10000000000000000 : ℝ)) (X := (50009269368639884581/50000000000000000000 : ℝ)) (by norm_num) 2173 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009782661134563663/25000000000000000000 : ℝ) ≤ (5000460927160671/5000000000000000 : ℝ) ^ (2173/512 : ℝ) := by
    have hpowers : (25009782661134563663/25000000000000000000 : ℝ)^512 ≤ (5000460927160671/5000000000000000 : ℝ)^2173 := by
      have hnat : (25009782661134563663 : ℕ)^512*5000000000000000^2173 ≤ 5000460927160671^2173*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009782661134563663 25000000000000000000 5000460927160671 5000000000000000 512 2173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000460927160671/5000000000000000 : ℝ)) (X := (25009782661134563663/25000000000000000000 : ℝ)) (by norm_num) 2173 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029861275898370071/50000000000000000000 : ℝ) ≤ (10001406931788893/10000000000000000 : ℝ) ^ (2173/512 : ℝ) := by
    have hpowers : (50029861275898370071/50000000000000000000 : ℝ)^512 ≤ (10001406931788893/10000000000000000 : ℝ)^2173 := by
      have hnat : (50029861275898370071 : ℕ)^512*10000000000000000^2173 ≤ 10001406931788893^2173*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029861275898370071 50000000000000000000 10001406931788893 10000000000000000 512 2173 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001406931788893/10000000000000000 : ℝ)) (X := (50029861275898370071/50000000000000000000 : ℝ)) (by norm_num) 2173 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9269368639884581/100000000000000000000 : ℝ) ≤ ((35580675171380408341/35590000000000000000 : ℝ)+2*(485077467551/355900000000000 : ℝ)*(5607/50000 : ℝ))^(2173/512 : ℝ) := by
    rw [show (35580675171380408341/35590000000000000000 : ℝ)+2*(485077467551/355900000000000 : ℝ)*(5607/50000 : ℝ)=(10000436776853791/10000000000000000 : ℝ) by norm_num, show 1+2*(9269368639884581/100000000000000000000 : ℝ)=(50009269368639884581/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29861275898370071/100000000000000000000 : ℝ)+(9269368639884581/100000000000000000000 : ℝ) ≤ ((35580675171380408341/35590000000000000000 : ℝ)+(485077467551/355900000000000 : ℝ)*((14773/100000 : ℝ)+(5607/50000 : ℝ)))^(2173/512 : ℝ) := by
    rw [show (35580675171380408341/35590000000000000000 : ℝ)+(485077467551/355900000000000 : ℝ)*((14773/100000 : ℝ)+(5607/50000 : ℝ))=(5000460927160671/5000000000000000 : ℝ) by norm_num, show 1+(29861275898370071/100000000000000000000 : ℝ)+(9269368639884581/100000000000000000000 : ℝ)=(25009782661134563663/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29861275898370071/100000000000000000000 : ℝ) ≤ ((35580675171380408341/35590000000000000000 : ℝ)+2*(485077467551/355900000000000 : ℝ)*(14773/100000 : ℝ))^(2173/512 : ℝ) := by
    rw [show (35580675171380408341/35590000000000000000 : ℝ)+2*(485077467551/355900000000000 : ℝ)*(14773/100000 : ℝ)=(10001406931788893/10000000000000000 : ℝ) by norm_num, show 1+2*(29861275898370071/100000000000000000000 : ℝ)=(50029861275898370071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35580675171380408341/35590000000000000000 : ℝ)*(X 1 0+X 2 0)+(485077467551/355900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2173/512 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (35580675171380408341/35590000000000000000 : ℝ)) (alpha := (485077467551/355900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35580675171380408341/35590000000000000000 : ℝ)*(X 0 1+X 2 1)+(485077467551/355900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2173/512 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (35580675171380408341/35590000000000000000 : ℝ)) (alpha := (485077467551/355900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35580675171380408341/35590000000000000000 : ℝ)*(X 0 2+X 1 2)+(485077467551/355900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2173/512 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (35580675171380408341/35590000000000000000 : ℝ)) (alpha := (485077467551/355900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1002847219/5000000000 : ℝ)*X 0 0+(676330793/1250000000 : ℝ)*X 0 1+(5245646439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534824217/1000000000 : ℝ)*X 1 0+(-417946687/2000000000 : ℝ)*X 1 1+(5245646451/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348242177/10000000000 : ℝ)*X 2 0+(5245646441/10000000000 : ℝ)*X 2 1+(-2089733439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4314970857/10000000000 : ℝ)*X 0 0+(4142516891/10000000000 : ℝ)*X 0 1+(898796289/2000000000 : ℝ)*X 0 2+(4314970857/10000000000 : ℝ)*X 1 0+(4142516891/10000000000 : ℝ)*X 1 1+(898796289/2000000000 : ℝ)*X 1 2+(4314970857/10000000000 : ℝ)*X 2 0+(4142516891/10000000000 : ℝ)*X 2 1+(898796289/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2005706259/10000000000 : ℝ)*X 0 0+(13115603/25000000 : ℝ)*X 0 1+(1082009701/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061105967/2000000000 : ℝ)*X 1 0+(-1925331381/10000000000 : ℝ)*X 1 1+(5410048551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326382457/2500000000 : ℝ)*X 2 0+(2705024293/5000000000 : ℝ)*X 2 1+(-1925331343/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((431499607/1000000000 : ℝ)*X 0 0+(2246357327/5000000000 : ℝ)*X 0 1+(4143790227/10000000000 : ℝ)*X 0 2+(431499607/1000000000 : ℝ)*X 1 0+(2246357327/5000000000 : ℝ)*X 1 1+(4143790227/10000000000 : ℝ)*X 1 2+(431499607/1000000000 : ℝ)*X 2 0+(2246357327/5000000000 : ℝ)*X 2 1+(4143790227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1387_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (111051306885351592215045591/22243750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57582779/6250000000000 : ℝ)*(base19) + (27036451/3125000000000 : ℝ)*(base23) + (3427713/10000000000000 : ℝ)*(lower2) + (64343023/50000000000000 : ℝ)*(upper3) + (78143243/100000000000000 : ℝ)*(upper5) + (55661903767583/1250000000000 : ℝ)*(major0) + (55661903767583/1250000000000 : ℝ)*(major1) + (55661903767583/1250000000000 : ℝ)*(major2) + (6060629747281673/100000000000000 : ℝ)*(sp0) + (1515162021163523/25000000000000 : ℝ)*(sp1) + (1515162035203031/25000000000000 : ℝ)*(sp2) + (1422622864548939/50000000000000 : ℝ)*(sp3) + (19258696883/100000000000000 : ℝ)*(sp4) + (9701321097/100000000000000 : ℝ)*(sp7) + (1422627715209487/50000000000000 : ℝ)*(f.failure) + (1515162251494639/25000000000000 : ℝ)*(f.sum) + (679267529093/3559000000000000000000000000 : ℝ)*base65 + (252551682409009803/44487500000000000000000000000000 : ℝ)*base67 + (150178940538952697/44487500000000000000000000000000 : ℝ)*base70 + (13006779963359803/44487500000000000000000000000000 : ℝ)*base71 + (3074635356371/889750000000000000000000000 : ℝ)*base73 + (472166347509827697/44487500000000000000000000000000 : ℝ)*base76 + (372808586936209803/44487500000000000000000000000000 : ℝ)*base77 + (197012705674659803/44487500000000000000000000000000 : ℝ)*base79 + (8779392557059/3559000000000000000000000000 : ℝ)*base82 + (369779/5000000000000000000000 : ℝ)*base90 + (369779/5000000000000000000000 : ℝ)*base92 + (369779/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8167994949057865240179/889750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1448045919/100000000000000 : ℝ)*(base19) + (810317693/50000000000000 : ℝ)*(base23) + (105670967/50000000000000 : ℝ)*(upper3) + (17949299/25000000000000 : ℝ)*(lower4) + (84472929/50000000000000 : ℝ)*(upper5) + (224267034224289/5000000000000 : ℝ)*(major0) + (224267034224289/5000000000000 : ℝ)*(major1) + (224267034224289/5000000000000 : ℝ)*(major2) + (1830062819/6250000000000 : ℝ)*(sp1) + (34910274181/100000000000000 : ℝ)*(sp2) + (6104730772914333/100000000000000 : ℝ)*(sp4) + (6104700043863311/100000000000000 : ℝ)*(sp5) + (3052347121002383/50000000000000 : ℝ)*(sp6) + (716487572513463/25000000000000 : ℝ)*(sp7) + (716487572513463/25000000000000 : ℝ)*(f.failure) + (6104730772914333/100000000000000 : ℝ)*(f.sum) + (1287466677269/3559000000000000000000000000 : ℝ)*base65 + (90357257140694549/177950000000000000000000000000000 : ℝ)*base67 + (366969897670744549/177950000000000000000000000000000 : ℝ)*base69 + (577367054215455451/177950000000000000000000000000000 : ℝ)*base72 + (1811418799313/3559000000000000000000000000 : ℝ)*base73 + (2460366629324255451/177950000000000000000000000000000 : ℝ)*base76 + (509581080329455451/177950000000000000000000000000000 : ℝ)*base78 + (64504485929544549/177950000000000000000000000000000 : ℝ)*base79 + (10922982933243/3559000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (37354629/2500000000000000000000 : ℝ)*base89 + (37354629/2500000000000000000000 : ℝ)*base91 + (37354629/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1387_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156504483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (737/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1387_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1387_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156504483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15937/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2533/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (737/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1387_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1387_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1387_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2173/512 : ℝ) ≤ p) (hpb : p ≤ (4347/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156504483/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15937/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2533/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5623/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (737/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1387_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
