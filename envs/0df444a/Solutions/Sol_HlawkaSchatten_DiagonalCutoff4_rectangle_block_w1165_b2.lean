-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1165_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:41:53.059628+00:00
-- url     : https://prove2.me/submissions/f549fd91-0f81-4b31-a3f4-e829a1c2bf56

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
theorem support_rectangle_w1165_s6_0 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2155907933/10000000000 : ℝ)*x 0 + (5392917987/10000000000 : ℝ)*x 1 + (5265820601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155907933/10000000000 : ℝ)^4179 ≤ (6551193814821/50000000000000 : ℝ)^3155 := by
    have hnat : (2155907933 : ℕ)^4179*50000000000000^3155 ≤ 6551193814821^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155907933 10000000000 6551193814821 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392917987/10000000000 : ℝ)^4179 ≤ (8827006107907/20000000000000 : ℝ)^3155 := by
    have hnat : (5392917987 : ℕ)^4179*20000000000000^3155 ≤ 8827006107907^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392917987 10000000000 8827006107907 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265820601/10000000000 : ℝ)^4179 ≤ (8552516362383/20000000000000 : ℝ)^3155 := by
    have hnat : (5265820601 : ℕ)^4179*20000000000000^3155 ≤ 8552516362383^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265820601 10000000000 8552516362383 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2155907933/10000000000 : ℝ), (5392917987/10000000000 : ℝ), (5265820601/10000000000 : ℝ)] ![(6551193814821/50000000000000 : ℝ), (8827006107907/20000000000000 : ℝ), (8552516362383/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2155907933/10000000000 : ℝ)|^4179 ≤ (6551193814821/50000000000000 : ℝ)^3155
        have hw : |(-2155907933/10000000000 : ℝ)|=(2155907933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392917987/10000000000 : ℝ)|^4179 ≤ (8827006107907/20000000000000 : ℝ)^3155
        have hw : |(5392917987/10000000000 : ℝ)|=(5392917987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265820601/10000000000 : ℝ)|^4179 ≤ (8552516362383/20000000000000 : ℝ)^3155
        have hw : |(5265820601/10000000000 : ℝ)|=(5265820601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s6_1 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672372479/5000000000 : ℝ)*x 0 + (-111018637/500000000 : ℝ)*x 1 + (5265820713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672372479/5000000000 : ℝ)^4179 ≤ (43613589401129/100000000000000 : ℝ)^3155 := by
    have hnat : (2672372479 : ℕ)^4179*100000000000000^3155 ≤ 43613589401129^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672372479 5000000000 43613589401129 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111018637/500000000 : ℝ)^4179 ≤ (13623827563291/100000000000000 : ℝ)^3155 := by
    have hnat : (111018637 : ℕ)^4179*100000000000000^3155 ≤ 13623827563291^3155*500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111018637 500000000 13623827563291 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265820713/10000000000 : ℝ)^4179 ≤ (42762583016643/100000000000000 : ℝ)^3155 := by
    have hnat : (5265820713 : ℕ)^4179*100000000000000^3155 ≤ 42762583016643^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265820713 10000000000 42762583016643 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672372479/5000000000 : ℝ), (-111018637/500000000 : ℝ), (5265820713/10000000000 : ℝ)] ![(43613589401129/100000000000000 : ℝ), (13623827563291/100000000000000 : ℝ), (42762583016643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672372479/5000000000 : ℝ)|^4179 ≤ (43613589401129/100000000000000 : ℝ)^3155
        have hw : |(2672372479/5000000000 : ℝ)|=(2672372479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-111018637/500000000 : ℝ)|^4179 ≤ (13623827563291/100000000000000 : ℝ)^3155
        have hw : |(-111018637/500000000 : ℝ)|=(111018637/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265820713/10000000000 : ℝ)|^4179 ≤ (42762583016643/100000000000000 : ℝ)^3155
        have hw : |(5265820713/10000000000 : ℝ)|=(5265820713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s6_2 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344745253/10000000000 : ℝ)*x 0 + (658227531/1250000000 : ℝ)*x 1 + (-2220372963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344745253/10000000000 : ℝ)^4179 ≤ (8722718517931/20000000000000 : ℝ)^3155 := by
    have hnat : (5344745253 : ℕ)^4179*20000000000000^3155 ≤ 8722718517931^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344745253 10000000000 8722718517931 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658227531/1250000000 : ℝ)^4179 ≤ (5345322251859/12500000000000 : ℝ)^3155 := by
    have hnat : (658227531 : ℕ)^4179*12500000000000^3155 ≤ 5345322251859^3155*1250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658227531 1250000000 5345322251859 12500000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2220372963/10000000000 : ℝ)^4179 ≤ (13623829375679/100000000000000 : ℝ)^3155 := by
    have hnat : (2220372963 : ℕ)^4179*100000000000000^3155 ≤ 13623829375679^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220372963 10000000000 13623829375679 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344745253/10000000000 : ℝ), (658227531/1250000000 : ℝ), (-2220372963/10000000000 : ℝ)] ![(8722718517931/20000000000000 : ℝ), (5345322251859/12500000000000 : ℝ), (13623829375679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344745253/10000000000 : ℝ)|^4179 ≤ (8722718517931/20000000000000 : ℝ)^3155
        have hw : |(5344745253/10000000000 : ℝ)|=(5344745253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658227531/1250000000 : ℝ)|^4179 ≤ (5345322251859/12500000000000 : ℝ)^3155
        have hw : |(658227531/1250000000 : ℝ)|=(658227531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2220372963/10000000000 : ℝ)|^4179 ≤ (13623829375679/100000000000000 : ℝ)^3155
        have hw : |(-2220372963/10000000000 : ℝ)|=(2220372963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s6_3 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (872285703/2000000000 : ℝ)*x 0 + (1059064547/2500000000 : ℝ)*x 1 + (561282227/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872285703/2000000000 : ℝ)^4179 ≤ (3331694415243/10000000000000 : ℝ)^3155 := by
    have hnat : (872285703 : ℕ)^4179*10000000000000^3155 ≤ 3331694415243^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872285703 2000000000 3331694415243 10000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059064547/2500000000 : ℝ)^4179 ≤ (32056365063129/100000000000000 : ℝ)^3155 := by
    have hnat : (1059064547 : ℕ)^4179*100000000000000^3155 ≤ 32056365063129^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059064547 2500000000 32056365063129 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561282227/1250000000 : ℝ)^4179 ≤ (17313345382371/50000000000000 : ℝ)^3155 := by
    have hnat : (561282227 : ℕ)^4179*50000000000000^3155 ≤ 17313345382371^3155*1250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561282227 1250000000 17313345382371 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872285703/2000000000 : ℝ), (1059064547/2500000000 : ℝ), (561282227/1250000000 : ℝ)] ![(3331694415243/10000000000000 : ℝ), (32056365063129/100000000000000 : ℝ), (17313345382371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872285703/2000000000 : ℝ)|^4179 ≤ (3331694415243/10000000000000 : ℝ)^3155
        have hw : |(872285703/2000000000 : ℝ)|=(872285703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059064547/2500000000 : ℝ)|^4179 ≤ (32056365063129/100000000000000 : ℝ)^3155
        have hw : |(1059064547/2500000000 : ℝ)|=(1059064547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561282227/1250000000 : ℝ)|^4179 ≤ (17313345382371/50000000000000 : ℝ)^3155
        have hw : |(561282227/1250000000 : ℝ)|=(561282227/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s6_4 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2155913117/10000000000 : ℝ)*x 0 + (5266141321/10000000000 : ℝ)*x 1 + (1078519177/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155913117/10000000000 : ℝ)^4179 ≤ (2620485872121/20000000000000 : ℝ)^3155 := by
    have hnat : (2155913117 : ℕ)^4179*20000000000000^3155 ≤ 2620485872121^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155913117 10000000000 2620485872121 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266141321/10000000000 : ℝ)^4179 ≤ (21383015834889/50000000000000 : ℝ)^3155 := by
    have hnat : (5266141321 : ℕ)^4179*50000000000000^3155 ≤ 21383015834889^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266141321 10000000000 21383015834889 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078519177/2000000000 : ℝ)^4179 ≤ (44131538960837/100000000000000 : ℝ)^3155 := by
    have hnat : (1078519177 : ℕ)^4179*100000000000000^3155 ≤ 44131538960837^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078519177 2000000000 44131538960837 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2155913117/10000000000 : ℝ), (5266141321/10000000000 : ℝ), (1078519177/2000000000 : ℝ)] ![(2620485872121/20000000000000 : ℝ), (21383015834889/50000000000000 : ℝ), (44131538960837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2155913117/10000000000 : ℝ)|^4179 ≤ (2620485872121/20000000000000 : ℝ)^3155
        have hw : |(-2155913117/10000000000 : ℝ)|=(2155913117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266141321/10000000000 : ℝ)|^4179 ≤ (21383015834889/50000000000000 : ℝ)^3155
        have hw : |(5266141321/10000000000 : ℝ)|=(5266141321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078519177/2000000000 : ℝ)|^4179 ≤ (44131538960837/100000000000000 : ℝ)^3155
        have hw : |(1078519177/2000000000 : ℝ)|=(1078519177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s6_5 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312490123/10000000000 : ℝ)*x 0 + (-2093597289/10000000000 : ℝ)*x 1 + (5392595877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312490123/10000000000 : ℝ)^4179 ≤ (8653060593/20000000000 : ℝ)^3155 := by
    have hnat : (5312490123 : ℕ)^4179*20000000000^3155 ≤ 8653060593^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312490123 10000000000 8653060593 20000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2093597289/10000000000 : ℝ)^4179 ≤ (12603158145879/100000000000000 : ℝ)^3155 := by
    have hnat : (2093597289 : ℕ)^4179*100000000000000^3155 ≤ 12603158145879^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093597289 10000000000 12603158145879 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392595877/10000000000 : ℝ)^4179 ≤ (22065769437059/50000000000000 : ℝ)^3155 := by
    have hnat : (5392595877 : ℕ)^4179*50000000000000^3155 ≤ 22065769437059^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392595877 10000000000 22065769437059 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312490123/10000000000 : ℝ), (-2093597289/10000000000 : ℝ), (5392595877/10000000000 : ℝ)] ![(8653060593/20000000000 : ℝ), (12603158145879/100000000000000 : ℝ), (22065769437059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312490123/10000000000 : ℝ)|^4179 ≤ (8653060593/20000000000 : ℝ)^3155
        have hw : |(5312490123/10000000000 : ℝ)|=(5312490123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2093597289/10000000000 : ℝ)|^4179 ≤ (12603158145879/100000000000000 : ℝ)^3155
        have hw : |(-2093597289/10000000000 : ℝ)|=(2093597289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392595877/10000000000 : ℝ)|^4179 ≤ (22065769437059/50000000000000 : ℝ)^3155
        have hw : |(5392595877/10000000000 : ℝ)|=(5392595877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s6_6 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312490127/10000000000 : ℝ)*x 0 + (2696297929/5000000000 : ℝ)*x 1 + (-2093597309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312490127/10000000000 : ℝ)^4179 ≤ (43265303008149/100000000000000 : ℝ)^3155 := by
    have hnat : (5312490127 : ℕ)^4179*100000000000000^3155 ≤ 43265303008149^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312490127 10000000000 43265303008149 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696297929/5000000000 : ℝ)^4179 ≤ (44131538668161/100000000000000 : ℝ)^3155 := by
    have hnat : (2696297929 : ℕ)^4179*100000000000000^3155 ≤ 44131538668161^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696297929 5000000000 44131538668161 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2093597309/10000000000 : ℝ)^4179 ≤ (12603158305353/100000000000000 : ℝ)^3155 := by
    have hnat : (2093597309 : ℕ)^4179*100000000000000^3155 ≤ 12603158305353^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093597309 10000000000 12603158305353 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312490127/10000000000 : ℝ), (2696297929/5000000000 : ℝ), (-2093597309/10000000000 : ℝ)] ![(43265303008149/100000000000000 : ℝ), (44131538668161/100000000000000 : ℝ), (12603158305353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312490127/10000000000 : ℝ)|^4179 ≤ (43265303008149/100000000000000 : ℝ)^3155
        have hw : |(5312490127/10000000000 : ℝ)|=(5312490127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696297929/5000000000 : ℝ)|^4179 ≤ (44131538668161/100000000000000 : ℝ)^3155
        have hw : |(2696297929/5000000000 : ℝ)|=(2696297929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2093597309/10000000000 : ℝ)|^4179 ≤ (12603158305353/100000000000000 : ℝ)^3155
        have hw : |(-2093597309/10000000000 : ℝ)|=(2093597309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s6_7 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2180718931/5000000000 : ℝ)*x 0 + (2244808059/5000000000 : ℝ)*x 1 + (2118451331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180718931/5000000000 : ℝ)^4179 ≤ (16658519364309/50000000000000 : ℝ)^3155 := by
    have hnat : (2180718931 : ℕ)^4179*50000000000000^3155 ≤ 16658519364309^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180718931 5000000000 16658519364309 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244808059/5000000000 : ℝ)^4179 ≤ (4327517044857/12500000000000 : ℝ)^3155 := by
    have hnat : (2244808059 : ℕ)^4179*12500000000000^3155 ≤ 4327517044857^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244808059 5000000000 4327517044857 12500000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118451331/5000000000 : ℝ)^4179 ≤ (32062824891573/100000000000000 : ℝ)^3155 := by
    have hnat : (2118451331 : ℕ)^4179*100000000000000^3155 ≤ 32062824891573^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118451331 5000000000 32062824891573 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180718931/5000000000 : ℝ), (2244808059/5000000000 : ℝ), (2118451331/5000000000 : ℝ)] ![(16658519364309/50000000000000 : ℝ), (4327517044857/12500000000000 : ℝ), (32062824891573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180718931/5000000000 : ℝ)|^4179 ≤ (16658519364309/50000000000000 : ℝ)^3155
        have hw : |(2180718931/5000000000 : ℝ)|=(2180718931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244808059/5000000000 : ℝ)|^4179 ≤ (4327517044857/12500000000000 : ℝ)^3155
        have hw : |(2244808059/5000000000 : ℝ)|=(2244808059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2118451331/5000000000 : ℝ)|^4179 ≤ (32062824891573/100000000000000 : ℝ)^3155
        have hw : |(2118451331/5000000000 : ℝ)|=(2118451331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1165_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11377/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14069/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7049/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11349/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7049/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11349/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7049/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11349/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7049/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11349/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7049/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11349/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7049/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11349/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11349/100000 : ℝ) ^ (8357/2048 : ℝ) ≤ (6960841071360989/50000000000000000000 : ℝ) := by
    have hpowers : (11349/100000 : ℝ)^8357 ≤ (6960841071360989/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11349 : ℕ)^8357*50000000000000000000^2048 ≤ 6960841071360989^2048*100000^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11349 100000 6960841071360989 50000000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11349/100000 : ℝ)) (X := (6960841071360989/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7049/50000 : ℝ) ^ (8357/2048 : ℝ) ≤ (33734999101146457/100000000000000000000 : ℝ) := by
    have hpowers : (7049/50000 : ℝ)^8357 ≤ (33734999101146457/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7049 : ℕ)^8357*100000000000000000000^2048 ≤ 33734999101146457^2048*50000^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7049 50000 33734999101146457 100000000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7049/50000 : ℝ)) (X := (33734999101146457/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006960841071360989/25000000000000000000 : ℝ) ≤ (5000341134485493/5000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (25006960841071360989/25000000000000000000 : ℝ)^2048 ≤ (5000341134485493/5000000000000000 : ℝ)^8357 := by
      have hnat : (25006960841071360989 : ℕ)^2048*5000000000000000^8357 ≤ 5000341134485493^8357*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006960841071360989 25000000000000000000 5000341134485493 5000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000341134485493/5000000000000000 : ℝ)) (X := (25006960841071360989/25000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009531336248773687/20000000000000000000 : ℝ) ≤ (10001167683747551/10000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (20009531336248773687/20000000000000000000 : ℝ)^2048 ≤ (10001167683747551/10000000000000000 : ℝ)^8357 := by
      have hnat : (20009531336248773687 : ℕ)^2048*10000000000000000^8357 ≤ 10001167683747551^8357*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009531336248773687 20000000000000000000 10001167683747551 10000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001167683747551/10000000000000000 : ℝ)) (X := (20009531336248773687/20000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033734999101146457/50000000000000000000 : ℝ) ≤ (2500413274631029/2500000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (50033734999101146457/50000000000000000000 : ℝ)^2048 ≤ (2500413274631029/2500000000000000 : ℝ)^8357 := by
      have hnat : (50033734999101146457 : ℕ)^2048*2500000000000000^8357 ≤ 2500413274631029^8357*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033734999101146457 50000000000000000000 2500413274631029 2500000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500413274631029/2500000000000000 : ℝ)) (X := (50033734999101146457/50000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6960841071360989/50000000000000000000 : ℝ) ≤ ((1717553600800173009/1718125000000000000 : ℝ)+2*(97082955313/54980000000000 : ℝ)*(11349/100000 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (1717553600800173009/1718125000000000000 : ℝ)+2*(97082955313/54980000000000 : ℝ)*(11349/100000 : ℝ)=(5000341134485493/5000000000000000 : ℝ) by norm_num, show 1+2*(6960841071360989/50000000000000000000 : ℝ)=(25006960841071360989/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33734999101146457/100000000000000000000 : ℝ)+(6960841071360989/50000000000000000000 : ℝ) ≤ ((1717553600800173009/1718125000000000000 : ℝ)+(97082955313/54980000000000 : ℝ)*((7049/50000 : ℝ)+(11349/100000 : ℝ)))^(8357/2048 : ℝ) := by
    rw [show (1717553600800173009/1718125000000000000 : ℝ)+(97082955313/54980000000000 : ℝ)*((7049/50000 : ℝ)+(11349/100000 : ℝ))=(10001167683747551/10000000000000000 : ℝ) by norm_num, show 1+(33734999101146457/100000000000000000000 : ℝ)+(6960841071360989/50000000000000000000 : ℝ)=(20009531336248773687/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33734999101146457/100000000000000000000 : ℝ) ≤ ((1717553600800173009/1718125000000000000 : ℝ)+2*(97082955313/54980000000000 : ℝ)*(7049/50000 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (1717553600800173009/1718125000000000000 : ℝ)+2*(97082955313/54980000000000 : ℝ)*(7049/50000 : ℝ)=(2500413274631029/2500000000000000 : ℝ) by norm_num, show 1+2*(33734999101146457/100000000000000000000 : ℝ)=(50033734999101146457/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1717553600800173009/1718125000000000000 : ℝ)*(X 1 0+X 2 0)+(97082955313/54980000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (11349/100000 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (1717553600800173009/1718125000000000000 : ℝ)) (alpha := (97082955313/54980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1717553600800173009/1718125000000000000 : ℝ)*(X 0 1+X 2 1)+(97082955313/54980000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (11349/100000 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (1717553600800173009/1718125000000000000 : ℝ)) (alpha := (97082955313/54980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1717553600800173009/1718125000000000000 : ℝ)*(X 0 2+X 1 2)+(97082955313/54980000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (11349/100000 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (1717553600800173009/1718125000000000000 : ℝ)) (alpha := (97082955313/54980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2155907933/10000000000 : ℝ)*X 0 0+(5392917987/10000000000 : ℝ)*X 0 1+(5265820601/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672372479/5000000000 : ℝ)*X 1 0+(-111018637/500000000 : ℝ)*X 1 1+(5265820713/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344745253/10000000000 : ℝ)*X 2 0+(658227531/1250000000 : ℝ)*X 2 1+(-2220372963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((872285703/2000000000 : ℝ)*X 0 0+(1059064547/2500000000 : ℝ)*X 0 1+(561282227/1250000000 : ℝ)*X 0 2+(872285703/2000000000 : ℝ)*X 1 0+(1059064547/2500000000 : ℝ)*X 1 1+(561282227/1250000000 : ℝ)*X 1 2+(872285703/2000000000 : ℝ)*X 2 0+(1059064547/2500000000 : ℝ)*X 2 1+(561282227/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2155913117/10000000000 : ℝ)*X 0 0+(5266141321/10000000000 : ℝ)*X 0 1+(1078519177/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312490123/10000000000 : ℝ)*X 1 0+(-2093597289/10000000000 : ℝ)*X 1 1+(5392595877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312490127/10000000000 : ℝ)*X 2 0+(2696297929/5000000000 : ℝ)*X 2 1+(-2093597309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180718931/5000000000 : ℝ)*X 0 0+(2244808059/5000000000 : ℝ)*X 0 1+(2118451331/5000000000 : ℝ)*X 0 2+(2180718931/5000000000 : ℝ)*X 1 0+(2244808059/5000000000 : ℝ)*X 1 1+(2118451331/5000000000 : ℝ)*X 1 2+(2180718931/5000000000 : ℝ)*X 2 0+(2244808059/5000000000 : ℝ)*X 2 1+(2118451331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3281254998115634835699/687250000000000000000000000 : ℝ) := by norm_num
    linear_combination (137295747/50000000000000 : ℝ)*(base23) + (22559973/10000000000000 : ℝ)*(lower2) + (17624273/20000000000000 : ℝ)*(upper3) + (180498603/100000000000000 : ℝ)*(lower4) + (54481887/100000000000000 : ℝ)*(upper5) + (368906669673871/6250000000000 : ℝ)*(major0) + (368906669673871/6250000000000 : ℝ)*(major1) + (368906669673871/6250000000000 : ℝ)*(major2) + (7867978963992719/100000000000000 : ℝ)*(sp0) + (7867978963992719/100000000000000 : ℝ)*(sp1) + (3933983106606239/50000000000000 : ℝ)*(sp2) + (196851121053597/5000000000000 : ℝ)*(sp3) + (3119047187/25000000000000 : ℝ)*(sp6) + (148566877/1250000000000 : ℝ)*(sp7) + (39370343064221/1000000000000 : ℝ)*(f.failure) + (7867978963992719/100000000000000 : ℝ)*(f.sum) + (266429499367589/2749000000000000000000000000 : ℝ)*base66 + (277473781900225731/42953125000000000000000000000000 : ℝ)*base67 + (201805287858444481/42953125000000000000000000000000 : ℝ)*base69 + (2149677341762238697/21476562500000000000000000000000 : ℝ)*base72 + (3177325933627/687250000000000000000000000 : ℝ)*base73 + (460933564929194481/42953125000000000000000000000000 : ℝ)*base75 + (121976222269051197/21476562500000000000000000000000 : ℝ)*base78 + (233854025550627161/10738281250000000000000000000000 : ℝ)*base80 + (1778592279991/1374500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (74407/12500000000000000000 : ℝ)*base90 + (74407/12500000000000000000 : ℝ)*base92 + (74407/12500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64212588103947926029506723/8590625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83514989/6250000000000 : ℝ)*(base19) + (693115229/50000000000000 : ℝ)*(base23) + (67382883/50000000000000 : ℝ)*(upper3) + (26540509/100000000000000 : ℝ)*(lower4) + (163151053/100000000000000 : ℝ)*(upper5) + (296625740356063/5000000000000 : ℝ)*(major0) + (296625740356063/5000000000000 : ℝ)*(major1) + (296625740356063/5000000000000 : ℝ)*(major2) + (9358448491/25000000000000 : ℝ)*(sp1) + (9114509437/25000000000000 : ℝ)*(sp2) + (790797934420129/10000000000000 : ℝ)*(sp4) + (7907940574167503/100000000000000 : ℝ)*(sp5) + (1976985374983271/25000000000000 : ℝ)*(sp6) + (1978525010441803/50000000000000 : ℝ)*(sp7) + (1978525010441803/50000000000000 : ℝ)*(f.failure) + (790797934420129/10000000000000 : ℝ)*(f.sum) + (1276595229161/1374500000000000000000000000 : ℝ)*base65 + (26588764468246433/8590625000000000000000000000000 : ℝ)*base68 + (77695536529328567/8590625000000000000000000000000 : ℝ)*base69 + (5733765488332923/2147656250000000000000000000000 : ℝ)*base71 + (5805285172589/2749000000000000000000000000 : ℝ)*base74 + (30414445666487279/4295312500000000000000000000000 : ℝ)*base76 + (16976900563584817/8590625000000000000000000000000 : ℝ)*base77 + (86706258022334817/8590625000000000000000000000000 : ℝ)*base79 + (344867133821/85906250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (9659601/625000000000000000000 : ℝ)*base90 + (9659601/625000000000000000000 : ℝ)*base92 + (9659601/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1165_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1165_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1165_s7_0 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2155932251/10000000000 : ℝ)*x 0 + (1348158249/2500000000 : ℝ)*x 1 + (5266089603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155932251/10000000000 : ℝ)^4179 ≤ (13102583388711/100000000000000 : ℝ)^3155 := by
    have hnat : (2155932251 : ℕ)^4179*100000000000000^3155 ≤ 13102583388711^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155932251 10000000000 13102583388711 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348158249/2500000000 : ℝ)^4179 ≤ (44131941239823/100000000000000 : ℝ)^3155 := by
    have hnat : (1348158249 : ℕ)^4179*100000000000000^3155 ≤ 44131941239823^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348158249 2500000000 44131941239823 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266089603/10000000000 : ℝ)^4179 ≤ (10691368838787/25000000000000 : ℝ)^3155 := by
    have hnat : (5266089603 : ℕ)^4179*25000000000000^3155 ≤ 10691368838787^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266089603 10000000000 10691368838787 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2155932251/10000000000 : ℝ), (1348158249/2500000000 : ℝ), (5266089603/10000000000 : ℝ)] ![(13102583388711/100000000000000 : ℝ), (44131941239823/100000000000000 : ℝ), (10691368838787/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2155932251/10000000000 : ℝ)|^4179 ≤ (13102583388711/100000000000000 : ℝ)^3155
        have hw : |(-2155932251/10000000000 : ℝ)|=(2155932251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348158249/2500000000 : ℝ)|^4179 ≤ (44131941239823/100000000000000 : ℝ)^3155
        have hw : |(1348158249/2500000000 : ℝ)|=(1348158249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266089603/10000000000 : ℝ)|^4179 ≤ (10691368838787/25000000000000 : ℝ)^3155
        have hw : |(5266089603/10000000000 : ℝ)|=(5266089603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s7_1 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534467323/1000000000 : ℝ)*x 0 + (-3552179/16000000 : ℝ)*x 1 + (1053217977/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534467323/1000000000 : ℝ)^4179 ≤ (43612814126401/100000000000000 : ℝ)^3155 := by
    have hnat : (534467323 : ℕ)^4179*100000000000000^3155 ≤ 43612814126401^3155*1000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534467323 1000000000 43612814126401 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3552179/16000000 : ℝ)^4179 ≤ (3405426868939/25000000000000 : ℝ)^3155 := by
    have hnat : (3552179 : ℕ)^4179*25000000000000^3155 ≤ 3405426868939^3155*16000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3552179 16000000 3405426868939 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053217977/2000000000 : ℝ)^4179 ≤ (42765478388531/100000000000000 : ℝ)^3155 := by
    have hnat : (1053217977 : ℕ)^4179*100000000000000^3155 ≤ 42765478388531^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053217977 2000000000 42765478388531 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534467323/1000000000 : ℝ), (-3552179/16000000 : ℝ), (1053217977/2000000000 : ℝ)] ![(43612814126401/100000000000000 : ℝ), (3405426868939/25000000000000 : ℝ), (42765478388531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534467323/1000000000 : ℝ)|^4179 ≤ (43612814126401/100000000000000 : ℝ)^3155
        have hw : |(534467323/1000000000 : ℝ)|=(534467323/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3552179/16000000 : ℝ)|^4179 ≤ (3405426868939/25000000000000 : ℝ)^3155
        have hw : |(-3552179/16000000 : ℝ)|=(3552179/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053217977/2000000000 : ℝ)|^4179 ≤ (42765478388531/100000000000000 : ℝ)^3155
        have hw : |(1053217977/2000000000 : ℝ)|=(1053217977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s7_2 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344673389/10000000000 : ℝ)*x 0 + (5266089973/10000000000 : ℝ)*x 1 + (-1110055773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344673389/10000000000 : ℝ)^4179 ≤ (21806407922477/50000000000000 : ℝ)^3155 := by
    have hnat : (5344673389 : ℕ)^4179*50000000000000^3155 ≤ 21806407922477^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344673389 10000000000 21806407922477 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266089973/10000000000 : ℝ)^4179 ≤ (21382739667559/50000000000000 : ℝ)^3155 := by
    have hnat : (5266089973 : ℕ)^4179*50000000000000^3155 ≤ 21382739667559^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266089973 10000000000 21382739667559 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1110055773/5000000000 : ℝ)^4179 ≤ (13621704801977/100000000000000 : ℝ)^3155 := by
    have hnat : (1110055773 : ℕ)^4179*100000000000000^3155 ≤ 13621704801977^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110055773 5000000000 13621704801977 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344673389/10000000000 : ℝ), (5266089973/10000000000 : ℝ), (-1110055773/5000000000 : ℝ)] ![(21806407922477/50000000000000 : ℝ), (21382739667559/50000000000000 : ℝ), (13621704801977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344673389/10000000000 : ℝ)|^4179 ≤ (21806407922477/50000000000000 : ℝ)^3155
        have hw : |(5344673389/10000000000 : ℝ)|=(5344673389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266089973/10000000000 : ℝ)|^4179 ≤ (21382739667559/50000000000000 : ℝ)^3155
        have hw : |(5266089973/10000000000 : ℝ)|=(5266089973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1110055773/5000000000 : ℝ)|^4179 ≤ (13621704801977/100000000000000 : ℝ)^3155
        have hw : |(-1110055773/5000000000 : ℝ)|=(1110055773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s7_3 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1090360701/2500000000 : ℝ)*x 0 + (2118405253/5000000000 : ℝ)*x 1 + (4489701661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090360701/2500000000 : ℝ)^4179 ≤ (6663417746703/20000000000000 : ℝ)^3155 := by
    have hnat : (1090360701 : ℕ)^4179*20000000000000^3155 ≤ 6663417746703^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090360701 2500000000 6663417746703 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2118405253/5000000000 : ℝ)^4179 ≤ (4007737644309/12500000000000 : ℝ)^3155 := by
    have hnat : (2118405253 : ℕ)^4179*12500000000000^3155 ≤ 4007737644309^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118405253 5000000000 4007737644309 12500000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489701661/10000000000 : ℝ)^4179 ≤ (865525252279/2500000000000 : ℝ)^3155 := by
    have hnat : (4489701661 : ℕ)^4179*2500000000000^3155 ≤ 865525252279^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489701661 10000000000 865525252279 2500000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090360701/2500000000 : ℝ), (2118405253/5000000000 : ℝ), (4489701661/10000000000 : ℝ)] ![(6663417746703/20000000000000 : ℝ), (4007737644309/12500000000000 : ℝ), (865525252279/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090360701/2500000000 : ℝ)|^4179 ≤ (6663417746703/20000000000000 : ℝ)^3155
        have hw : |(1090360701/2500000000 : ℝ)|=(1090360701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2118405253/5000000000 : ℝ)|^4179 ≤ (4007737644309/12500000000000 : ℝ)^3155
        have hw : |(2118405253/5000000000 : ℝ)|=(2118405253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489701661/10000000000 : ℝ)|^4179 ≤ (865525252279/2500000000000 : ℝ)^3155
        have hw : |(4489701661/10000000000 : ℝ)|=(4489701661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s7_4 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-431187289/2000000000 : ℝ)*x 0 + (5266408211/10000000000 : ℝ)*x 1 + (2696156857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431187289/2000000000 : ℝ)^4179 ≤ (655130857517/5000000000000 : ℝ)^3155 := by
    have hnat : (431187289 : ℕ)^4179*5000000000000^3155 ≤ 655130857517^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431187289 2000000000 655130857517 5000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266408211/10000000000 : ℝ)^4179 ≤ (42768902551661/100000000000000 : ℝ)^3155 := by
    have hnat : (5266408211 : ℕ)^4179*100000000000000^3155 ≤ 42768902551661^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266408211 10000000000 42768902551661 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696156857/5000000000 : ℝ)^4179 ≤ (8825696057787/20000000000000 : ℝ)^3155 := by
    have hnat : (2696156857 : ℕ)^4179*20000000000000^3155 ≤ 8825696057787^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696156857 5000000000 8825696057787 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431187289/2000000000 : ℝ), (5266408211/10000000000 : ℝ), (2696156857/5000000000 : ℝ)] ![(655130857517/5000000000000 : ℝ), (42768902551661/100000000000000 : ℝ), (8825696057787/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431187289/2000000000 : ℝ)|^4179 ≤ (655130857517/5000000000000 : ℝ)^3155
        have hw : |(-431187289/2000000000 : ℝ)|=(431187289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266408211/10000000000 : ℝ)|^4179 ≤ (42768902551661/100000000000000 : ℝ)^3155
        have hw : |(5266408211/10000000000 : ℝ)|=(5266408211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696156857/5000000000 : ℝ)|^4179 ≤ (8825696057787/20000000000000 : ℝ)^3155
        have hw : |(2696156857/5000000000 : ℝ)|=(2696156857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s7_5 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656279439/5000000000 : ℝ)*x 0 + (-2093887439/10000000000 : ℝ)*x 1 + (5392314017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656279439/5000000000 : ℝ)^4179 ≤ (43266044650553/100000000000000 : ℝ)^3155 := by
    have hnat : (2656279439 : ℕ)^4179*100000000000000^3155 ≤ 43266044650553^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656279439 5000000000 43266044650553 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2093887439/10000000000 : ℝ)^4179 ≤ (6302735881763/50000000000000 : ℝ)^3155 := by
    have hnat : (2093887439 : ℕ)^4179*50000000000000^3155 ≤ 6302735881763^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093887439 10000000000 6302735881763 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392314017/10000000000 : ℝ)^4179 ≤ (44128483573361/100000000000000 : ℝ)^3155 := by
    have hnat : (5392314017 : ℕ)^4179*100000000000000^3155 ≤ 44128483573361^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392314017 10000000000 44128483573361 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656279439/5000000000 : ℝ), (-2093887439/10000000000 : ℝ), (5392314017/10000000000 : ℝ)] ![(43266044650553/100000000000000 : ℝ), (6302735881763/50000000000000 : ℝ), (44128483573361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656279439/5000000000 : ℝ)|^4179 ≤ (43266044650553/100000000000000 : ℝ)^3155
        have hw : |(2656279439/5000000000 : ℝ)|=(2656279439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2093887439/10000000000 : ℝ)|^4179 ≤ (6302735881763/50000000000000 : ℝ)^3155
        have hw : |(-2093887439/10000000000 : ℝ)|=(2093887439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392314017/10000000000 : ℝ)|^4179 ≤ (44128483573361/100000000000000 : ℝ)^3155
        have hw : |(5392314017/10000000000 : ℝ)|=(5392314017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s7_6 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656279399/5000000000 : ℝ)*x 0 + (674039271/1250000000 : ℝ)*x 1 + (-1046943671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656279399/5000000000 : ℝ)^4179 ≤ (43266043787561/100000000000000 : ℝ)^3155 := by
    have hnat : (2656279399 : ℕ)^4179*100000000000000^3155 ≤ 43266043787561^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656279399 5000000000 43266043787561 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674039271/1250000000 : ℝ)^4179 ≤ (22064242605077/50000000000000 : ℝ)^3155 := by
    have hnat : (674039271 : ℕ)^4179*50000000000000^3155 ≤ 22064242605077^3155*1250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674039271 1250000000 22064242605077 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046943671/5000000000 : ℝ)^4179 ≤ (12605470990043/100000000000000 : ℝ)^3155 := by
    have hnat : (1046943671 : ℕ)^4179*100000000000000^3155 ≤ 12605470990043^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046943671 5000000000 12605470990043 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656279399/5000000000 : ℝ), (674039271/1250000000 : ℝ), (-1046943671/5000000000 : ℝ)] ![(43266043787561/100000000000000 : ℝ), (22064242605077/50000000000000 : ℝ), (12605470990043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656279399/5000000000 : ℝ)|^4179 ≤ (43266043787561/100000000000000 : ℝ)^3155
        have hw : |(2656279399/5000000000 : ℝ)|=(2656279399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674039271/1250000000 : ℝ)|^4179 ≤ (22064242605077/50000000000000 : ℝ)^3155
        have hw : |(674039271/1250000000 : ℝ)|=(674039271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1046943671/5000000000 : ℝ)|^4179 ≤ (12605470990043/100000000000000 : ℝ)^3155
        have hw : |(-1046943671/5000000000 : ℝ)|=(1046943671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s7_7 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4361451917/10000000000 : ℝ)*x 0 + (561133243/1250000000 : ℝ)*x 1 + (4237449069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361451917/10000000000 : ℝ)^4179 ≤ (16658590471053/50000000000000 : ℝ)^3155 := by
    have hnat : (4361451917 : ℕ)^4179*50000000000000^3155 ≤ 16658590471053^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361451917 10000000000 16658590471053 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561133243/1250000000 : ℝ)^4179 ≤ (1730725851791/5000000000000 : ℝ)^3155 := by
    have hnat : (561133243 : ℕ)^4179*5000000000000^3155 ≤ 1730725851791^3155*1250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561133243 1250000000 1730725851791 5000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4237449069/10000000000 : ℝ)^4179 ≤ (16034151001947/50000000000000 : ℝ)^3155 := by
    have hnat : (4237449069 : ℕ)^4179*50000000000000^3155 ≤ 16034151001947^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237449069 10000000000 16034151001947 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361451917/10000000000 : ℝ), (561133243/1250000000 : ℝ), (4237449069/10000000000 : ℝ)] ![(16658590471053/50000000000000 : ℝ), (1730725851791/5000000000000 : ℝ), (16034151001947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361451917/10000000000 : ℝ)|^4179 ≤ (16658590471053/50000000000000 : ℝ)^3155
        have hw : |(4361451917/10000000000 : ℝ)|=(4361451917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561133243/1250000000 : ℝ)|^4179 ≤ (1730725851791/5000000000000 : ℝ)^3155
        have hw : |(561133243/1250000000 : ℝ)|=(561133243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4237449069/10000000000 : ℝ)|^4179 ≤ (16034151001947/50000000000000 : ℝ)^3155
        have hw : |(4237449069/10000000000 : ℝ)|=(4237449069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1165_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5691/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14063/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11377/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11377/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11377/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11377/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11377/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11377/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11377/100000 : ℝ) ^ (8357/2048 : ℝ) ≤ (14062371961861377/100000000000000000000 : ℝ) := by
    have hpowers : (11377/100000 : ℝ)^8357 ≤ (14062371961861377/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11377 : ℕ)^8357*100000000000000000000^2048 ≤ 14062371961861377^2048*100000^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11377 100000 14062371961861377 100000000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11377/100000 : ℝ)) (X := (14062371961861377/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14069/100000 : ℝ) ^ (8357/2048 : ℝ) ≤ (4181591082167129/12500000000000000000 : ℝ) := by
    have hpowers : (14069/100000 : ℝ)^8357 ≤ (4181591082167129/12500000000000000000 : ℝ)^2048 := by
      have hnat : (14069 : ℕ)^8357*12500000000000000000^2048 ≤ 4181591082167129^2048*100000^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14069 100000 4181591082167129 12500000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14069/100000 : ℝ)) (X := (4181591082167129/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014062371961861377/50000000000000000000 : ℝ) ≤ (5000344581558523/5000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (50014062371961861377/50000000000000000000 : ℝ)^2048 ≤ (5000344581558523/5000000000000000 : ℝ)^8357 := by
      have hnat : (50014062371961861377 : ℕ)^2048*5000000000000000^8357 ≤ 5000344581558523^8357*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014062371961861377 50000000000000000000 5000344581558523 5000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000344581558523/5000000000000000 : ℝ)) (X := (50014062371961861377/50000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047515100619198409/100000000000000000000 : ℝ) ≤ (5000582107680897/5000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (100047515100619198409/100000000000000000000 : ℝ)^2048 ≤ (5000582107680897/5000000000000000 : ℝ)^8357 := by
      have hnat : (100047515100619198409 : ℕ)^2048*5000000000000000^8357 ≤ 5000582107680897^8357*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047515100619198409 100000000000000000000 5000582107680897 5000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000582107680897/5000000000000000 : ℝ)) (X := (100047515100619198409/100000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254181591082167129/6250000000000000000 : ℝ) ≤ (5000819633803271/5000000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (6254181591082167129/6250000000000000000 : ℝ)^2048 ≤ (5000819633803271/5000000000000000 : ℝ)^8357 := by
      have hnat : (6254181591082167129 : ℕ)^2048*5000000000000000^8357 ≤ 5000819633803271^8357*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254181591082167129 6250000000000000000 5000819633803271 5000000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000819633803271/5000000000000000 : ℝ)) (X := (6254181591082167129/6250000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14062371961861377/100000000000000000000 : ℝ) ≤ ((84097018401044037/84125000000000000 : ℝ)+2*(118763061187/67300000000000 : ℝ)*(11377/100000 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (84097018401044037/84125000000000000 : ℝ)+2*(118763061187/67300000000000 : ℝ)*(11377/100000 : ℝ)=(5000344581558523/5000000000000000 : ℝ) by norm_num, show 1+2*(14062371961861377/100000000000000000000 : ℝ)=(50014062371961861377/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4181591082167129/12500000000000000000 : ℝ)+(14062371961861377/100000000000000000000 : ℝ) ≤ ((84097018401044037/84125000000000000 : ℝ)+(118763061187/67300000000000 : ℝ)*((14069/100000 : ℝ)+(11377/100000 : ℝ)))^(8357/2048 : ℝ) := by
    rw [show (84097018401044037/84125000000000000 : ℝ)+(118763061187/67300000000000 : ℝ)*((14069/100000 : ℝ)+(11377/100000 : ℝ))=(5000582107680897/5000000000000000 : ℝ) by norm_num, show 1+(4181591082167129/12500000000000000000 : ℝ)+(14062371961861377/100000000000000000000 : ℝ)=(100047515100619198409/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4181591082167129/12500000000000000000 : ℝ) ≤ ((84097018401044037/84125000000000000 : ℝ)+2*(118763061187/67300000000000 : ℝ)*(14069/100000 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (84097018401044037/84125000000000000 : ℝ)+2*(118763061187/67300000000000 : ℝ)*(14069/100000 : ℝ)=(5000819633803271/5000000000000000 : ℝ) by norm_num, show 1+2*(4181591082167129/12500000000000000000 : ℝ)=(6254181591082167129/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (84097018401044037/84125000000000000 : ℝ)*(X 1 0+X 2 0)+(118763061187/67300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (11377/100000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (84097018401044037/84125000000000000 : ℝ)) (alpha := (118763061187/67300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (84097018401044037/84125000000000000 : ℝ)*(X 0 1+X 2 1)+(118763061187/67300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (11377/100000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (84097018401044037/84125000000000000 : ℝ)) (alpha := (118763061187/67300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (84097018401044037/84125000000000000 : ℝ)*(X 0 2+X 1 2)+(118763061187/67300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (11377/100000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (84097018401044037/84125000000000000 : ℝ)) (alpha := (118763061187/67300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2155932251/10000000000 : ℝ)*X 0 0+(1348158249/2500000000 : ℝ)*X 0 1+(5266089603/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534467323/1000000000 : ℝ)*X 1 0+(-3552179/16000000 : ℝ)*X 1 1+(1053217977/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344673389/10000000000 : ℝ)*X 2 0+(5266089973/10000000000 : ℝ)*X 2 1+(-1110055773/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1090360701/2500000000 : ℝ)*X 0 0+(2118405253/5000000000 : ℝ)*X 0 1+(4489701661/10000000000 : ℝ)*X 0 2+(1090360701/2500000000 : ℝ)*X 1 0+(2118405253/5000000000 : ℝ)*X 1 1+(4489701661/10000000000 : ℝ)*X 1 2+(1090360701/2500000000 : ℝ)*X 2 0+(2118405253/5000000000 : ℝ)*X 2 1+(4489701661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-431187289/2000000000 : ℝ)*X 0 0+(5266408211/10000000000 : ℝ)*X 0 1+(2696156857/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656279439/5000000000 : ℝ)*X 1 0+(-2093887439/10000000000 : ℝ)*X 1 1+(5392314017/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656279399/5000000000 : ℝ)*X 2 0+(674039271/1250000000 : ℝ)*X 2 1+(-1046943671/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4361451917/10000000000 : ℝ)*X 0 0+(561133243/1250000000 : ℝ)*X 0 1+(4237449069/10000000000 : ℝ)*X 0 2+(4361451917/10000000000 : ℝ)*X 1 0+(561133243/1250000000 : ℝ)*X 1 1+(4237449069/10000000000 : ℝ)*X 1 2+(4361451917/10000000000 : ℝ)*X 2 0+(561133243/1250000000 : ℝ)*X 2 1+(4237449069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23100156935943619933070943/2103125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (152941013/10000000000000 : ℝ)*(base19) + (1747103907/100000000000000 : ℝ)*(base23) + (11266321/5000000000000 : ℝ)*(upper3) + (2324921/25000000000000 : ℝ)*(upper4) + (393253299/50000000000000 : ℝ)*(upper5) + (2964206258818987/50000000000000 : ℝ)*(major0) + (2964206258818987/50000000000000 : ℝ)*(major1) + (2964206258818987/50000000000000 : ℝ)*(major2) + (7902453755789701/100000000000000 : ℝ)*(sp0) + (7902509389261451/100000000000000 : ℝ)*(sp1) + (3951254585783837/50000000000000 : ℝ)*(sp2) + (494287126915759/12500000000000 : ℝ)*(sp3) + (57162881881/100000000000000 : ℝ)*(sp4) + (8367576979/50000000000000 : ℝ)*(sp7) + (395431375048003/10000000000000 : ℝ)*(f.failure) + (7902510918671581/100000000000000 : ℝ)*(f.sum) + (1488063243979/420625000000000000000000000 : ℝ)*base66 + (5501865925798019/4206250000000000000000000000000 : ℝ)*base67 + (15412011501548019/4206250000000000000000000000000 : ℝ)*base69 + (16922414158241769/4206250000000000000000000000000 : ℝ)*base71 + (3375794939897/3365000000000000000000000000 : ℝ)*base74 + (29016623572539481/4206250000000000000000000000000 : ℝ)*base76 + (50418682822308231/4206250000000000000000000000000 : ℝ)*base78 + (70399114112079269/4206250000000000000000000000000 : ℝ)*base79 + (263258025411/420625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (295001/125000000000000000000 : ℝ)*base90 + (295001/125000000000000000000 : ℝ)*base92 + (295001/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45164962890026531294718519/4206250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34086441/50000000000000 : ℝ)*(base19) + (64505121/10000000000000 : ℝ)*(base23) + (57644251/25000000000000 : ℝ)*(upper3) + (27920909/10000000000000 : ℝ)*(lower4) + (42096437/100000000000000 : ℝ)*(upper5) + (5958372550383557/100000000000000 : ℝ)*(major0) + (5958372550383557/100000000000000 : ℝ)*(major1) + (5958372550383557/100000000000000 : ℝ)*(major2) + (3287095061/100000000000000 : ℝ)*(sp1) + (7890244013/25000000000000 : ℝ)*(sp2) + (39712236670813/500000000000 : ℝ)*(sp4) + (7942443978894657/100000000000000 : ℝ)*(sp5) + (7942415128135337/100000000000000 : ℝ)*(sp6) + (124196794021407/3125000000000 : ℝ)*(sp7) + (124196794021407/3125000000000 : ℝ)*(f.failure) + (39712236670813/500000000000 : ℝ)*(f.sum) + (3743274734761/3365000000000000000000000000 : ℝ)*base66 + (143324494034298359/8412500000000000000000000000000 : ℝ)*base67 + (235492619666798359/8412500000000000000000000000000 : ℝ)*base69 + (55369353213748359/8412500000000000000000000000000 : ℝ)*base71 + (26519092779989/3365000000000000000000000000 : ℝ)*base73 + (116143062523773359/8412500000000000000000000000000 : ℝ)*base75 + (171119521012573359/8412500000000000000000000000000 : ℝ)*base77 + (217289106935848359/8412500000000000000000000000000 : ℝ)*base79 + (17445766838509/3365000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (322297/19531250000000000000 : ℝ)*base90 + (322297/19531250000000000000 : ℝ)*base92 + (322297/19531250000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1165_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5691/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1165_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1165_s8_0 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-538984741/2500000000 : ℝ)*x 0 + (5392577623/10000000000 : ℝ)*x 1 + (5266140381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538984741/2500000000 : ℝ)^4179 ≤ (6551318714129/50000000000000 : ℝ)^3155 := by
    have hnat : (538984741 : ℕ)^4179*50000000000000^3155 ≤ 6551318714129^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538984741 2500000000 6551318714129 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392577623/10000000000 : ℝ)^4179 ≤ (44131341003181/100000000000000 : ℝ)^3155 := by
    have hnat : (5392577623 : ℕ)^4179*100000000000000^3155 ≤ 44131341003181^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392577623 10000000000 44131341003181 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266140381/10000000000 : ℝ)^4179 ≤ (42766021558471/100000000000000 : ℝ)^3155 := by
    have hnat : (5266140381 : ℕ)^4179*100000000000000^3155 ≤ 42766021558471^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266140381 10000000000 42766021558471 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-538984741/2500000000 : ℝ), (5392577623/10000000000 : ℝ), (5266140381/10000000000 : ℝ)] ![(6551318714129/50000000000000 : ℝ), (44131341003181/100000000000000 : ℝ), (42766021558471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-538984741/2500000000 : ℝ)|^4179 ≤ (6551318714129/50000000000000 : ℝ)^3155
        have hw : |(-538984741/2500000000 : ℝ)|=(538984741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392577623/10000000000 : ℝ)|^4179 ≤ (44131341003181/100000000000000 : ℝ)^3155
        have hw : |(5392577623/10000000000 : ℝ)|=(5392577623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266140381/10000000000 : ℝ)|^4179 ≤ (42766021558471/100000000000000 : ℝ)^3155
        have hw : |(5266140381/10000000000 : ℝ)|=(5266140381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s8_1 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344659029/10000000000 : ℝ)*x 0 + (-1110031857/5000000000 : ℝ)*x 1 + (5266140541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344659029/10000000000 : ℝ)^4179 ≤ (4361266063477/10000000000000 : ℝ)^3155 := by
    have hnat : (5344659029 : ℕ)^4179*10000000000000^3155 ≤ 4361266063477^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344659029 10000000000 4361266063477 10000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1110031857/5000000000 : ℝ)^4179 ≤ (6810658036597/50000000000000 : ℝ)^3155 := by
    have hnat : (1110031857 : ℕ)^4179*50000000000000^3155 ≤ 6810658036597^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110031857 5000000000 6810658036597 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266140541/10000000000 : ℝ)^4179 ≤ (5345752909943/12500000000000 : ℝ)^3155 := by
    have hnat : (5266140541 : ℕ)^4179*12500000000000^3155 ≤ 5345752909943^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266140541 10000000000 5345752909943 12500000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344659029/10000000000 : ℝ), (-1110031857/5000000000 : ℝ), (5266140541/10000000000 : ℝ)] ![(4361266063477/10000000000000 : ℝ), (6810658036597/50000000000000 : ℝ), (5345752909943/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344659029/10000000000 : ℝ)|^4179 ≤ (4361266063477/10000000000000 : ℝ)^3155
        have hw : |(5344659029/10000000000 : ℝ)|=(5344659029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1110031857/5000000000 : ℝ)|^4179 ≤ (6810658036597/50000000000000 : ℝ)^3155
        have hw : |(-1110031857/5000000000 : ℝ)|=(1110031857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266140541/10000000000 : ℝ)|^4179 ≤ (5345752909943/12500000000000 : ℝ)^3155
        have hw : |(5266140541/10000000000 : ℝ)|=(5266140541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s8_2 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336164783/2500000000 : ℝ)*x 0 + (5266140441/10000000000 : ℝ)*x 1 + (-2220063709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336164783/2500000000 : ℝ)^4179 ≤ (21806330874023/50000000000000 : ℝ)^3155 := by
    have hnat : (1336164783 : ℕ)^4179*50000000000000^3155 ≤ 21806330874023^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336164783 2500000000 21806330874023 50000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266140441/10000000000 : ℝ)^4179 ≤ (42766022203873/100000000000000 : ℝ)^3155 := by
    have hnat : (5266140441 : ℕ)^4179*100000000000000^3155 ≤ 42766022203873^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266140441 10000000000 42766022203873 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2220063709/10000000000 : ℝ)^4179 ≤ (170266450407/1250000000000 : ℝ)^3155 := by
    have hnat : (2220063709 : ℕ)^4179*1250000000000^3155 ≤ 170266450407^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220063709 10000000000 170266450407 1250000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336164783/2500000000 : ℝ), (5266140441/10000000000 : ℝ), (-2220063709/10000000000 : ℝ)] ![(21806330874023/50000000000000 : ℝ), (42766022203873/100000000000000 : ℝ), (170266450407/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336164783/2500000000 : ℝ)|^4179 ≤ (21806330874023/50000000000000 : ℝ)^3155
        have hw : |(1336164783/2500000000 : ℝ)|=(1336164783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266140441/10000000000 : ℝ)|^4179 ≤ (42766022203873/100000000000000 : ℝ)^3155
        have hw : |(5266140441/10000000000 : ℝ)|=(5266140441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2220063709/10000000000 : ℝ)|^4179 ≤ (170266450407/1250000000000 : ℝ)^3155
        have hw : |(-2220063709/10000000000 : ℝ)|=(2220063709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s8_3 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (545180631/1250000000 : ℝ)*x 0 + (1059229161/2500000000 : ℝ)*x 1 + (2244797639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545180631/1250000000 : ℝ)^4179 ≤ (33317111439103/100000000000000 : ℝ)^3155 := by
    have hnat : (545180631 : ℕ)^4179*100000000000000^3155 ≤ 33317111439103^3155*1250000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545180631 1250000000 33317111439103 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059229161/2500000000 : ℝ)^4179 ≤ (6412593008491/20000000000000 : ℝ)^3155 := by
    have hnat : (1059229161 : ℕ)^4179*20000000000000^3155 ≤ 6412593008491^3155*2500000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059229161 2500000000 6412593008491 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244797639/5000000000 : ℝ)^4179 ≤ (540936304701/1562500000000 : ℝ)^3155 := by
    have hnat : (2244797639 : ℕ)^4179*1562500000000^3155 ≤ 540936304701^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244797639 5000000000 540936304701 1562500000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545180631/1250000000 : ℝ), (1059229161/2500000000 : ℝ), (2244797639/5000000000 : ℝ)] ![(33317111439103/100000000000000 : ℝ), (6412593008491/20000000000000 : ℝ), (540936304701/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545180631/1250000000 : ℝ)|^4179 ≤ (33317111439103/100000000000000 : ℝ)^3155
        have hw : |(545180631/1250000000 : ℝ)|=(545180631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059229161/2500000000 : ℝ)|^4179 ≤ (6412593008491/20000000000000 : ℝ)^3155
        have hw : |(1059229161/2500000000 : ℝ)|=(1059229161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2244797639/5000000000 : ℝ)|^4179 ≤ (540936304701/1562500000000 : ℝ)^3155
        have hw : |(2244797639/5000000000 : ℝ)|=(2244797639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s8_4 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1077971873/5000000000 : ℝ)*x 0 + (1053291641/2000000000 : ℝ)*x 1 + (5392258679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077971873/5000000000 : ℝ)^4179 ≤ (13102675923317/100000000000000 : ℝ)^3155 := by
    have hnat : (1077971873 : ℕ)^4179*100000000000000^3155 ≤ 13102675923317^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077971873 5000000000 13102675923317 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053291641/2000000000 : ℝ)^4179 ≤ (10692360083071/25000000000000 : ℝ)^3155 := by
    have hnat : (1053291641 : ℕ)^4179*25000000000000^3155 ≤ 10692360083071^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053291641 2000000000 10692360083071 25000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392258679/10000000000 : ℝ)^4179 ≤ (44127883727631/100000000000000 : ℝ)^3155 := by
    have hnat : (5392258679 : ℕ)^4179*100000000000000^3155 ≤ 44127883727631^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392258679 10000000000 44127883727631 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1077971873/5000000000 : ℝ), (1053291641/2000000000 : ℝ), (5392258679/10000000000 : ℝ)] ![(13102675923317/100000000000000 : ℝ), (10692360083071/25000000000000 : ℝ), (44127883727631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1077971873/5000000000 : ℝ)|^4179 ≤ (13102675923317/100000000000000 : ℝ)^3155
        have hw : |(-1077971873/5000000000 : ℝ)|=(1077971873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053291641/2000000000 : ℝ)|^4179 ≤ (10692360083071/25000000000000 : ℝ)^3155
        have hw : |(1053291641/2000000000 : ℝ)|=(1053291641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392258679/10000000000 : ℝ)|^4179 ≤ (44127883727631/100000000000000 : ℝ)^3155
        have hw : |(5392258679/10000000000 : ℝ)|=(5392258679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s8_5 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062514309/2000000000 : ℝ)*x 0 + (-2093945527/10000000000 : ℝ)*x 1 + (5392258679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062514309/2000000000 : ℝ)^4179 ≤ (8653236258899/20000000000000 : ℝ)^3155 := by
    have hnat : (1062514309 : ℕ)^4179*20000000000000^3155 ≤ 8653236258899^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062514309 2000000000 8653236258899 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2093945527/10000000000 : ℝ)^4179 ≤ (12605934962041/100000000000000 : ℝ)^3155 := by
    have hnat : (2093945527 : ℕ)^4179*100000000000000^3155 ≤ 12605934962041^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093945527 10000000000 12605934962041 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392258679/10000000000 : ℝ)^4179 ≤ (44127883727631/100000000000000 : ℝ)^3155 := by
    have hnat : (5392258679 : ℕ)^4179*100000000000000^3155 ≤ 44127883727631^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392258679 10000000000 44127883727631 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062514309/2000000000 : ℝ), (-2093945527/10000000000 : ℝ), (5392258679/10000000000 : ℝ)] ![(8653236258899/20000000000000 : ℝ), (12605934962041/100000000000000 : ℝ), (44127883727631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062514309/2000000000 : ℝ)|^4179 ≤ (8653236258899/20000000000000 : ℝ)^3155
        have hw : |(1062514309/2000000000 : ℝ)|=(1062514309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2093945527/10000000000 : ℝ)|^4179 ≤ (12605934962041/100000000000000 : ℝ)^3155
        have hw : |(-2093945527/10000000000 : ℝ)|=(2093945527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392258679/10000000000 : ℝ)|^4179 ≤ (44127883727631/100000000000000 : ℝ)^3155
        have hw : |(5392258679/10000000000 : ℝ)|=(5392258679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s8_6 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656285773/5000000000 : ℝ)*x 0 + (5392258679/10000000000 : ℝ)*x 1 + (-1046972763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656285773/5000000000 : ℝ)^4179 ≤ (43266181305283/100000000000000 : ℝ)^3155 := by
    have hnat : (2656285773 : ℕ)^4179*100000000000000^3155 ≤ 43266181305283^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656285773 5000000000 43266181305283 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392258679/10000000000 : ℝ)^4179 ≤ (44127883727631/100000000000000 : ℝ)^3155 := by
    have hnat : (5392258679 : ℕ)^4179*100000000000000^3155 ≤ 44127883727631^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392258679 10000000000 44127883727631 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046972763/5000000000 : ℝ)^4179 ≤ (12605934954067/100000000000000 : ℝ)^3155 := by
    have hnat : (1046972763 : ℕ)^4179*100000000000000^3155 ≤ 12605934954067^3155*5000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046972763 5000000000 12605934954067 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656285773/5000000000 : ℝ), (5392258679/10000000000 : ℝ), (-1046972763/5000000000 : ℝ)] ![(43266181305283/100000000000000 : ℝ), (44127883727631/100000000000000 : ℝ), (12605934954067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656285773/5000000000 : ℝ)|^4179 ≤ (43266181305283/100000000000000 : ℝ)^3155
        have hw : |(2656285773/5000000000 : ℝ)|=(2656285773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392258679/10000000000 : ℝ)|^4179 ≤ (44127883727631/100000000000000 : ℝ)^3155
        have hw : |(5392258679/10000000000 : ℝ)|=(5392258679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1046972763/5000000000 : ℝ)|^4179 ≤ (12605934954067/100000000000000 : ℝ)^3155
        have hw : |(-1046972763/5000000000 : ℝ)|=(1046972763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1165_s8_7 (p : ℝ) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4361454541/10000000000 : ℝ)*x 0 + (897792073/2000000000 : ℝ)*x 1 + (847510799/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361454541/10000000000 : ℝ)^4179 ≤ (2082325468293/6250000000000 : ℝ)^3155 := by
    have hnat : (4361454541 : ℕ)^4179*6250000000000^3155 ≤ 2082325468293^3155*10000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361454541 10000000000 2082325468293 6250000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897792073/2000000000 : ℝ)^4179 ≤ (34613438707067/100000000000000 : ℝ)^3155 := by
    have hnat : (897792073 : ℕ)^4179*100000000000000^3155 ≤ 34613438707067^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897792073 2000000000 34613438707067 100000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847510799/2000000000 : ℝ)^4179 ≤ (6413870758927/20000000000000 : ℝ)^3155 := by
    have hnat : (847510799 : ℕ)^4179*20000000000000^3155 ≤ 6413870758927^3155*2000000000^4179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847510799 2000000000 6413870758927 20000000000000 4179 3155 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4179/1024 : ℝ)) 4179 3155 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361454541/10000000000 : ℝ), (897792073/2000000000 : ℝ), (847510799/2000000000 : ℝ)] ![(2082325468293/6250000000000 : ℝ), (34613438707067/100000000000000 : ℝ), (6413870758927/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361454541/10000000000 : ℝ)|^4179 ≤ (2082325468293/6250000000000 : ℝ)^3155
        have hw : |(4361454541/10000000000 : ℝ)|=(4361454541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(897792073/2000000000 : ℝ)|^4179 ≤ (34613438707067/100000000000000 : ℝ)^3155
        have hw : |(897792073/2000000000 : ℝ)|=(897792073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(847510799/2000000000 : ℝ)|^4179 ≤ (6413870758927/20000000000000 : ℝ)^3155
        have hw : |(847510799/2000000000 : ℝ)|=(847510799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1165_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5691/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11383/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7031/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14063/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5691/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14063/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5691/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14063/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5691/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14063/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5691/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14063/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5691/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14063/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5691/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5691/50000 : ℝ) ^ (8357/2048 : ℝ) ≤ (14087607655925547/100000000000000000000 : ℝ) := by
    have hpowers : (5691/50000 : ℝ)^8357 ≤ (14087607655925547/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5691 : ℕ)^8357*100000000000000000000^2048 ≤ 14087607655925547^2048*50000^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5691 50000 14087607655925547 100000000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5691/50000 : ℝ)) (X := (14087607655925547/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14063/100000 : ℝ) ^ (8357/2048 : ℝ) ≤ (1669727560055039/5000000000000000000 : ℝ) := by
    have hpowers : (14063/100000 : ℝ)^8357 ≤ (1669727560055039/5000000000000000000 : ℝ)^2048 := by
      have hnat : (14063 : ℕ)^8357*5000000000000000000^2048 ≤ 1669727560055039^2048*100000^8357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14063 100000 1669727560055039 5000000000000000000 8357 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14063/100000 : ℝ)) (X := (1669727560055039/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014087607655925547/50000000000000000000 : ℝ) ≤ (1250086299965797/1250000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (50014087607655925547/50000000000000000000 : ℝ)^2048 ≤ (1250086299965797/1250000000000000 : ℝ)^8357 := by
      have hnat : (50014087607655925547 : ℕ)^2048*1250000000000000^8357 ≤ 1250086299965797^8357*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014087607655925547 50000000000000000000 1250086299965797 1250000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250086299965797/1250000000000000 : ℝ)) (X := (50014087607655925547/50000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047482158857026327/100000000000000000000 : ℝ) ≤ (2500290852091773/2500000000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (100047482158857026327/100000000000000000000 : ℝ)^2048 ≤ (2500290852091773/2500000000000000 : ℝ)^8357 := by
      have hnat : (100047482158857026327 : ℕ)^2048*2500000000000000^8357 ≤ 2500290852091773^8357*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047482158857026327 100000000000000000000 2500290852091773 2500000000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500290852091773/2500000000000000 : ℝ)) (X := (100047482158857026327/100000000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501669727560055039/2500000000000000000 : ℝ) ≤ (156275569015747/156250000000000 : ℝ) ^ (8357/2048 : ℝ) := by
    have hpowers : (2501669727560055039/2500000000000000000 : ℝ)^2048 ≤ (156275569015747/156250000000000 : ℝ)^8357 := by
      have hnat : (2501669727560055039 : ℕ)^2048*156250000000000^8357 ≤ 156275569015747^8357*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501669727560055039 2500000000000000000 156275569015747 156250000000000 2048 8357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156275569015747/156250000000000 : ℝ)) (X := (2501669727560055039/2500000000000000000 : ℝ)) (by norm_num) 8357 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14087607655925547/100000000000000000000 : ℝ) ≤ ((478590774874449197/478750000000000000 : ℝ)+2*(118252160179/67025000000000 : ℝ)*(5691/50000 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (478590774874449197/478750000000000000 : ℝ)+2*(118252160179/67025000000000 : ℝ)*(5691/50000 : ℝ)=(1250086299965797/1250000000000000 : ℝ) by norm_num, show 1+2*(14087607655925547/100000000000000000000 : ℝ)=(50014087607655925547/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1669727560055039/5000000000000000000 : ℝ)+(14087607655925547/100000000000000000000 : ℝ) ≤ ((478590774874449197/478750000000000000 : ℝ)+(118252160179/67025000000000 : ℝ)*((14063/100000 : ℝ)+(5691/50000 : ℝ)))^(8357/2048 : ℝ) := by
    rw [show (478590774874449197/478750000000000000 : ℝ)+(118252160179/67025000000000 : ℝ)*((14063/100000 : ℝ)+(5691/50000 : ℝ))=(2500290852091773/2500000000000000 : ℝ) by norm_num, show 1+(1669727560055039/5000000000000000000 : ℝ)+(14087607655925547/100000000000000000000 : ℝ)=(100047482158857026327/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1669727560055039/5000000000000000000 : ℝ) ≤ ((478590774874449197/478750000000000000 : ℝ)+2*(118252160179/67025000000000 : ℝ)*(14063/100000 : ℝ))^(8357/2048 : ℝ) := by
    rw [show (478590774874449197/478750000000000000 : ℝ)+2*(118252160179/67025000000000 : ℝ)*(14063/100000 : ℝ)=(156275569015747/156250000000000 : ℝ) by norm_num, show 1+2*(1669727560055039/5000000000000000000 : ℝ)=(2501669727560055039/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (478590774874449197/478750000000000000 : ℝ)*(X 1 0+X 2 0)+(118252160179/67025000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (5691/50000 : ℝ)) (hi := (14063/100000 : ℝ)) (c := (478590774874449197/478750000000000000 : ℝ)) (alpha := (118252160179/67025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (478590774874449197/478750000000000000 : ℝ)*(X 0 1+X 2 1)+(118252160179/67025000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (5691/50000 : ℝ)) (hi := (14063/100000 : ℝ)) (c := (478590774874449197/478750000000000000 : ℝ)) (alpha := (118252160179/67025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (478590774874449197/478750000000000000 : ℝ)*(X 0 2+X 1 2)+(118252160179/67025000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8357/2048 : ℝ)) (lo := (5691/50000 : ℝ)) (hi := (14063/100000 : ℝ)) (c := (478590774874449197/478750000000000000 : ℝ)) (alpha := (118252160179/67025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-538984741/2500000000 : ℝ)*X 0 0+(5392577623/10000000000 : ℝ)*X 0 1+(5266140381/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344659029/10000000000 : ℝ)*X 1 0+(-1110031857/5000000000 : ℝ)*X 1 1+(5266140541/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336164783/2500000000 : ℝ)*X 2 0+(5266140441/10000000000 : ℝ)*X 2 1+(-2220063709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((545180631/1250000000 : ℝ)*X 0 0+(1059229161/2500000000 : ℝ)*X 0 1+(2244797639/5000000000 : ℝ)*X 0 2+(545180631/1250000000 : ℝ)*X 1 0+(1059229161/2500000000 : ℝ)*X 1 1+(2244797639/5000000000 : ℝ)*X 1 2+(545180631/1250000000 : ℝ)*X 2 0+(1059229161/2500000000 : ℝ)*X 2 1+(2244797639/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1077971873/5000000000 : ℝ)*X 0 0+(1053291641/2000000000 : ℝ)*X 0 1+(5392258679/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062514309/2000000000 : ℝ)*X 1 0+(-2093945527/10000000000 : ℝ)*X 1 1+(5392258679/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656285773/5000000000 : ℝ)*X 2 0+(5392258679/10000000000 : ℝ)*X 2 1+(-1046972763/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4361454541/10000000000 : ℝ)*X 0 0+(897792073/2000000000 : ℝ)*X 0 1+(847510799/2000000000 : ℝ)*X 0 2+(4361454541/10000000000 : ℝ)*X 1 0+(897792073/2000000000 : ℝ)*X 1 1+(847510799/2000000000 : ℝ)*X 1 2+(4361454541/10000000000 : ℝ)*X 2 0+(897792073/2000000000 : ℝ)*X 2 1+(847510799/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1165_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (870573971708756220685528083/83781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2193919933/100000000000000 : ℝ)*(base19) + (107966663/5000000000000 : ℝ)*(base23) + (2498753/2500000000000 : ℝ)*(lower2) + (61201167/20000000000000 : ℝ)*(upper3) + (509559/250000000000 : ℝ)*(upper5) + (2966714755410309/50000000000000 : ℝ)*(major0) + (2966714755410309/50000000000000 : ℝ)*(major1) + (2966714755410309/50000000000000 : ℝ)*(major2) + (7909130417810711/100000000000000 : ℝ)*(sp0) + (3954598171721757/50000000000000 : ℝ)*(sp1) + (7909196378030187/100000000000000 : ℝ)*(sp2) + (1978813065803791/50000000000000 : ℝ)*(sp3) + (2128736023/3125000000000 : ℝ)*(sp4) + (34006302333/100000000000000 : ℝ)*(sp7) + (1978830068954957/50000000000000 : ℝ)*(f.failure) + (7909198537363447/100000000000000 : ℝ)*(f.sum) + (44434577674257/13405000000000000000000000000 : ℝ)*base66 + (100794957560428111/167562500000000000000000000000000 : ℝ)*base67 + (1701865805813321889/167562500000000000000000000000000 : ℝ)*base70 + (3079682180497634389/167562500000000000000000000000000 : ℝ)*base72 + (40403824578097/13405000000000000000000000000 : ℝ)*base74 + (279810529623259389/167562500000000000000000000000000 : ℝ)*base76 + (3258912020173759389/167562500000000000000000000000000 : ℝ)*base78 + (2873322013013303111/167562500000000000000000000000000 : ℝ)*base79 + (4789957304137/3351250000000000000000000000 : ℝ)*base81 + (6319319/625000000000000000000 : ℝ)*base90 + (6319319/625000000000000000000 : ℝ)*base92 + (6319319/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4157770090307555666061/478750000000000000000000000 : ℝ) := by norm_num
    linear_combination (78955049/5000000000000 : ℝ)*(base19) + (429628119/25000000000000 : ℝ)*(base23) + (138245027/25000000000000 : ℝ)*(lower1) + (174628769/100000000000000 : ℝ)*(upper3) + (62515969/100000000000000 : ℝ)*(lower4) + (35527243/20000000000000 : ℝ)*(upper5) + (2981662955586273/50000000000000 : ℝ)*(major0) + (2981662955586273/50000000000000 : ℝ)*(major1) + (2981662955586273/50000000000000 : ℝ)*(major2) + (335098529/10000000000000 : ℝ)*(sp2) + (3974525090110369/50000000000000 : ℝ)*(sp4) + (3974524300559879/50000000000000 : ℝ)*(sp5) + (1987261277680743/25000000000000 : ℝ)*(sp6) + (1988800676318207/50000000000000 : ℝ)*(sp7) + (1988800676318207/50000000000000 : ℝ)*(f.failure) + (3974525090110369/50000000000000 : ℝ)*(f.sum) + (3050372115529/957500000000000000000000000 : ℝ)*base65 + (51250636161877219/23937500000000000000000000000000 : ℝ)*base68 + (233666112709622781/23937500000000000000000000000000 : ℝ)*base69 + (5134386105902372781/23937500000000000000000000000000 : ℝ)*base71 + (2819306085353/478750000000000000000000000 : ℝ)*base74 + (1336097557549127219/23937500000000000000000000000000 : ℝ)*base76 + (142488239460502219/23937500000000000000000000000000 : ℝ)*base78 + (182246951450372781/23937500000000000000000000000000 : ℝ)*base79 + (1437229378759/239375000000000000000000000 : ℝ)*base82 + (642931/625000000000000000000 : ℝ)*base89 + (642931/625000000000000000000 : ℝ)*base91 + (642931/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1165_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14063/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5691/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1165_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1165_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1165_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1165_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1165_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8357/2048 : ℝ) ≤ p) (hpb : p ≤ (4179/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18740333/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1165_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
