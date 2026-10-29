-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1488_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:14:56.677867+00:00
-- url     : https://prove2.me/submissions/b1c5f65e-f880-4bf2-85c8-000284fdb3a2

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
theorem support_rectangle_w1488_s0_0 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-342317453/2000000000 : ℝ)*x 0 + (5931547983/10000000000 : ℝ)*x 1 + (4844918521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (342317453/2000000000 : ℝ)^4473 ≤ (10134376245741/100000000000000 : ℝ)^3449 := by
    have hnat : (342317453 : ℕ)^4473*100000000000000^3449 ≤ 10134376245741^3449*2000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342317453 2000000000 10134376245741 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5931547983/10000000000 : ℝ)^4473 ≤ (1587348170551/3125000000000 : ℝ)^3449 := by
    have hnat : (5931547983 : ℕ)^4473*3125000000000^3449 ≤ 1587348170551^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5931547983 10000000000 1587348170551 3125000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4844918521/10000000000 : ℝ)^4473 ≤ (39070482276723/100000000000000 : ℝ)^3449 := by
    have hnat : (4844918521 : ℕ)^4473*100000000000000^3449 ≤ 39070482276723^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4844918521 10000000000 39070482276723 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-342317453/2000000000 : ℝ), (5931547983/10000000000 : ℝ), (4844918521/10000000000 : ℝ)] ![(10134376245741/100000000000000 : ℝ), (1587348170551/3125000000000 : ℝ), (39070482276723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-342317453/2000000000 : ℝ)|^4473 ≤ (10134376245741/100000000000000 : ℝ)^3449
        have hw : |(-342317453/2000000000 : ℝ)|=(342317453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5931547983/10000000000 : ℝ)|^4473 ≤ (1587348170551/3125000000000 : ℝ)^3449
        have hw : |(5931547983/10000000000 : ℝ)|=(5931547983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4844918521/10000000000 : ℝ)|^4473 ≤ (39070482276723/100000000000000 : ℝ)^3449
        have hw : |(4844918521/10000000000 : ℝ)|=(4844918521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s0_1 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5483221093/10000000000 : ℝ)*x 0 + (-2322575419/10000000000 : ℝ)*x 1 + (1211229631/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5483221093/10000000000 : ℝ)^4473 ≤ (45872888465657/100000000000000 : ℝ)^3449 := by
    have hnat : (5483221093 : ℕ)^4473*100000000000000^3449 ≤ 45872888465657^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483221093 10000000000 45872888465657 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2322575419/10000000000 : ℝ)^4473 ≤ (7528314606773/50000000000000 : ℝ)^3449 := by
    have hnat : (2322575419 : ℕ)^4473*50000000000000^3449 ≤ 7528314606773^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2322575419 10000000000 7528314606773 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1211229631/2500000000 : ℝ)^4473 ≤ (19535241154049/50000000000000 : ℝ)^3449 := by
    have hnat : (1211229631 : ℕ)^4473*50000000000000^3449 ≤ 19535241154049^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1211229631 2500000000 19535241154049 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5483221093/10000000000 : ℝ), (-2322575419/10000000000 : ℝ), (1211229631/2500000000 : ℝ)] ![(45872888465657/100000000000000 : ℝ), (7528314606773/50000000000000 : ℝ), (19535241154049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5483221093/10000000000 : ℝ)|^4473 ≤ (45872888465657/100000000000000 : ℝ)^3449
        have hw : |(5483221093/10000000000 : ℝ)|=(5483221093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2322575419/10000000000 : ℝ)|^4473 ≤ (7528314606773/50000000000000 : ℝ)^3449
        have hw : |(-2322575419/10000000000 : ℝ)|=(2322575419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1211229631/2500000000 : ℝ)|^4473 ≤ (19535241154049/50000000000000 : ℝ)^3449
        have hw : |(1211229631/2500000000 : ℝ)|=(1211229631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s0_2 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5483221081/10000000000 : ℝ)*x 0 + (4844918553/10000000000 : ℝ)*x 1 + (-1161287699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5483221081/10000000000 : ℝ)^4473 ≤ (22936444167729/50000000000000 : ℝ)^3449 := by
    have hnat : (5483221081 : ℕ)^4473*50000000000000^3449 ≤ 22936444167729^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483221081 10000000000 22936444167729 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4844918553/10000000000 : ℝ)^4473 ≤ (19535241305697/50000000000000 : ℝ)^3449 := by
    have hnat : (4844918553 : ℕ)^4473*50000000000000^3449 ≤ 19535241305697^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4844918553 10000000000 19535241305697 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1161287699/5000000000 : ℝ)^4473 ≤ (1505662903699/10000000000000 : ℝ)^3449 := by
    have hnat : (1161287699 : ℕ)^4473*10000000000000^3449 ≤ 1505662903699^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1161287699 5000000000 1505662903699 10000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5483221081/10000000000 : ℝ), (4844918553/10000000000 : ℝ), (-1161287699/5000000000 : ℝ)] ![(22936444167729/50000000000000 : ℝ), (19535241305697/50000000000000 : ℝ), (1505662903699/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5483221081/10000000000 : ℝ)|^4473 ≤ (22936444167729/50000000000000 : ℝ)^3449
        have hw : |(5483221081/10000000000 : ℝ)|=(5483221081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4844918553/10000000000 : ℝ)|^4473 ≤ (19535241305697/50000000000000 : ℝ)^3449
        have hw : |(4844918553/10000000000 : ℝ)|=(4844918553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1161287699/5000000000 : ℝ)|^4473 ≤ (1505662903699/10000000000000 : ℝ)^3449
        have hw : |(-1161287699/5000000000 : ℝ)|=(1161287699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s0_3 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (166067171/400000000 : ℝ)*x 0 + (96604281/312500000 : ℝ)*x 1 + (5513749001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166067171/400000000 : ℝ)^4473 ≤ (31979770130871/100000000000000 : ℝ)^3449 := by
    have hnat : (166067171 : ℕ)^4473*100000000000000^3449 ≤ 31979770130871^3449*400000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166067171 400000000 31979770130871 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96604281/312500000 : ℝ)^4473 ≤ (5453960753731/25000000000000 : ℝ)^3449 := by
    have hnat : (96604281 : ℕ)^4473*25000000000000^3449 ≤ 5453960753731^3449*312500000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96604281 312500000 5453960753731 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5513749001/10000000000 : ℝ)^4473 ≤ (5775548354971/12500000000000 : ℝ)^3449 := by
    have hnat : (5513749001 : ℕ)^4473*12500000000000^3449 ≤ 5775548354971^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513749001 10000000000 5775548354971 12500000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166067171/400000000 : ℝ), (96604281/312500000 : ℝ), (5513749001/10000000000 : ℝ)] ![(31979770130871/100000000000000 : ℝ), (5453960753731/25000000000000 : ℝ), (5775548354971/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166067171/400000000 : ℝ)|^4473 ≤ (31979770130871/100000000000000 : ℝ)^3449
        have hw : |(166067171/400000000 : ℝ)|=(166067171/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(96604281/312500000 : ℝ)|^4473 ≤ (5453960753731/25000000000000 : ℝ)^3449
        have hw : |(96604281/312500000 : ℝ)|=(96604281/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5513749001/10000000000 : ℝ)|^4473 ≤ (5775548354971/12500000000000 : ℝ)^3449
        have hw : |(5513749001/10000000000 : ℝ)|=(5513749001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s0_4 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-107207383/625000000 : ℝ)*x 0 + (4872757187/10000000000 : ℝ)*x 1 + (5902708969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107207383/625000000 : ℝ)^4473 ≤ (10163034743341/100000000000000 : ℝ)^3449 := by
    have hnat : (107207383 : ℕ)^4473*100000000000000^3449 ≤ 10163034743341^3449*625000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107207383 625000000 10163034743341 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4872757187/10000000000 : ℝ)^4473 ≤ (19680940018001/50000000000000 : ℝ)^3449 := by
    have hnat : (4872757187 : ℕ)^4473*50000000000000^3449 ≤ 19680940018001^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4872757187 10000000000 19680940018001 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5902708969/10000000000 : ℝ)^4473 ≤ (10095017041481/20000000000000 : ℝ)^3449 := by
    have hnat : (5902708969 : ℕ)^4473*20000000000000^3449 ≤ 10095017041481^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5902708969 10000000000 10095017041481 20000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107207383/625000000 : ℝ), (4872757187/10000000000 : ℝ), (5902708969/10000000000 : ℝ)] ![(10163034743341/100000000000000 : ℝ), (19680940018001/50000000000000 : ℝ), (10095017041481/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107207383/625000000 : ℝ)|^4473 ≤ (10163034743341/100000000000000 : ℝ)^3449
        have hw : |(-107207383/625000000 : ℝ)|=(107207383/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4872757187/10000000000 : ℝ)|^4473 ≤ (19680940018001/50000000000000 : ℝ)^3449
        have hw : |(4872757187/10000000000 : ℝ)|=(4872757187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5902708969/10000000000 : ℝ)|^4473 ≤ (10095017041481/20000000000000 : ℝ)^3449
        have hw : |(5902708969/10000000000 : ℝ)|=(5902708969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s0_5 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (51864707/100000000 : ℝ)*x 0 + (-1264784871/10000000000 : ℝ)*x 1 + (5902709021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51864707/100000000 : ℝ)^4473 ≤ (42679377269403/100000000000000 : ℝ)^3449 := by
    have hnat : (51864707 : ℕ)^4473*100000000000000^3449 ≤ 42679377269403^3449*100000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51864707 100000000 42679377269403 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1264784871/10000000000 : ℝ)^4473 ≤ (6845536933397/100000000000000 : ℝ)^3449 := by
    have hnat : (1264784871 : ℕ)^4473*100000000000000^3449 ≤ 6845536933397^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1264784871 10000000000 6845536933397 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5902709021/10000000000 : ℝ)^4473 ≤ (10095017156817/20000000000000 : ℝ)^3449 := by
    have hnat : (5902709021 : ℕ)^4473*20000000000000^3449 ≤ 10095017156817^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5902709021 10000000000 10095017156817 20000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(51864707/100000000 : ℝ), (-1264784871/10000000000 : ℝ), (5902709021/10000000000 : ℝ)] ![(42679377269403/100000000000000 : ℝ), (6845536933397/100000000000000 : ℝ), (10095017156817/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(51864707/100000000 : ℝ)|^4473 ≤ (42679377269403/100000000000000 : ℝ)^3449
        have hw : |(51864707/100000000 : ℝ)|=(51864707/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1264784871/10000000000 : ℝ)|^4473 ≤ (6845536933397/100000000000000 : ℝ)^3449
        have hw : |(-1264784871/10000000000 : ℝ)|=(1264784871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5902709021/10000000000 : ℝ)|^4473 ≤ (10095017156817/20000000000000 : ℝ)^3449
        have hw : |(5902709021/10000000000 : ℝ)|=(5902709021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s0_6 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2593235379/5000000000 : ℝ)*x 0 + (1180541779/2000000000 : ℝ)*x 1 + (-1264784981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2593235379/5000000000 : ℝ)^4473 ≤ (10669844472097/25000000000000 : ℝ)^3449 := by
    have hnat : (2593235379 : ℕ)^4473*25000000000000^3449 ≤ 10669844472097^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593235379 5000000000 10669844472097 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1180541779/2000000000 : ℝ)^4473 ≤ (25237542193373/50000000000000 : ℝ)^3449 := by
    have hnat : (1180541779 : ℕ)^4473*50000000000000^3449 ≤ 25237542193373^3449*2000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1180541779 2000000000 25237542193373 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1264784981/10000000000 : ℝ)^4473 ≤ (273821508221/4000000000000 : ℝ)^3449 := by
    have hnat : (1264784981 : ℕ)^4473*4000000000000^3449 ≤ 273821508221^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1264784981 10000000000 273821508221 4000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2593235379/5000000000 : ℝ), (1180541779/2000000000 : ℝ), (-1264784981/10000000000 : ℝ)] ![(10669844472097/25000000000000 : ℝ), (25237542193373/50000000000000 : ℝ), (273821508221/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2593235379/5000000000 : ℝ)|^4473 ≤ (10669844472097/25000000000000 : ℝ)^3449
        have hw : |(2593235379/5000000000 : ℝ)|=(2593235379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1180541779/2000000000 : ℝ)|^4473 ≤ (25237542193373/50000000000000 : ℝ)^3449
        have hw : |(1180541779/2000000000 : ℝ)|=(1180541779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1264784981/10000000000 : ℝ)|^4473 ≤ (273821508221/4000000000000 : ℝ)^3449
        have hw : |(-1264784981/10000000000 : ℝ)|=(1264784981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s0_7 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2079998399/5000000000 : ℝ)*x 0 + (1090337707/2000000000 : ℝ)*x 1 + (1577813791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079998399/5000000000 : ℝ)^4473 ≤ (16031442654227/50000000000000 : ℝ)^3449 := by
    have hnat : (2079998399 : ℕ)^4473*50000000000000^3449 ≤ 16031442654227^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079998399 5000000000 16031442654227 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090337707/2000000000 : ℝ)^4473 ≤ (45531055593693/100000000000000 : ℝ)^3449 := by
    have hnat : (1090337707 : ℕ)^4473*100000000000000^3449 ≤ 45531055593693^3449*2000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090337707 2000000000 45531055593693 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1577813791/5000000000 : ℝ)^4473 ≤ (22406059091419/100000000000000 : ℝ)^3449 := by
    have hnat : (1577813791 : ℕ)^4473*100000000000000^3449 ≤ 22406059091419^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577813791 5000000000 22406059091419 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2079998399/5000000000 : ℝ), (1090337707/2000000000 : ℝ), (1577813791/5000000000 : ℝ)] ![(16031442654227/50000000000000 : ℝ), (45531055593693/100000000000000 : ℝ), (22406059091419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2079998399/5000000000 : ℝ)|^4473 ≤ (16031442654227/50000000000000 : ℝ)^3449
        have hw : |(2079998399/5000000000 : ℝ)|=(2079998399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090337707/2000000000 : ℝ)|^4473 ≤ (45531055593693/100000000000000 : ℝ)^3449
        have hw : |(1090337707/2000000000 : ℝ)|=(1090337707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1577813791/5000000000 : ℝ)|^4473 ≤ (22406059091419/100000000000000 : ℝ)^3449
        have hw : |(1577813791/5000000000 : ℝ)|=(1577813791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1488_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2513/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25799/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4471/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4471 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4471*1^1024 ≤ 0^1024*1^4471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4471/1024 : ℝ) ≤ (1830248171589693427/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4471 ≤ (1830248171589693427/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4471*100000000000000000000^1024 ≤ 1830248171589693427^1024*5^4471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1830248171589693427 100000000000000000000 4471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1830248171589693427/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4471 := by
      have hnat : (1 : ℕ)^1024*1^4471 ≤ 1^4471*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101830248171589693427/100000000000000000000 : ℝ) ≤ (10041625862478441/10000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (101830248171589693427/100000000000000000000 : ℝ)^1024 ≤ (10041625862478441/10000000000000000 : ℝ)^4471 := by
      have hnat : (101830248171589693427 : ℕ)^1024*10000000000000000^4471 ≤ 10041625862478441^4471*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101830248171589693427 100000000000000000000 10041625862478441 10000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10041625862478441/10000000000000000 : ℝ)) (X := (101830248171589693427/100000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51830248171589693427/50000000000000000000 : ℝ) ≤ (5041625862478441/5000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (51830248171589693427/50000000000000000000 : ℝ)^1024 ≤ (5041625862478441/5000000000000000 : ℝ)^4471 := by
      have hnat : (51830248171589693427 : ℕ)^1024*5000000000000000^4471 ≤ 5041625862478441^4471*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51830248171589693427 50000000000000000000 5041625862478441 5000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5041625862478441/5000000000000000 : ℝ)) (X := (51830248171589693427/50000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(41625862478441/4000000000000000 : ℝ)*(0 : ℝ))^(4471/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(41625862478441/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1830248171589693427/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(41625862478441/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4471/1024 : ℝ) := by
    rw [show (1 : ℝ)+(41625862478441/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10041625862478441/10000000000000000 : ℝ) by norm_num, show 1+(1830248171589693427/100000000000000000000 : ℝ)+(0 : ℝ)=(101830248171589693427/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1830248171589693427/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(41625862478441/4000000000000000 : ℝ)*(2/5 : ℝ))^(4471/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(41625862478441/4000000000000000 : ℝ)*(2/5 : ℝ)=(5041625862478441/5000000000000000 : ℝ) by norm_num, show 1+2*(1830248171589693427/100000000000000000000 : ℝ)=(51830248171589693427/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(41625862478441/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (41625862478441/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(41625862478441/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (41625862478441/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(41625862478441/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (41625862478441/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-342317453/2000000000 : ℝ)*X 0 0+(5931547983/10000000000 : ℝ)*X 0 1+(4844918521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5483221093/10000000000 : ℝ)*X 1 0+(-2322575419/10000000000 : ℝ)*X 1 1+(1211229631/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5483221081/10000000000 : ℝ)*X 2 0+(4844918553/10000000000 : ℝ)*X 2 1+(-1161287699/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((166067171/400000000 : ℝ)*X 0 0+(96604281/312500000 : ℝ)*X 0 1+(5513749001/10000000000 : ℝ)*X 0 2+(166067171/400000000 : ℝ)*X 1 0+(96604281/312500000 : ℝ)*X 1 1+(5513749001/10000000000 : ℝ)*X 1 2+(166067171/400000000 : ℝ)*X 2 0+(96604281/312500000 : ℝ)*X 2 1+(5513749001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-107207383/625000000 : ℝ)*X 0 0+(4872757187/10000000000 : ℝ)*X 0 1+(5902708969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((51864707/100000000 : ℝ)*X 1 0+(-1264784871/10000000000 : ℝ)*X 1 1+(5902709021/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2593235379/5000000000 : ℝ)*X 2 0+(1180541779/2000000000 : ℝ)*X 2 1+(-1264784981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2079998399/5000000000 : ℝ)*X 0 0+(1090337707/2000000000 : ℝ)*X 0 1+(1577813791/5000000000 : ℝ)*X 0 2+(2079998399/5000000000 : ℝ)*X 1 0+(1090337707/2000000000 : ℝ)*X 1 1+(1577813791/5000000000 : ℝ)*X 1 2+(2079998399/5000000000 : ℝ)*X 2 0+(1090337707/2000000000 : ℝ)*X 2 1+(1577813791/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (485103915319970445885567/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48575867/100000000000000 : ℝ)*(base1) + (1084715267/100000000000000 : ℝ)*(base19) + (1082701233/100000000000000 : ℝ)*(base23) + (26596581/20000000000000 : ℝ)*(upper3) + (2158467/1562500000000 : ℝ)*(upper5) + (666549719784429/100000000000000 : ℝ)*(major0) + (666549719784429/100000000000000 : ℝ)*(major1) + (666549719784429/100000000000000 : ℝ)*(major2) + (460140242384151/50000000000000 : ℝ)*(sp0) + (18405663214411/2000000000000 : ℝ)*(sp1) + (184056632546917/20000000000000 : ℝ)*(sp2) + (412813301649349/100000000000000 : ℝ)*(sp3) + (3809243383/100000000000000 : ℝ)*(sp4) + (1682206513/100000000000000 : ℝ)*(sp7) + (412815032431729/100000000000000 : ℝ)*(f.failure) + (460142122717909/50000000000000 : ℝ)*(f.sum) + (416707079004811/200000000000000000000000000000 : ℝ)*base66 + (787096119995189/400000000000000000000000000000 : ℝ)*base67 + (148379973604811/400000000000000000000000000000 : ℝ)*base70 + (1204246780395189/400000000000000000000000000000 : ℝ)*base71 + (342751062604811/200000000000000000000000000000 : ℝ)*base74 + (1775242133995189/400000000000000000000000000000 : ℝ)*base75 + (707756686395189/400000000000000000000000000000 : ℝ)*base77 + (647054687204811/400000000000000000000000000000 : ℝ)*base80 + (618044237004811/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (28871479/5000000000000000000000 : ℝ)*base90 + (28871479/5000000000000000000000 : ℝ)*base92 + (28871479/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (976871035509856740420699/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2168060839/100000000000000 : ℝ)*(base19) + (2194838001/100000000000000 : ℝ)*(base23) + (43188003/25000000000000 : ℝ)*(base32) + (65099939/20000000000000 : ℝ)*(upper3) + (26642019/12500000000000 : ℝ)*(upper5) + (703223514299829/100000000000000 : ℝ)*(major0) + (703223514299829/100000000000000 : ℝ)*(major1) + (703223514299829/100000000000000 : ℝ)*(major2) + (5368423089/100000000000000 : ℝ)*(sp1) + (2823328837/50000000000000 : ℝ)*(sp2) + (970918445674591/100000000000000 : ℝ)*(sp4) + (970910909190663/100000000000000 : ℝ)*(sp5) + (242727651044729/25000000000000 : ℝ)*(sp6) + (108882021137343/25000000000000 : ℝ)*(sp7) + (87105651460277/20000000000000 : ℝ)*(f.failure) + (970918445674591/100000000000000 : ℝ)*(f.sum) + (337657680886589/200000000000000000000000000000 : ℝ)*base65 + (937028507686589/400000000000000000000000000000 : ℝ)*base67 + (319948649286589/400000000000000000000000000000 : ℝ)*base69 + (1506382229286589/400000000000000000000000000000 : ℝ)*base71 + (419274471286589/200000000000000000000000000000 : ℝ)*base73 + (594602697286589/400000000000000000000000000000 : ℝ)*base75 + (72272811286589/400000000000000000000000000000 : ℝ)*base77 + (2341609297686589/400000000000000000000000000000 : ℝ)*base79 + (75979991286589/200000000000000000000000000000 : ℝ)*base81 + (6372973/1000000000000000000000 : ℝ)*base89 + (6372973/1000000000000000000000 : ℝ)*base91 + (6372973/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1488_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2513/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25799/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1488_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1488_s1_0 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1871795517/10000000000 : ℝ)*x 0 + (1396752061/2500000000 : ℝ)*x 1 + (5086593521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1871795517/10000000000 : ℝ)^4473 ≤ (2276269227911/20000000000000 : ℝ)^3449 := by
    have hnat : (1871795517 : ℕ)^4473*20000000000000^3449 ≤ 2276269227911^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871795517 10000000000 2276269227911 20000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1396752061/2500000000 : ℝ)^4473 ≤ (23501059825987/50000000000000 : ℝ)^3449 := by
    have hnat : (1396752061 : ℕ)^4473*50000000000000^3449 ≤ 23501059825987^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1396752061 2500000000 23501059825987 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5086593521/10000000000 : ℝ)^4473 ≤ (20808267096741/50000000000000 : ℝ)^3449 := by
    have hnat : (5086593521 : ℕ)^4473*50000000000000^3449 ≤ 20808267096741^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5086593521 10000000000 20808267096741 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1871795517/10000000000 : ℝ), (1396752061/2500000000 : ℝ), (5086593521/10000000000 : ℝ)] ![(2276269227911/20000000000000 : ℝ), (23501059825987/50000000000000 : ℝ), (20808267096741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1871795517/10000000000 : ℝ)|^4473 ≤ (2276269227911/20000000000000 : ℝ)^3449
        have hw : |(-1871795517/10000000000 : ℝ)|=(1871795517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1396752061/2500000000 : ℝ)|^4473 ≤ (23501059825987/50000000000000 : ℝ)^3449
        have hw : |(1396752061/2500000000 : ℝ)|=(1396752061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5086593521/10000000000 : ℝ)|^4473 ≤ (20808267096741/50000000000000 : ℝ)^3449
        have hw : |(5086593521/10000000000 : ℝ)|=(5086593521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s1_1 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391059883/10000000000 : ℝ)*x 0 + (-2136114449/10000000000 : ℝ)*x 1 + (5086593113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391059883/10000000000 : ℝ)^4473 ≤ (11218863181447/25000000000000 : ℝ)^3449 := by
    have hnat : (5391059883 : ℕ)^4473*25000000000000^3449 ≤ 11218863181447^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391059883 10000000000 11218863181447 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2136114449/10000000000 : ℝ)^4473 ≤ (844251087401/6250000000000 : ℝ)^3449 := by
    have hnat : (2136114449 : ℕ)^4473*6250000000000^3449 ≤ 844251087401^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136114449 10000000000 844251087401 6250000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5086593113/10000000000 : ℝ)^4473 ≤ (41616529864311/100000000000000 : ℝ)^3449 := by
    have hnat : (5086593113 : ℕ)^4473*100000000000000^3449 ≤ 41616529864311^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5086593113 10000000000 41616529864311 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391059883/10000000000 : ℝ), (-2136114449/10000000000 : ℝ), (5086593113/10000000000 : ℝ)] ![(11218863181447/25000000000000 : ℝ), (844251087401/6250000000000 : ℝ), (41616529864311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391059883/10000000000 : ℝ)|^4473 ≤ (11218863181447/25000000000000 : ℝ)^3449
        have hw : |(5391059883/10000000000 : ℝ)|=(5391059883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2136114449/10000000000 : ℝ)|^4473 ≤ (844251087401/6250000000000 : ℝ)^3449
        have hw : |(-2136114449/10000000000 : ℝ)|=(2136114449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5086593113/10000000000 : ℝ)|^4473 ≤ (41616529864311/100000000000000 : ℝ)^3449
        have hw : |(5086593113/10000000000 : ℝ)|=(5086593113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s1_2 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391059553/10000000000 : ℝ)*x 0 + (2543296639/5000000000 : ℝ)*x 1 + (-213611467/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391059553/10000000000 : ℝ)^4473 ≤ (44875449163293/100000000000000 : ℝ)^3449 := by
    have hnat : (5391059553 : ℕ)^4473*100000000000000^3449 ≤ 44875449163293^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391059553 10000000000 44875449163293 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2543296639/5000000000 : ℝ)^4473 ≤ (41616531615079/100000000000000 : ℝ)^3449 := by
    have hnat : (2543296639 : ℕ)^4473*100000000000000^3449 ≤ 41616531615079^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2543296639 5000000000 41616531615079 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (213611467/1000000000 : ℝ)^4473 ≤ (6754009605431/50000000000000 : ℝ)^3449 := by
    have hnat : (213611467 : ℕ)^4473*50000000000000^3449 ≤ 6754009605431^3449*1000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213611467 1000000000 6754009605431 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391059553/10000000000 : ℝ), (2543296639/5000000000 : ℝ), (-213611467/1000000000 : ℝ)] ![(44875449163293/100000000000000 : ℝ), (41616531615079/100000000000000 : ℝ), (6754009605431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391059553/10000000000 : ℝ)|^4473 ≤ (44875449163293/100000000000000 : ℝ)^3449
        have hw : |(5391059553/10000000000 : ℝ)|=(5391059553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2543296639/5000000000 : ℝ)|^4473 ≤ (41616531615079/100000000000000 : ℝ)^3449
        have hw : |(2543296639/5000000000 : ℝ)|=(2543296639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-213611467/1000000000 : ℝ)|^4473 ≤ (6754009605431/50000000000000 : ℝ)^3449
        have hw : |(-213611467/1000000000 : ℝ)|=(213611467/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s1_3 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2129177649/5000000000 : ℝ)*x 0 + (1866014351/5000000000 : ℝ)*x 1 + (4847598431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129177649/5000000000 : ℝ)^4473 ≤ (33049484003683/100000000000000 : ℝ)^3449 := by
    have hnat : (2129177649 : ℕ)^4473*100000000000000^3449 ≤ 33049484003683^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129177649 5000000000 33049484003683 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1866014351/5000000000 : ℝ)^4473 ≤ (5570400731453/20000000000000 : ℝ)^3449 := by
    have hnat : (1866014351 : ℕ)^4473*20000000000000^3449 ≤ 5570400731453^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866014351 5000000000 5570400731453 20000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4847598431/10000000000 : ℝ)^4473 ≤ (9774628081519/25000000000000 : ℝ)^3449 := by
    have hnat : (4847598431 : ℕ)^4473*25000000000000^3449 ≤ 9774628081519^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4847598431 10000000000 9774628081519 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2129177649/5000000000 : ℝ), (1866014351/5000000000 : ℝ), (4847598431/10000000000 : ℝ)] ![(33049484003683/100000000000000 : ℝ), (5570400731453/20000000000000 : ℝ), (9774628081519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2129177649/5000000000 : ℝ)|^4473 ≤ (33049484003683/100000000000000 : ℝ)^3449
        have hw : |(2129177649/5000000000 : ℝ)|=(2129177649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1866014351/5000000000 : ℝ)|^4473 ≤ (5570400731453/20000000000000 : ℝ)^3449
        have hw : |(1866014351/5000000000 : ℝ)|=(1866014351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4847598431/10000000000 : ℝ)|^4473 ≤ (9774628081519/25000000000000 : ℝ)^3449
        have hw : |(4847598431/10000000000 : ℝ)|=(4847598431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s1_4 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1872146793/10000000000 : ℝ)*x 0 + (5092382753/10000000000 : ℝ)*x 1 + (2790561151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1872146793/10000000000 : ℝ)^4473 ≤ (711507267389/6250000000000 : ℝ)^3449 := by
    have hnat : (1872146793 : ℕ)^4473*6250000000000^3449 ≤ 711507267389^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872146793 10000000000 711507267389 6250000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5092382753/10000000000 : ℝ)^4473 ≤ (20838986225079/50000000000000 : ℝ)^3449 := by
    have hnat : (5092382753 : ℕ)^4473*50000000000000^3449 ≤ 20838986225079^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5092382753 10000000000 20838986225079 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2790561151/5000000000 : ℝ)^4473 ≤ (4693791124849/10000000000000 : ℝ)^3449 := by
    have hnat : (2790561151 : ℕ)^4473*10000000000000^3449 ≤ 4693791124849^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2790561151 5000000000 4693791124849 10000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1872146793/10000000000 : ℝ), (5092382753/10000000000 : ℝ), (2790561151/5000000000 : ℝ)] ![(711507267389/6250000000000 : ℝ), (20838986225079/50000000000000 : ℝ), (4693791124849/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1872146793/10000000000 : ℝ)|^4473 ≤ (711507267389/6250000000000 : ℝ)^3449
        have hw : |(-1872146793/10000000000 : ℝ)|=(1872146793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5092382753/10000000000 : ℝ)|^4473 ≤ (20838986225079/50000000000000 : ℝ)^3449
        have hw : |(5092382753/10000000000 : ℝ)|=(5092382753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2790561151/5000000000 : ℝ)|^4473 ≤ (4693791124849/10000000000000 : ℝ)^3449
        have hw : |(2790561151/5000000000 : ℝ)|=(2790561151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s1_5 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2629823713/5000000000 : ℝ)*x 0 + (-1641585261/10000000000 : ℝ)*x 1 + (87205037/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629823713/5000000000 : ℝ)^4473 ≤ (43461960456539/100000000000000 : ℝ)^3449 := by
    have hnat : (2629823713 : ℕ)^4473*100000000000000^3449 ≤ 43461960456539^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629823713 5000000000 43461960456539 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1641585261/10000000000 : ℝ)^4473 ≤ (480006377957/5000000000000 : ℝ)^3449 := by
    have hnat : (1641585261 : ℕ)^4473*5000000000000^3449 ≤ 480006377957^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1641585261 10000000000 480006377957 5000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87205037/156250000 : ℝ)^4473 ≤ (11734477992089/25000000000000 : ℝ)^3449 := by
    have hnat : (87205037 : ℕ)^4473*25000000000000^3449 ≤ 11734477992089^3449*156250000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87205037 156250000 11734477992089 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2629823713/5000000000 : ℝ), (-1641585261/10000000000 : ℝ), (87205037/156250000 : ℝ)] ![(43461960456539/100000000000000 : ℝ), (480006377957/5000000000000 : ℝ), (11734477992089/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2629823713/5000000000 : ℝ)|^4473 ≤ (43461960456539/100000000000000 : ℝ)^3449
        have hw : |(2629823713/5000000000 : ℝ)|=(2629823713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1641585261/10000000000 : ℝ)|^4473 ≤ (480006377957/5000000000000 : ℝ)^3449
        have hw : |(-1641585261/10000000000 : ℝ)|=(1641585261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(87205037/156250000 : ℝ)|^4473 ≤ (11734477992089/25000000000000 : ℝ)^3449
        have hw : |(87205037/156250000 : ℝ)|=(87205037/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s1_6 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5259647403/10000000000 : ℝ)*x 0 + (1395280589/2500000000 : ℝ)*x 1 + (-51299541/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259647403/10000000000 : ℝ)^4473 ≤ (5432745026257/12500000000000 : ℝ)^3449 := by
    have hnat : (5259647403 : ℕ)^4473*12500000000000^3449 ≤ 5432745026257^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259647403 10000000000 5432745026257 12500000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1395280589/2500000000 : ℝ)^4473 ≤ (1466809744921/3125000000000 : ℝ)^3449 := by
    have hnat : (1395280589 : ℕ)^4473*3125000000000^3449 ≤ 1466809744921^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1395280589 2500000000 1466809744921 3125000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51299541/312500000 : ℝ)^4473 ≤ (9600127945943/100000000000000 : ℝ)^3449 := by
    have hnat : (51299541 : ℕ)^4473*100000000000000^3449 ≤ 9600127945943^3449*312500000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51299541 312500000 9600127945943 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259647403/10000000000 : ℝ), (1395280589/2500000000 : ℝ), (-51299541/312500000 : ℝ)] ![(5432745026257/12500000000000 : ℝ), (1466809744921/3125000000000 : ℝ), (9600127945943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259647403/10000000000 : ℝ)|^4473 ≤ (5432745026257/12500000000000 : ℝ)^3449
        have hw : |(5259647403/10000000000 : ℝ)|=(5259647403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1395280589/2500000000 : ℝ)|^4473 ≤ (1466809744921/3125000000000 : ℝ)^3449
        have hw : |(1395280589/2500000000 : ℝ)|=(1395280589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51299541/312500000 : ℝ)|^4473 ≤ (9600127945943/100000000000000 : ℝ)^3449
        have hw : |(-51299541/312500000 : ℝ)|=(51299541/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s1_7 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4259138227/10000000000 : ℝ)*x 0 + (4834692717/10000000000 : ℝ)*x 1 + (1872574933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4259138227/10000000000 : ℝ)^4473 ≤ (8264341166531/25000000000000 : ℝ)^3449 := by
    have hnat : (4259138227 : ℕ)^4473*25000000000000^3449 ≤ 8264341166531^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4259138227 10000000000 8264341166531 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4834692717/10000000000 : ℝ)^4473 ≤ (19481784787967/50000000000000 : ℝ)^3449 := by
    have hnat : (4834692717 : ℕ)^4473*50000000000000^3449 ≤ 19481784787967^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4834692717 10000000000 19481784787967 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1872574933/5000000000 : ℝ)^4473 ≤ (5595813147281/20000000000000 : ℝ)^3449 := by
    have hnat : (1872574933 : ℕ)^4473*20000000000000^3449 ≤ 5595813147281^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872574933 5000000000 5595813147281 20000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4259138227/10000000000 : ℝ), (4834692717/10000000000 : ℝ), (1872574933/5000000000 : ℝ)] ![(8264341166531/25000000000000 : ℝ), (19481784787967/50000000000000 : ℝ), (5595813147281/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4259138227/10000000000 : ℝ)|^4473 ≤ (8264341166531/25000000000000 : ℝ)^3449
        have hw : |(4259138227/10000000000 : ℝ)|=(4259138227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4834692717/10000000000 : ℝ)|^4473 ≤ (19481784787967/50000000000000 : ℝ)^3449
        have hw : |(4834692717/10000000000 : ℝ)|=(4834692717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1872574933/5000000000 : ℝ)|^4473 ≤ (5595813147281/20000000000000 : ℝ)^3449
        have hw : |(1872574933/5000000000 : ℝ)|=(1872574933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1488_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25799/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2513/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4011/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9301/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25799/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2513/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25799/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2513/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25799/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2513/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25799/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2513/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25799/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2513/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25799/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2513/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
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
  have hpowlo : (2513/100000 : ℝ) ^ (4471/1024 : ℝ) ≤ (5174554317761/50000000000000000000 : ℝ) := by
    have hpowers : (2513/100000 : ℝ)^4471 ≤ (5174554317761/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2513 : ℕ)^4471*50000000000000000000^1024 ≤ 5174554317761^1024*100000^4471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2513 100000 5174554317761 50000000000000000000 4471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2513/100000 : ℝ)) (X := (5174554317761/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25799/100000 : ℝ) ^ (4471/1024 : ℝ) ≤ (134866482519567323/50000000000000000000 : ℝ) := by
    have hpowers : (25799/100000 : ℝ)^4471 ≤ (134866482519567323/50000000000000000000 : ℝ)^1024 := by
      have hnat : (25799 : ℕ)^4471*50000000000000000000^1024 ≤ 134866482519567323^1024*100000^4471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25799 100000 134866482519567323 50000000000000000000 4471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25799/100000 : ℝ)) (X := (134866482519567323/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000005174554317761/25000000000000000000 : ℝ) ≤ (10000000474054413/10000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (25000005174554317761/25000000000000000000 : ℝ)^1024 ≤ (10000000474054413/10000000000000000 : ℝ)^4471 := by
      have hnat : (25000005174554317761 : ℕ)^1024*10000000000000000^4471 ≤ 10000000474054413^4471*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000005174554317761 25000000000000000000 10000000474054413 10000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000474054413/10000000000000000 : ℝ)) (X := (25000005174554317761/25000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12533717914268471271/12500000000000000000 : ℝ) ≤ (1000617155881529/1000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (12533717914268471271/12500000000000000000 : ℝ)^1024 ≤ (1000617155881529/1000000000000000 : ℝ)^4471 := by
      have hnat : (12533717914268471271 : ℕ)^1024*1000000000000000^4471 ≤ 1000617155881529^4471*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12533717914268471271 12500000000000000000 1000617155881529 1000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000617155881529/1000000000000000 : ℝ)) (X := (12533717914268471271/12500000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25134866482519567323/25000000000000000000 : ℝ) ≤ (10012342643576167/10000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (25134866482519567323/25000000000000000000 : ℝ)^1024 ≤ (10012342643576167/10000000000000000 : ℝ)^4471 := by
      have hnat : (25134866482519567323 : ℕ)^1024*10000000000000000^4471 ≤ 10012342643576167^4471*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25134866482519567323 25000000000000000000 10012342643576167 10000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012342643576167/10000000000000000 : ℝ)) (X := (25134866482519567323/25000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5174554317761/50000000000000000000 : ℝ) ≤ ((58207248791705723329/58215000000000000000 : ℝ)+2*(6171084760877/2328600000000000 : ℝ)*(2513/100000 : ℝ))^(4471/1024 : ℝ) := by
    rw [show (58207248791705723329/58215000000000000000 : ℝ)+2*(6171084760877/2328600000000000 : ℝ)*(2513/100000 : ℝ)=(10000000474054413/10000000000000000 : ℝ) by norm_num, show 1+2*(5174554317761/50000000000000000000 : ℝ)=(25000005174554317761/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(134866482519567323/50000000000000000000 : ℝ)+(5174554317761/50000000000000000000 : ℝ) ≤ ((58207248791705723329/58215000000000000000 : ℝ)+(6171084760877/2328600000000000 : ℝ)*((25799/100000 : ℝ)+(2513/100000 : ℝ)))^(4471/1024 : ℝ) := by
    rw [show (58207248791705723329/58215000000000000000 : ℝ)+(6171084760877/2328600000000000 : ℝ)*((25799/100000 : ℝ)+(2513/100000 : ℝ))=(1000617155881529/1000000000000000 : ℝ) by norm_num, show 1+(134866482519567323/50000000000000000000 : ℝ)+(5174554317761/50000000000000000000 : ℝ)=(12533717914268471271/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(134866482519567323/50000000000000000000 : ℝ) ≤ ((58207248791705723329/58215000000000000000 : ℝ)+2*(6171084760877/2328600000000000 : ℝ)*(25799/100000 : ℝ))^(4471/1024 : ℝ) := by
    rw [show (58207248791705723329/58215000000000000000 : ℝ)+2*(6171084760877/2328600000000000 : ℝ)*(25799/100000 : ℝ)=(10012342643576167/10000000000000000 : ℝ) by norm_num, show 1+2*(134866482519567323/50000000000000000000 : ℝ)=(25134866482519567323/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (58207248791705723329/58215000000000000000 : ℝ)*(X 1 0+X 2 0)+(6171084760877/2328600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (2513/100000 : ℝ)) (hi := (25799/100000 : ℝ)) (c := (58207248791705723329/58215000000000000000 : ℝ)) (alpha := (6171084760877/2328600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (58207248791705723329/58215000000000000000 : ℝ)*(X 0 1+X 2 1)+(6171084760877/2328600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (2513/100000 : ℝ)) (hi := (25799/100000 : ℝ)) (c := (58207248791705723329/58215000000000000000 : ℝ)) (alpha := (6171084760877/2328600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (58207248791705723329/58215000000000000000 : ℝ)*(X 0 2+X 1 2)+(6171084760877/2328600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (2513/100000 : ℝ)) (hi := (25799/100000 : ℝ)) (c := (58207248791705723329/58215000000000000000 : ℝ)) (alpha := (6171084760877/2328600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1871795517/10000000000 : ℝ)*X 0 0+(1396752061/2500000000 : ℝ)*X 0 1+(5086593521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5391059883/10000000000 : ℝ)*X 1 0+(-2136114449/10000000000 : ℝ)*X 1 1+(5086593113/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5391059553/10000000000 : ℝ)*X 2 0+(2543296639/5000000000 : ℝ)*X 2 1+(-213611467/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2129177649/5000000000 : ℝ)*X 0 0+(1866014351/5000000000 : ℝ)*X 0 1+(4847598431/10000000000 : ℝ)*X 0 2+(2129177649/5000000000 : ℝ)*X 1 0+(1866014351/5000000000 : ℝ)*X 1 1+(4847598431/10000000000 : ℝ)*X 1 2+(2129177649/5000000000 : ℝ)*X 2 0+(1866014351/5000000000 : ℝ)*X 2 1+(4847598431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1872146793/10000000000 : ℝ)*X 0 0+(5092382753/10000000000 : ℝ)*X 0 1+(2790561151/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2629823713/5000000000 : ℝ)*X 1 0+(-1641585261/10000000000 : ℝ)*X 1 1+(87205037/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5259647403/10000000000 : ℝ)*X 2 0+(1395280589/2500000000 : ℝ)*X 2 1+(-51299541/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4259138227/10000000000 : ℝ)*X 0 0+(4834692717/10000000000 : ℝ)*X 0 1+(1872574933/5000000000 : ℝ)*X 0 2+(4259138227/10000000000 : ℝ)*X 1 0+(4834692717/10000000000 : ℝ)*X 1 1+(1872574933/5000000000 : ℝ)*X 1 2+(4259138227/10000000000 : ℝ)*X 2 0+(4834692717/10000000000 : ℝ)*X 2 1+(1872574933/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (760093266538035502409614737/97025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22632917/25000000000000 : ℝ)*(base1) + (719098397/50000000000000 : ℝ)*(base19) + (328968111/25000000000000 : ℝ)*(base23) + (112889049/50000000000000 : ℝ)*(upper3) + (94481199/100000000000000 : ℝ)*(upper5) + (144738466195749/10000000000000 : ℝ)*(major0) + (144738466195749/10000000000000 : ℝ)*(major1) + (144738466195749/10000000000000 : ℝ)*(major2) + (1998351541603651/100000000000000 : ℝ)*(sp0) + (12489732229501/625000000000 : ℝ)*(sp1) + (199835727904451/10000000000000 : ℝ)*(sp2) + (112050793125061/12500000000000 : ℝ)*(sp3) + (7143844971/100000000000000 : ℝ)*(sp4) + (4032332729/100000000000000 : ℝ)*(sp7) + (448205233932443/50000000000000 : ℝ)*(f.failure) + (999179297458477/50000000000000 : ℝ)*(f.sum) + (3405542996697/1940500000000000000000000000 : ℝ)*base65 + (182372553441117807/194050000000000000000000000000000 : ℝ)*base67 + (1703848400226167807/194050000000000000000000000000000 : ℝ)*base69 + (757278102061567807/194050000000000000000000000000000 : ℝ)*base71 + (1904427798329/1940500000000000000000000000 : ℝ)*base74 + (788112931344817807/194050000000000000000000000000000 : ℝ)*base75 + (1938196010424067807/194050000000000000000000000000000 : ℝ)*base77 + (709195061490467807/194050000000000000000000000000000 : ℝ)*base79 + (7836521465389/3881000000000000000000000000 : ℝ)*base81 + (12545693/2500000000000000000000 : ℝ)*base90 + (12545693/2500000000000000000000 : ℝ)*base92 + (12545693/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (415919476839568278303964431/121281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6769049/1000000000000 : ℝ)*(base19) + (140602921/20000000000000 : ℝ)*(base23) + (20527579/20000000000000 : ℝ)*(upper3) + (12778207/100000000000000 : ℝ)*(lower4) + (24370373/50000000000000 : ℝ)*(upper5) + (370486898593811/25000000000000 : ℝ)*(major0) + (370486898593811/25000000000000 : ℝ)*(major1) + (370486898593811/25000000000000 : ℝ)*(major2) + (829317/19531250000 : ℝ)*(sp1) + (4676861291/100000000000000 : ℝ)*(sp2) + (2046078704442207/100000000000000 : ℝ)*(sp4) + (2046073781434267/100000000000000 : ℝ)*(sp5) + (2046073324566311/100000000000000 : ℝ)*(sp6) + (28681761562363/3125000000000 : ℝ)*(sp7) + (28681761562363/3125000000000 : ℝ)*(f.failure) + (2046078704442207/100000000000000 : ℝ)*(f.sum) + (248530436179921/58215000000000000000000000000 : ℝ)*base66 + (1595066057418422273/485125000000000000000000000000000 : ℝ)*base67 + (452206919895047273/485125000000000000000000000000000 : ℝ)*base69 + (768666380235452727/485125000000000000000000000000000 : ℝ)*base72 + (69440391665881/58215000000000000000000000000 : ℝ)*base74 + (3814148754417297273/485125000000000000000000000000000 : ℝ)*base75 + (390388354150297273/485125000000000000000000000000000 : ℝ)*base77 + (2636389420220547273/485125000000000000000000000000000 : ℝ)*base79 + (37041998956279/14553750000000000000000000000 : ℝ)*base82 + (5613/156250000000000000000 : ℝ)*base90 + (5613/156250000000000000000 : ℝ)*base92 + (5613/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1488_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25799/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2513/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4011/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9301/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1488_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1488_s2_0 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1899214461/10000000000 : ℝ)*x 0 + (5466019633/10000000000 : ℝ)*x 1 + (2594933479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1899214461/10000000000 : ℝ)^4473 ≤ (11598032617799/100000000000000 : ℝ)^3449 := by
    have hnat : (1899214461 : ℕ)^4473*100000000000000^3449 ≤ 11598032617799^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899214461 10000000000 11598032617799 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5466019633/10000000000 : ℝ)^4473 ≤ (22843170598221/50000000000000 : ℝ)^3449 := by
    have hnat : (5466019633 : ℕ)^4473*50000000000000^3449 ≤ 22843170598221^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466019633 10000000000 22843170598221 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2594933479/5000000000 : ℝ)^4473 ≤ (8543125232213/20000000000000 : ℝ)^3449 := by
    have hnat : (2594933479 : ℕ)^4473*20000000000000^3449 ≤ 8543125232213^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594933479 5000000000 8543125232213 20000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1899214461/10000000000 : ℝ), (5466019633/10000000000 : ℝ), (2594933479/5000000000 : ℝ)] ![(11598032617799/100000000000000 : ℝ), (22843170598221/50000000000000 : ℝ), (8543125232213/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1899214461/10000000000 : ℝ)|^4473 ≤ (11598032617799/100000000000000 : ℝ)^3449
        have hw : |(-1899214461/10000000000 : ℝ)|=(1899214461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5466019633/10000000000 : ℝ)|^4473 ≤ (22843170598221/50000000000000 : ℝ)^3449
        have hw : |(5466019633/10000000000 : ℝ)|=(5466019633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2594933479/5000000000 : ℝ)|^4473 ≤ (8543125232213/20000000000000 : ℝ)^3449
        have hw : |(2594933479/5000000000 : ℝ)|=(2594933479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s2_1 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2680277751/5000000000 : ℝ)*x 0 + (-255198631/1250000000 : ℝ)*x 1 + (162183349/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680277751/5000000000 : ℝ)^4473 ≤ (356371371647/800000000000 : ℝ)^3449 := by
    have hnat : (2680277751 : ℕ)^4473*800000000000^3449 ≤ 356371371647^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680277751 5000000000 356371371647 800000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (255198631/1250000000 : ℝ)^4473 ≤ (3184487532183/25000000000000 : ℝ)^3449 := by
    have hnat : (255198631 : ℕ)^4473*25000000000000^3449 ≤ 3184487532183^3449*1250000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255198631 1250000000 3184487532183 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (162183349/312500000 : ℝ)^4473 ≤ (10678907100663/25000000000000 : ℝ)^3449 := by
    have hnat : (162183349 : ℕ)^4473*25000000000000^3449 ≤ 10678907100663^3449*312500000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162183349 312500000 10678907100663 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680277751/5000000000 : ℝ), (-255198631/1250000000 : ℝ), (162183349/312500000 : ℝ)] ![(356371371647/800000000000 : ℝ), (3184487532183/25000000000000 : ℝ), (10678907100663/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680277751/5000000000 : ℝ)|^4473 ≤ (356371371647/800000000000 : ℝ)^3449
        have hw : |(2680277751/5000000000 : ℝ)|=(2680277751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-255198631/1250000000 : ℝ)|^4473 ≤ (3184487532183/25000000000000 : ℝ)^3449
        have hw : |(-255198631/1250000000 : ℝ)|=(255198631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(162183349/312500000 : ℝ)|^4473 ≤ (10678907100663/25000000000000 : ℝ)^3449
        have hw : |(162183349/312500000 : ℝ)|=(162183349/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s2_2 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (67006947/125000000 : ℝ)*x 0 + (2594933517/5000000000 : ℝ)*x 1 + (-25519861/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67006947/125000000 : ℝ)^4473 ≤ (44546424236411/100000000000000 : ℝ)^3449 := by
    have hnat : (67006947 : ℕ)^4473*100000000000000^3449 ≤ 44546424236411^3449*125000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67006947 125000000 44546424236411 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2594933517/5000000000 : ℝ)^4473 ≤ (21357813486153/50000000000000 : ℝ)^3449 := by
    have hnat : (2594933517 : ℕ)^4473*50000000000000^3449 ≤ 21357813486153^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594933517 5000000000 21357813486153 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25519861/125000000 : ℝ)^4473 ≤ (1592243596167/12500000000000 : ℝ)^3449 := by
    have hnat : (25519861 : ℕ)^4473*12500000000000^3449 ≤ 1592243596167^3449*125000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25519861 125000000 1592243596167 12500000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67006947/125000000 : ℝ), (2594933517/5000000000 : ℝ), (-25519861/125000000 : ℝ)] ![(44546424236411/100000000000000 : ℝ), (21357813486153/50000000000000 : ℝ), (1592243596167/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67006947/125000000 : ℝ)|^4473 ≤ (44546424236411/100000000000000 : ℝ)^3449
        have hw : |(67006947/125000000 : ℝ)|=(67006947/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2594933517/5000000000 : ℝ)|^4473 ≤ (21357813486153/50000000000000 : ℝ)^3449
        have hw : |(2594933517/5000000000 : ℝ)|=(2594933517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25519861/125000000 : ℝ)|^4473 ≤ (1592243596167/12500000000000 : ℝ)^3449
        have hw : |(-25519861/125000000 : ℝ)|=(25519861/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s2_3 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4277951699/10000000000 : ℝ)*x 0 + (3979720297/10000000000 : ℝ)*x 1 + (459534553/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4277951699/10000000000 : ℝ)^4473 ≤ (16623431531589/50000000000000 : ℝ)^3449 := by
    have hnat : (4277951699 : ℕ)^4473*50000000000000^3449 ≤ 16623431531589^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4277951699 10000000000 16623431531589 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979720297/10000000000 : ℝ)^4473 ≤ (7568149815281/25000000000000 : ℝ)^3449 := by
    have hnat : (3979720297 : ℕ)^4473*25000000000000^3449 ≤ 7568149815281^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979720297 10000000000 7568149815281 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (459534553/1000000000 : ℝ)^4473 ≤ (1459221506443/4000000000000 : ℝ)^3449 := by
    have hnat : (459534553 : ℕ)^4473*4000000000000^3449 ≤ 1459221506443^3449*1000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459534553 1000000000 1459221506443 4000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4277951699/10000000000 : ℝ), (3979720297/10000000000 : ℝ), (459534553/1000000000 : ℝ)] ![(16623431531589/50000000000000 : ℝ), (7568149815281/25000000000000 : ℝ), (1459221506443/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4277951699/10000000000 : ℝ)|^4473 ≤ (16623431531589/50000000000000 : ℝ)^3449
        have hw : |(4277951699/10000000000 : ℝ)|=(4277951699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979720297/10000000000 : ℝ)|^4473 ≤ (7568149815281/25000000000000 : ℝ)^3449
        have hw : |(3979720297/10000000000 : ℝ)|=(3979720297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(459534553/1000000000 : ℝ)|^4473 ≤ (1459221506443/4000000000000 : ℝ)^3449
        have hw : |(459534553/1000000000 : ℝ)|=(459534553/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s2_4 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-379854751/2000000000 : ℝ)*x 0 + (5191639051/10000000000 : ℝ)*x 1 + (5464231111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (379854751/2000000000 : ℝ)^4473 ≤ (11598502218551/100000000000000 : ℝ)^3449 := by
    have hnat : (379854751 : ℕ)^4473*100000000000000^3449 ≤ 11598502218551^3449*2000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379854751 2000000000 11598502218551 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5191639051/10000000000 : ℝ)^4473 ≤ (5341817854371/12500000000000 : ℝ)^3449 := by
    have hnat : (5191639051 : ℕ)^4473*12500000000000^3449 ≤ 5341817854371^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191639051 10000000000 5341817854371 12500000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5464231111/10000000000 : ℝ)^4473 ≤ (45666954934137/100000000000000 : ℝ)^3449 := by
    have hnat : (5464231111 : ℕ)^4473*100000000000000^3449 ≤ 45666954934137^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464231111 10000000000 45666954934137 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-379854751/2000000000 : ℝ), (5191639051/10000000000 : ℝ), (5464231111/10000000000 : ℝ)] ![(11598502218551/100000000000000 : ℝ), (5341817854371/12500000000000 : ℝ), (45666954934137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-379854751/2000000000 : ℝ)|^4473 ≤ (11598502218551/100000000000000 : ℝ)^3449
        have hw : |(-379854751/2000000000 : ℝ)|=(379854751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5191639051/10000000000 : ℝ)|^4473 ≤ (5341817854371/12500000000000 : ℝ)^3449
        have hw : |(5191639051/10000000000 : ℝ)|=(5191639051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5464231111/10000000000 : ℝ)|^4473 ≤ (45666954934137/100000000000000 : ℝ)^3449
        have hw : |(5464231111/10000000000 : ℝ)|=(5464231111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s2_5 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66103883/125000000 : ℝ)*x 0 + (-441806247/2500000000 : ℝ)*x 1 + (1092846217/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66103883/125000000 : ℝ)^4473 ≤ (8753876360767/20000000000000 : ℝ)^3449 := by
    have hnat : (66103883 : ℕ)^4473*20000000000000^3449 ≤ 8753876360767^3449*125000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66103883 125000000 8753876360767 20000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441806247/2500000000 : ℝ)^4473 ≤ (2112732706299/20000000000000 : ℝ)^3449 := by
    have hnat : (441806247 : ℕ)^4473*20000000000000^3449 ≤ 2112732706299^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441806247 2500000000 2112732706299 20000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092846217/2000000000 : ℝ)^4473 ≤ (45666954652329/100000000000000 : ℝ)^3449 := by
    have hnat : (1092846217 : ℕ)^4473*100000000000000^3449 ≤ 45666954652329^3449*2000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092846217 2000000000 45666954652329 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66103883/125000000 : ℝ), (-441806247/2500000000 : ℝ), (1092846217/2000000000 : ℝ)] ![(8753876360767/20000000000000 : ℝ), (2112732706299/20000000000000 : ℝ), (45666954652329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66103883/125000000 : ℝ)|^4473 ≤ (8753876360767/20000000000000 : ℝ)^3449
        have hw : |(66103883/125000000 : ℝ)|=(66103883/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-441806247/2500000000 : ℝ)|^4473 ≤ (2112732706299/20000000000000 : ℝ)^3449
        have hw : |(-441806247/2500000000 : ℝ)|=(441806247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092846217/2000000000 : ℝ)|^4473 ≤ (45666954652329/100000000000000 : ℝ)^3449
        have hw : |(1092846217/2000000000 : ℝ)|=(1092846217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s2_6 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288310827/10000000000 : ℝ)*x 0 + (5464231103/10000000000 : ℝ)*x 1 + (-13806443/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288310827/10000000000 : ℝ)^4473 ≤ (21884691905541/50000000000000 : ℝ)^3449 := by
    have hnat : (5288310827 : ℕ)^4473*50000000000000^3449 ≤ 21884691905541^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288310827 10000000000 21884691905541 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5464231103/10000000000 : ℝ)^4473 ≤ (45666954847427/100000000000000 : ℝ)^3449 := by
    have hnat : (5464231103 : ℕ)^4473*100000000000000^3449 ≤ 45666954847427^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464231103 10000000000 45666954847427 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13806443/78125000 : ℝ)^4473 ≤ (10563661329853/100000000000000 : ℝ)^3449 := by
    have hnat : (13806443 : ℕ)^4473*100000000000000^3449 ≤ 10563661329853^3449*78125000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13806443 78125000 10563661329853 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288310827/10000000000 : ℝ), (5464231103/10000000000 : ℝ), (-13806443/78125000 : ℝ)] ![(21884691905541/50000000000000 : ℝ), (45666954847427/100000000000000 : ℝ), (10563661329853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288310827/10000000000 : ℝ)|^4473 ≤ (21884691905541/50000000000000 : ℝ)^3449
        have hw : |(5288310827/10000000000 : ℝ)|=(5288310827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5464231103/10000000000 : ℝ)|^4473 ≤ (45666954847427/100000000000000 : ℝ)^3449
        have hw : |(5464231103/10000000000 : ℝ)|=(5464231103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13806443/78125000 : ℝ)|^4473 ≤ (10563661329853/100000000000000 : ℝ)^3449
        have hw : |(-13806443/78125000 : ℝ)|=(13806443/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s2_7 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4278083479/10000000000 : ℝ)*x 0 + (4591394341/10000000000 : ℝ)*x 1 + (248981757/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4278083479/10000000000 : ℝ)^4473 ≤ (1662409564461/5000000000000 : ℝ)^3449 := by
    have hnat : (4278083479 : ℕ)^4473*5000000000000^3449 ≤ 1662409564461^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278083479 10000000000 1662409564461 5000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4591394341/10000000000 : ℝ)^4473 ≤ (18219931632271/50000000000000 : ℝ)^3449 := by
    have hnat : (4591394341 : ℕ)^4473*50000000000000^3449 ≤ 18219931632271^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4591394341 10000000000 18219931632271 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (248981757/625000000 : ℝ)^4473 ≤ (15155972714923/50000000000000 : ℝ)^3449 := by
    have hnat : (248981757 : ℕ)^4473*50000000000000^3449 ≤ 15155972714923^3449*625000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248981757 625000000 15155972714923 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4278083479/10000000000 : ℝ), (4591394341/10000000000 : ℝ), (248981757/625000000 : ℝ)] ![(1662409564461/5000000000000 : ℝ), (18219931632271/50000000000000 : ℝ), (15155972714923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4278083479/10000000000 : ℝ)|^4473 ≤ (1662409564461/5000000000000 : ℝ)^3449
        have hw : |(4278083479/10000000000 : ℝ)|=(4278083479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4591394341/10000000000 : ℝ)|^4473 ≤ (18219931632271/50000000000000 : ℝ)^3449
        have hw : |(4591394341/10000000000 : ℝ)|=(4591394341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(248981757/625000000 : ℝ)|^4473 ≤ (15155972714923/50000000000000 : ℝ)^3449
        have hw : |(248981757/625000000 : ℝ)|=(248981757/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1488_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9301/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4011/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10253/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3219/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9301/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4011/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9301/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4011/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9301/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4011/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9301/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4011/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9301/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4011/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9301/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4011/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4011/50000 : ℝ) ^ (4471/1024 : ℝ) ≤ (410967013209893/25000000000000000000 : ℝ) := by
    have hpowers : (4011/50000 : ℝ)^4471 ≤ (410967013209893/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4011 : ℕ)^4471*25000000000000000000^1024 ≤ 410967013209893^1024*50000^4471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4011 50000 410967013209893 25000000000000000000 4471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4011/50000 : ℝ)) (X := (410967013209893/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9301/50000 : ℝ) ^ (4471/1024 : ℝ) ≤ (32338011822970067/50000000000000000000 : ℝ) := by
    have hpowers : (9301/50000 : ℝ)^4471 ≤ (32338011822970067/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9301 : ℕ)^4471*50000000000000000000^1024 ≤ 32338011822970067^1024*50000^4471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9301 50000 32338011822970067 50000000000000000000 4471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9301/50000 : ℝ)) (X := (32338011822970067/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500410967013209893/12500000000000000000 : ℝ) ≤ (10000075298570907/10000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (12500410967013209893/12500000000000000000 : ℝ)^1024 ≤ (10000075298570907/10000000000000000 : ℝ)^4471 := by
      have hnat : (12500410967013209893 : ℕ)^1024*10000000000000000^4471 ≤ 10000075298570907^4471*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500410967013209893 12500000000000000000 10000075298570907 10000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000075298570907/10000000000000000 : ℝ)) (X := (12500410967013209893/12500000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50033159945849389853/50000000000000000000 : ℝ) ≤ (10001518546502257/10000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (50033159945849389853/50000000000000000000 : ℝ)^1024 ≤ (10001518546502257/10000000000000000 : ℝ)^4471 := by
      have hnat : (50033159945849389853 : ℕ)^1024*10000000000000000^4471 ≤ 10001518546502257^4471*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033159945849389853 50000000000000000000 10001518546502257 10000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001518546502257/10000000000000000 : ℝ)) (X := (50033159945849389853/50000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25032338011822970067/25000000000000000000 : ℝ) ≤ (10002961794433607/10000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (25032338011822970067/25000000000000000000 : ℝ)^1024 ≤ (10002961794433607/10000000000000000 : ℝ)^4471 := by
      have hnat : (25032338011822970067 : ℕ)^1024*10000000000000000^4471 ≤ 10002961794433607^4471*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25032338011822970067 25000000000000000000 10002961794433607 10000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002961794433607/10000000000000000 : ℝ)) (X := (25032338011822970067/25000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(410967013209893/25000000000000000000 : ℝ) ≤ ((5288882059453480833/5290000000000000000 : ℝ)+2*(28864958627/21160000000000 : ℝ)*(4011/50000 : ℝ))^(4471/1024 : ℝ) := by
    rw [show (5288882059453480833/5290000000000000000 : ℝ)+2*(28864958627/21160000000000 : ℝ)*(4011/50000 : ℝ)=(10000075298570907/10000000000000000 : ℝ) by norm_num, show 1+2*(410967013209893/25000000000000000000 : ℝ)=(12500410967013209893/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32338011822970067/50000000000000000000 : ℝ)+(410967013209893/25000000000000000000 : ℝ) ≤ ((5288882059453480833/5290000000000000000 : ℝ)+(28864958627/21160000000000 : ℝ)*((9301/50000 : ℝ)+(4011/50000 : ℝ)))^(4471/1024 : ℝ) := by
    rw [show (5288882059453480833/5290000000000000000 : ℝ)+(28864958627/21160000000000 : ℝ)*((9301/50000 : ℝ)+(4011/50000 : ℝ))=(10001518546502257/10000000000000000 : ℝ) by norm_num, show 1+(32338011822970067/50000000000000000000 : ℝ)+(410967013209893/25000000000000000000 : ℝ)=(50033159945849389853/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32338011822970067/50000000000000000000 : ℝ) ≤ ((5288882059453480833/5290000000000000000 : ℝ)+2*(28864958627/21160000000000 : ℝ)*(9301/50000 : ℝ))^(4471/1024 : ℝ) := by
    rw [show (5288882059453480833/5290000000000000000 : ℝ)+2*(28864958627/21160000000000 : ℝ)*(9301/50000 : ℝ)=(10002961794433607/10000000000000000 : ℝ) by norm_num, show 1+2*(32338011822970067/50000000000000000000 : ℝ)=(25032338011822970067/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5288882059453480833/5290000000000000000 : ℝ)*(X 1 0+X 2 0)+(28864958627/21160000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (4011/50000 : ℝ)) (hi := (9301/50000 : ℝ)) (c := (5288882059453480833/5290000000000000000 : ℝ)) (alpha := (28864958627/21160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5288882059453480833/5290000000000000000 : ℝ)*(X 0 1+X 2 1)+(28864958627/21160000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (4011/50000 : ℝ)) (hi := (9301/50000 : ℝ)) (c := (5288882059453480833/5290000000000000000 : ℝ)) (alpha := (28864958627/21160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5288882059453480833/5290000000000000000 : ℝ)*(X 0 2+X 1 2)+(28864958627/21160000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (4011/50000 : ℝ)) (hi := (9301/50000 : ℝ)) (c := (5288882059453480833/5290000000000000000 : ℝ)) (alpha := (28864958627/21160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1899214461/10000000000 : ℝ)*X 0 0+(5466019633/10000000000 : ℝ)*X 0 1+(2594933479/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2680277751/5000000000 : ℝ)*X 1 0+(-255198631/1250000000 : ℝ)*X 1 1+(162183349/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((67006947/125000000 : ℝ)*X 2 0+(2594933517/5000000000 : ℝ)*X 2 1+(-25519861/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4277951699/10000000000 : ℝ)*X 0 0+(3979720297/10000000000 : ℝ)*X 0 1+(459534553/1000000000 : ℝ)*X 0 2+(4277951699/10000000000 : ℝ)*X 1 0+(3979720297/10000000000 : ℝ)*X 1 1+(459534553/1000000000 : ℝ)*X 1 2+(4277951699/10000000000 : ℝ)*X 2 0+(3979720297/10000000000 : ℝ)*X 2 1+(459534553/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-379854751/2000000000 : ℝ)*X 0 0+(5191639051/10000000000 : ℝ)*X 0 1+(5464231111/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((66103883/125000000 : ℝ)*X 1 0+(-441806247/2500000000 : ℝ)*X 1 1+(1092846217/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288310827/10000000000 : ℝ)*X 2 0+(5464231103/10000000000 : ℝ)*X 2 1+(-13806443/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4278083479/10000000000 : ℝ)*X 0 0+(4591394341/10000000000 : ℝ)*X 0 1+(248981757/625000000 : ℝ)*X 0 2+(4278083479/10000000000 : ℝ)*X 1 0+(4591394341/10000000000 : ℝ)*X 1 1+(248981757/625000000 : ℝ)*X 1 2+(4278083479/10000000000 : ℝ)*X 2 0+(4591394341/10000000000 : ℝ)*X 2 1+(248981757/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2061637165444826515509231/575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92799759/50000000000000 : ℝ)*(base19) + (4501057/2000000000000 : ℝ)*(base23) + (72277547/100000000000000 : ℝ)*(lower2) + (42622247/100000000000000 : ℝ)*(upper3) + (98081201/100000000000000 : ℝ)*(upper5) + (131139024086729/5000000000000 : ℝ)*(major0) + (131139024086729/5000000000000 : ℝ)*(major1) + (131139024086729/5000000000000 : ℝ)*(major2) + (226324163120919/6250000000000 : ℝ)*(sp0) + (3621190896442697/100000000000000 : ℝ)*(sp1) + (724238171397873/20000000000000 : ℝ)*(sp2) + (1624367188999463/100000000000000 : ℝ)*(sp3) + (4472107511/100000000000000 : ℝ)*(sp4) + (1286456137/50000000000000 : ℝ)*(sp7) + (1624369761911737/100000000000000 : ℝ)*(f.failure) + (724238216408443/20000000000000 : ℝ)*(f.sum) + (9022352491/2875000000000000000000000 : ℝ)*base65 + (9979174535790641/1150000000000000000000000000000 : ℝ)*base68 + (17519959817740641/1150000000000000000000000000000 : ℝ)*base70 + (15059219195640641/1150000000000000000000000000000 : ℝ)*base72 + (14264153963/23000000000000000000000000 : ℝ)*base73 + (20951084802190641/1150000000000000000000000000000 : ℝ)*base76 + (9514406227540641/1150000000000000000000000000000 : ℝ)*base78 + (15283017910340641/1150000000000000000000000000000 : ℝ)*base80 + (17203182873/2875000000000000000000000 : ℝ)*base82 + (67506513/5000000000000000000000 : ℝ)*base89 + (67506513/5000000000000000000000 : ℝ)*base91 + (67506513/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (650754295656050571130760901/66125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (683683329/50000000000000 : ℝ)*(base19) + (1640237503/100000000000000 : ℝ)*(base23) + (87280571/50000000000000 : ℝ)*(upper3) + (46120873/100000000000000 : ℝ)*(lower4) + (60348269/25000000000000 : ℝ)*(upper5) + (664259148390533/25000000000000 : ℝ)*(major0) + (664259148390533/25000000000000 : ℝ)*(major1) + (664259148390533/25000000000000 : ℝ)*(major2) + (15895191813/100000000000000 : ℝ)*(sp1) + (19989723027/100000000000000 : ℝ)*(sp2) + (3668487218601137/100000000000000 : ℝ)*(sp4) + (1834234978021333/50000000000000 : ℝ)*(sp5) + (3668465588640607/100000000000000 : ℝ)*(sp6) + (1645585640480629/100000000000000 : ℝ)*(sp7) + (1645585640480629/100000000000000 : ℝ)*(f.failure) + (3668487218601137/100000000000000 : ℝ)*(f.sum) + (248902684221/264500000000000000000000000 : ℝ)*base66 + (1236689639139096011/132250000000000000000000000000000 : ℝ)*base68 + (147268914311846011/132250000000000000000000000000000 : ℝ)*base70 + (359102203576346011/132250000000000000000000000000000 : ℝ)*base72 + (2113450507371/529000000000000000000000000 : ℝ)*base74 + (1178712451342596011/132250000000000000000000000000000 : ℝ)*base76 + (620317925988096011/132250000000000000000000000000000 : ℝ)*base78 + (1029584876416096011/132250000000000000000000000000000 : ℝ)*base80 + (1489418161471/264500000000000000000000000 : ℝ)*base81 + (20104621/5000000000000000000000 : ℝ)*base89 + (20104621/5000000000000000000000 : ℝ)*base91 + (20104621/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1488_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9301/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4011/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10253/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3219/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1488_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1488_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10253/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3219/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1488_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1488_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1488_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10253/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3219/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1488_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
