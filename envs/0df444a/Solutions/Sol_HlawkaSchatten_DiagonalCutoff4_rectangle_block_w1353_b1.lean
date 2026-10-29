-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1353_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:08:07.105257+00:00
-- url     : https://prove2.me/submissions/b5a28383-6684-44a1-b81e-04cb6fccdfb3

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
theorem support_rectangle_w1353_s3_0 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1016427849/5000000000 : ℝ)*x 0 + (5425781339/10000000000 : ℝ)*x 1 + (261619127/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1016427849/5000000000 : ℝ)^4313 ≤ (12379179738953/100000000000000 : ℝ)^3289 := by
    have hnat : (1016427849 : ℕ)^4313*100000000000000^3289 ≤ 12379179738953^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016427849 5000000000 12379179738953 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425781339/10000000000 : ℝ)^4313 ≤ (5606599938839/12500000000000 : ℝ)^3289 := by
    have hnat : (5425781339 : ℕ)^4313*12500000000000^3289 ≤ 5606599938839^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425781339 10000000000 5606599938839 12500000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261619127/500000000 : ℝ)^4313 ≤ (2673001295951/6250000000000 : ℝ)^3289 := by
    have hnat : (261619127 : ℕ)^4313*6250000000000^3289 ≤ 2673001295951^3289*500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261619127 500000000 2673001295951 6250000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1016427849/5000000000 : ℝ), (5425781339/10000000000 : ℝ), (261619127/500000000 : ℝ)] ![(12379179738953/100000000000000 : ℝ), (5606599938839/12500000000000 : ℝ), (2673001295951/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1016427849/5000000000 : ℝ)|^4313 ≤ (12379179738953/100000000000000 : ℝ)^3289
        have hw : |(-1016427849/5000000000 : ℝ)|=(1016427849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425781339/10000000000 : ℝ)|^4313 ≤ (5606599938839/12500000000000 : ℝ)^3289
        have hw : |(5425781339/10000000000 : ℝ)|=(5425781339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261619127/500000000 : ℝ)|^4313 ≤ (2673001295951/6250000000000 : ℝ)^3289
        have hw : |(261619127/500000000 : ℝ)|=(261619127/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s3_1 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676145321/5000000000 : ℝ)*x 0 + (-1065834837/5000000000 : ℝ)*x 1 + (5232382227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676145321/5000000000 : ℝ)^4313 ≤ (44057820492211/100000000000000 : ℝ)^3289 := by
    have hnat : (2676145321 : ℕ)^4313*100000000000000^3289 ≤ 44057820492211^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676145321 5000000000 44057820492211 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1065834837/5000000000 : ℝ)^4313 ≤ (2634832422897/20000000000000 : ℝ)^3289 := by
    have hnat : (1065834837 : ℕ)^4313*20000000000000^3289 ≤ 2634832422897^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065834837 5000000000 2634832422897 20000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5232382227/10000000000 : ℝ)^4313 ≤ (10692004345079/25000000000000 : ℝ)^3289 := by
    have hnat : (5232382227 : ℕ)^4313*25000000000000^3289 ≤ 10692004345079^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232382227 10000000000 10692004345079 25000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676145321/5000000000 : ℝ), (-1065834837/5000000000 : ℝ), (5232382227/10000000000 : ℝ)] ![(44057820492211/100000000000000 : ℝ), (2634832422897/20000000000000 : ℝ), (10692004345079/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676145321/5000000000 : ℝ)|^4313 ≤ (44057820492211/100000000000000 : ℝ)^3289
        have hw : |(2676145321/5000000000 : ℝ)|=(2676145321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1065834837/5000000000 : ℝ)|^4313 ≤ (2634832422897/20000000000000 : ℝ)^3289
        have hw : |(-1065834837/5000000000 : ℝ)|=(1065834837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5232382227/10000000000 : ℝ)|^4313 ≤ (10692004345079/25000000000000 : ℝ)^3289
        have hw : |(5232382227/10000000000 : ℝ)|=(5232382227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s3_2 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352290083/10000000000 : ℝ)*x 0 + (163511929/312500000 : ℝ)*x 1 + (-2131671079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352290083/10000000000 : ℝ)^4313 ≤ (5507226807267/12500000000000 : ℝ)^3289 := by
    have hnat : (5352290083 : ℕ)^4313*12500000000000^3289 ≤ 5507226807267^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352290083 10000000000 5507226807267 12500000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163511929/312500000 : ℝ)^4313 ≤ (4276801203177/10000000000000 : ℝ)^3289 := by
    have hnat : (163511929 : ℕ)^4313*10000000000000^3289 ≤ 4276801203177^3289*312500000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163511929 312500000 4276801203177 10000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2131671079/10000000000 : ℝ)^4313 ≤ (13174173501111/100000000000000 : ℝ)^3289 := by
    have hnat : (2131671079 : ℕ)^4313*100000000000000^3289 ≤ 13174173501111^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131671079 10000000000 13174173501111 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352290083/10000000000 : ℝ), (163511929/312500000 : ℝ), (-2131671079/10000000000 : ℝ)] ![(5507226807267/12500000000000 : ℝ), (4276801203177/10000000000000 : ℝ), (13174173501111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352290083/10000000000 : ℝ)|^4313 ≤ (5507226807267/12500000000000 : ℝ)^3289
        have hw : |(5352290083/10000000000 : ℝ)|=(5352290083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163511929/312500000 : ℝ)|^4313 ≤ (4276801203177/10000000000000 : ℝ)^3289
        have hw : |(163511929/312500000 : ℝ)|=(163511929/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2131671079/10000000000 : ℝ)|^4313 ≤ (13174173501111/100000000000000 : ℝ)^3289
        have hw : |(-2131671079/10000000000 : ℝ)|=(2131671079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s3_3 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4322752701/10000000000 : ℝ)*x 0 + (4123815607/10000000000 : ℝ)*x 1 + (4530581807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322752701/10000000000 : ℝ)^4313 ≤ (33293367716291/100000000000000 : ℝ)^3289 := by
    have hnat : (4322752701 : ℕ)^4313*100000000000000^3289 ≤ 33293367716291^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322752701 10000000000 33293367716291 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4123815607/10000000000 : ℝ)^4313 ≤ (6259738310663/20000000000000 : ℝ)^3289 := by
    have hnat : (4123815607 : ℕ)^4313*20000000000000^3289 ≤ 6259738310663^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4123815607 10000000000 6259738310663 20000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4530581807/10000000000 : ℝ)^4313 ≤ (35407940709433/100000000000000 : ℝ)^3289 := by
    have hnat : (4530581807 : ℕ)^4313*100000000000000^3289 ≤ 35407940709433^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530581807 10000000000 35407940709433 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322752701/10000000000 : ℝ), (4123815607/10000000000 : ℝ), (4530581807/10000000000 : ℝ)] ![(33293367716291/100000000000000 : ℝ), (6259738310663/20000000000000 : ℝ), (35407940709433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322752701/10000000000 : ℝ)|^4313 ≤ (33293367716291/100000000000000 : ℝ)^3289
        have hw : |(4322752701/10000000000 : ℝ)|=(4322752701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4123815607/10000000000 : ℝ)|^4313 ≤ (6259738310663/20000000000000 : ℝ)^3289
        have hw : |(4123815607/10000000000 : ℝ)|=(4123815607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4530581807/10000000000 : ℝ)|^4313 ≤ (35407940709433/100000000000000 : ℝ)^3289
        have hw : |(4530581807/10000000000 : ℝ)|=(4530581807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s3_4 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-203287453/1000000000 : ℝ)*x 0 + (5233182987/10000000000 : ℝ)*x 1 + (678121997/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (203287453/1000000000 : ℝ)^4313 ≤ (12379330121687/100000000000000 : ℝ)^3289 := by
    have hnat : (203287453 : ℕ)^4313*100000000000000^3289 ≤ 12379330121687^3289*1000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203287453 1000000000 12379330121687 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5233182987/10000000000 : ℝ)^4313 ≤ (342212804441/800000000000 : ℝ)^3289 := by
    have hnat : (5233182987 : ℕ)^4313*800000000000^3289 ≤ 342212804441^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233182987 10000000000 342212804441 800000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678121997/1250000000 : ℝ)^4313 ≤ (8968813860949/20000000000000 : ℝ)^3289 := by
    have hnat : (678121997 : ℕ)^4313*20000000000000^3289 ≤ 8968813860949^3289*1250000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678121997 1250000000 8968813860949 20000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-203287453/1000000000 : ℝ), (5233182987/10000000000 : ℝ), (678121997/1250000000 : ℝ)] ![(12379330121687/100000000000000 : ℝ), (342212804441/800000000000 : ℝ), (8968813860949/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-203287453/1000000000 : ℝ)|^4313 ≤ (12379330121687/100000000000000 : ℝ)^3289
        have hw : |(-203287453/1000000000 : ℝ)|=(203287453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5233182987/10000000000 : ℝ)|^4313 ≤ (342212804441/800000000000 : ℝ)^3289
        have hw : |(5233182987/10000000000 : ℝ)|=(5233182987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678121997/1250000000 : ℝ)|^4313 ≤ (8968813860949/20000000000000 : ℝ)^3289
        have hw : |(678121997/1250000000 : ℝ)|=(678121997/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s3_5 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060482241/2000000000 : ℝ)*x 0 + (-484769053/2500000000 : ℝ)*x 1 + (1356244103/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060482241/2000000000 : ℝ)^4313 ≤ (4352018418501/10000000000000 : ℝ)^3289 := by
    have hnat : (1060482241 : ℕ)^4313*10000000000000^3289 ≤ 4352018418501^3289*2000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060482241 2000000000 4352018418501 10000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (484769053/2500000000 : ℝ)^4313 ≤ (9090423261/78125000000 : ℝ)^3289 := by
    have hnat : (484769053 : ℕ)^4313*78125000000^3289 ≤ 9090423261^3289*2500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484769053 2500000000 9090423261 78125000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356244103/2500000000 : ℝ)^4313 ≤ (8968814806183/20000000000000 : ℝ)^3289 := by
    have hnat : (1356244103 : ℕ)^4313*20000000000000^3289 ≤ 8968814806183^3289*2500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356244103 2500000000 8968814806183 20000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060482241/2000000000 : ℝ), (-484769053/2500000000 : ℝ), (1356244103/2500000000 : ℝ)] ![(4352018418501/10000000000000 : ℝ), (9090423261/78125000000 : ℝ), (8968814806183/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060482241/2000000000 : ℝ)|^4313 ≤ (4352018418501/10000000000000 : ℝ)^3289
        have hw : |(1060482241/2000000000 : ℝ)|=(1060482241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-484769053/2500000000 : ℝ)|^4313 ≤ (9090423261/78125000000 : ℝ)^3289
        have hw : |(-484769053/2500000000 : ℝ)|=(484769053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356244103/2500000000 : ℝ)|^4313 ≤ (8968814806183/20000000000000 : ℝ)^3289
        have hw : |(1356244103/2500000000 : ℝ)|=(1356244103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s3_6 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530241227/1000000000 : ℝ)*x 0 + (5424975701/10000000000 : ℝ)*x 1 + (-387815147/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530241227/1000000000 : ℝ)^4313 ≤ (21760097823797/50000000000000 : ℝ)^3289 := by
    have hnat : (530241227 : ℕ)^4313*50000000000000^3289 ≤ 21760097823797^3289*1000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530241227 1000000000 21760097823797 50000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424975701/10000000000 : ℝ)^4313 ≤ (4484406632379/10000000000000 : ℝ)^3289 := by
    have hnat : (5424975701 : ℕ)^4313*10000000000000^3289 ≤ 4484406632379^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424975701 10000000000 4484406632379 10000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387815147/2000000000 : ℝ)^4313 ≤ (11635738020609/100000000000000 : ℝ)^3289 := by
    have hnat : (387815147 : ℕ)^4313*100000000000000^3289 ≤ 11635738020609^3289*2000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387815147 2000000000 11635738020609 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530241227/1000000000 : ℝ), (5424975701/10000000000 : ℝ), (-387815147/2000000000 : ℝ)] ![(21760097823797/50000000000000 : ℝ), (4484406632379/10000000000000 : ℝ), (11635738020609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530241227/1000000000 : ℝ)|^4313 ≤ (21760097823797/50000000000000 : ℝ)^3289
        have hw : |(530241227/1000000000 : ℝ)|=(530241227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424975701/10000000000 : ℝ)|^4313 ≤ (4484406632379/10000000000000 : ℝ)^3289
        have hw : |(5424975701/10000000000 : ℝ)|=(5424975701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-387815147/2000000000 : ℝ)|^4313 ≤ (11635738020609/100000000000000 : ℝ)^3289
        have hw : |(-387815147/2000000000 : ℝ)|=(387815147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s3_7 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (432279207/1000000000 : ℝ)*x 0 + (2264448799/5000000000 : ℝ)*x 1 + (825101943/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432279207/1000000000 : ℝ)^4313 ≤ (2080860333501/6250000000000 : ℝ)^3289 := by
    have hnat : (432279207 : ℕ)^4313*6250000000000^3289 ≤ 2080860333501^3289*1000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432279207 1000000000 2080860333501 6250000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264448799/5000000000 : ℝ)^4313 ≤ (1415627240563/4000000000000 : ℝ)^3289 := by
    have hnat : (2264448799 : ℕ)^4313*4000000000000^3289 ≤ 1415627240563^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264448799 5000000000 1415627240563 4000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (825101943/2000000000 : ℝ)^4313 ≤ (31315553642901/100000000000000 : ℝ)^3289 := by
    have hnat : (825101943 : ℕ)^4313*100000000000000^3289 ≤ 31315553642901^3289*2000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825101943 2000000000 31315553642901 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(432279207/1000000000 : ℝ), (2264448799/5000000000 : ℝ), (825101943/2000000000 : ℝ)] ![(2080860333501/6250000000000 : ℝ), (1415627240563/4000000000000 : ℝ), (31315553642901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(432279207/1000000000 : ℝ)|^4313 ≤ (2080860333501/6250000000000 : ℝ)^3289
        have hw : |(432279207/1000000000 : ℝ)|=(432279207/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2264448799/5000000000 : ℝ)|^4313 ≤ (1415627240563/4000000000000 : ℝ)^3289
        have hw : |(2264448799/5000000000 : ℝ)|=(2264448799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(825101943/2000000000 : ℝ)|^4313 ≤ (31315553642901/100000000000000 : ℝ)^3289
        have hw : |(825101943/2000000000 : ℝ)|=(825101943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1353_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155162223/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9923/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5453/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14999/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16061/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9923/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16061/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9923/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16061/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9923/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16061/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9923/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16061/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9923/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16061/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9923/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9923/100000 : ℝ) ^ (539/128 : ℝ) ≤ (595561131573949/10000000000000000000 : ℝ) := by
    have hpowers : (9923/100000 : ℝ)^539 ≤ (595561131573949/10000000000000000000 : ℝ)^128 := by
      have hnat : (9923 : ℕ)^539*10000000000000000000^128 ≤ 595561131573949^128*100000^539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9923 100000 595561131573949 10000000000000000000 539 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9923/100000 : ℝ)) (X := (595561131573949/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hpowhi : (16061/100000 : ℝ) ^ (539/128 : ℝ) ≤ (45243686291028729/100000000000000000000 : ℝ) := by
    have hpowers : (16061/100000 : ℝ)^539 ≤ (45243686291028729/100000000000000000000 : ℝ)^128 := by
      have hnat : (16061 : ℕ)^539*100000000000000000000^128 ≤ 45243686291028729^128*100000^539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16061 100000 45243686291028729 100000000000000000000 539 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16061/100000 : ℝ)) (X := (45243686291028729/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000595561131573949/5000000000000000000 : ℝ) ≤ (2500070712767323/2500000000000000 : ℝ) ^ (539/128 : ℝ) := by
    have hpowers : (5000595561131573949/5000000000000000000 : ℝ)^128 ≤ (2500070712767323/2500000000000000 : ℝ)^539 := by
      have hnat : (5000595561131573949 : ℕ)^128*2500000000000000^539 ≤ 2500070712767323^539*5000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000595561131573949 5000000000000000000 2500070712767323 2500000000000000 128 539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500070712767323/2500000000000000 : ℝ)) (X := (5000595561131573949/5000000000000000000 : ℝ)) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051199297606768219/100000000000000000000 : ℝ) ≤ (1250151953414003/1250000000000000 : ℝ) ^ (539/128 : ℝ) := by
    have hpowers : (100051199297606768219/100000000000000000000 : ℝ)^128 ≤ (1250151953414003/1250000000000000 : ℝ)^539 := by
      have hnat : (100051199297606768219 : ℕ)^128*1250000000000000^539 ≤ 1250151953414003^539*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051199297606768219 100000000000000000000 1250151953414003 1250000000000000 128 539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250151953414003/1250000000000000 : ℝ)) (X := (100051199297606768219/100000000000000000000 : ℝ)) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50045243686291028729/50000000000000000000 : ℝ) ≤ (2500537100888689/2500000000000000 : ℝ) ^ (539/128 : ℝ) := by
    have hpowers : (50045243686291028729/50000000000000000000 : ℝ)^128 ≤ (2500537100888689/2500000000000000 : ℝ)^539 := by
      have hnat : (50045243686291028729 : ℕ)^128*2500000000000000^539 ≤ 2500537100888689^539*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50045243686291028729 50000000000000000000 2500537100888689 2500000000000000 128 539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500537100888689/2500000000000000 : ℝ)) (X := (50045243686291028729/50000000000000000000 : ℝ)) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(595561131573949/10000000000000000000 : ℝ) ≤ ((426133501823264271/426250000000000000 : ℝ)+2*(25910451187/17050000000000 : ℝ)*(9923/100000 : ℝ))^(539/128 : ℝ) := by
    rw [show (426133501823264271/426250000000000000 : ℝ)+2*(25910451187/17050000000000 : ℝ)*(9923/100000 : ℝ)=(2500070712767323/2500000000000000 : ℝ) by norm_num, show 1+2*(595561131573949/10000000000000000000 : ℝ)=(5000595561131573949/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(45243686291028729/100000000000000000000 : ℝ)+(595561131573949/10000000000000000000 : ℝ) ≤ ((426133501823264271/426250000000000000 : ℝ)+(25910451187/17050000000000 : ℝ)*((16061/100000 : ℝ)+(9923/100000 : ℝ)))^(539/128 : ℝ) := by
    rw [show (426133501823264271/426250000000000000 : ℝ)+(25910451187/17050000000000 : ℝ)*((16061/100000 : ℝ)+(9923/100000 : ℝ))=(1250151953414003/1250000000000000 : ℝ) by norm_num, show 1+(45243686291028729/100000000000000000000 : ℝ)+(595561131573949/10000000000000000000 : ℝ)=(100051199297606768219/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(45243686291028729/100000000000000000000 : ℝ) ≤ ((426133501823264271/426250000000000000 : ℝ)+2*(25910451187/17050000000000 : ℝ)*(16061/100000 : ℝ))^(539/128 : ℝ) := by
    rw [show (426133501823264271/426250000000000000 : ℝ)+2*(25910451187/17050000000000 : ℝ)*(16061/100000 : ℝ)=(2500537100888689/2500000000000000 : ℝ) by norm_num, show 1+2*(45243686291028729/100000000000000000000 : ℝ)=(50045243686291028729/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (426133501823264271/426250000000000000 : ℝ)*(X 1 0+X 2 0)+(25910451187/17050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (539/128 : ℝ)) (lo := (9923/100000 : ℝ)) (hi := (16061/100000 : ℝ)) (c := (426133501823264271/426250000000000000 : ℝ)) (alpha := (25910451187/17050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (426133501823264271/426250000000000000 : ℝ)*(X 0 1+X 2 1)+(25910451187/17050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (539/128 : ℝ)) (lo := (9923/100000 : ℝ)) (hi := (16061/100000 : ℝ)) (c := (426133501823264271/426250000000000000 : ℝ)) (alpha := (25910451187/17050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (426133501823264271/426250000000000000 : ℝ)*(X 0 2+X 1 2)+(25910451187/17050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (539/128 : ℝ)) (lo := (9923/100000 : ℝ)) (hi := (16061/100000 : ℝ)) (c := (426133501823264271/426250000000000000 : ℝ)) (alpha := (25910451187/17050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1016427849/5000000000 : ℝ)*X 0 0+(5425781339/10000000000 : ℝ)*X 0 1+(261619127/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676145321/5000000000 : ℝ)*X 1 0+(-1065834837/5000000000 : ℝ)*X 1 1+(5232382227/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352290083/10000000000 : ℝ)*X 2 0+(163511929/312500000 : ℝ)*X 2 1+(-2131671079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4322752701/10000000000 : ℝ)*X 0 0+(4123815607/10000000000 : ℝ)*X 0 1+(4530581807/10000000000 : ℝ)*X 0 2+(4322752701/10000000000 : ℝ)*X 1 0+(4123815607/10000000000 : ℝ)*X 1 1+(4530581807/10000000000 : ℝ)*X 1 2+(4322752701/10000000000 : ℝ)*X 2 0+(4123815607/10000000000 : ℝ)*X 2 1+(4530581807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-203287453/1000000000 : ℝ)*X 0 0+(5233182987/10000000000 : ℝ)*X 0 1+(678121997/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060482241/2000000000 : ℝ)*X 1 0+(-484769053/2500000000 : ℝ)*X 1 1+(1356244103/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530241227/1000000000 : ℝ)*X 2 0+(5424975701/10000000000 : ℝ)*X 2 1+(-387815147/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((432279207/1000000000 : ℝ)*X 0 0+(2264448799/5000000000 : ℝ)*X 0 1+(825101943/2000000000 : ℝ)*X 0 2+(432279207/1000000000 : ℝ)*X 1 0+(2264448799/5000000000 : ℝ)*X 1 1+(825101943/2000000000 : ℝ)*X 1 2+(432279207/1000000000 : ℝ)*X 2 0+(2264448799/5000000000 : ℝ)*X 2 1+(825101943/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15122045013764609506431/1705000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1762414571/100000000000000 : ℝ)*(base19) + (411484237/25000000000000 : ℝ)*(base23) + (35993417/6250000000000 : ℝ)*(upper3) + (12236957/4000000000000 : ℝ)*(lower4) + (3814572291378161/100000000000000 : ℝ)*(major0) + (3814572291378161/100000000000000 : ℝ)*(major1) + (3814572291378161/100000000000000 : ℝ)*(major2) + (161584299609213/3125000000000 : ℝ)*(sp0) + (2585350573955619/50000000000000 : ℝ)*(sp1) + (2585342690393371/50000000000000 : ℝ)*(sp2) + (1229213182608393/50000000000000 : ℝ)*(sp3) + (2661415497/50000000000000 : ℝ)*(sp4) + (397090053/2500000000000 : ℝ)*(sp6) + (3002314513/20000000000000 : ℝ)*(sp7) + (49168827535787/2000000000000 : ℝ)*(f.failure) + (5170702910325809/100000000000000 : ℝ)*(f.sum) + (3231741084063/852500000000000000000000000 : ℝ)*base66 + (286778095125589369/42625000000000000000000000000000 : ℝ)*base68 + (356933661371464369/42625000000000000000000000000000 : ℝ)*base70 + (255781989702160631/42625000000000000000000000000000 : ℝ)*base71 + (3651705952793/852500000000000000000000000 : ℝ)*base74 + (259097576563285631/42625000000000000000000000000000 : ℝ)*base75 + (92253001978410631/42625000000000000000000000000000 : ℝ)*base77 + (438881085194839369/42625000000000000000000000000000 : ℝ)*base80 + (17081598668381/1705000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (974501/200000000000000000000 : ℝ)*base89 + (974501/200000000000000000000 : ℝ)*base91 + (974501/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22379919881353624338365853/10656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (116397029/20000000000000 : ℝ)*(base19) + (450913279/20000000000000 : ℝ)*(base23) + (245222053/100000000000000 : ℝ)*(upper3) + (202739951/100000000000000 : ℝ)*(lower4) + (94236829/50000000000000 : ℝ)*(upper5) + (1923241063350777/50000000000000 : ℝ)*(major0) + (1923241063350777/50000000000000 : ℝ)*(major1) + (1923241063350777/50000000000000 : ℝ)*(major2) + (6447911813/50000000000000 : ℝ)*(sp1) + (19364204149/50000000000000 : ℝ)*(sp2) + (8342331743831/160000000000 : ℝ)*(sp4) + (1042788772417121/20000000000000 : ℝ)*(sp5) + (2606958178459841/50000000000000 : ℝ)*(sp6) + (2479006843503109/100000000000000 : ℝ)*(sp7) + (2479006843503109/100000000000000 : ℝ)*(f.failure) + (8342331743831/160000000000 : ℝ)*(f.sum) + (1689410372801/426250000000000000000000000 : ℝ)*base66 + (167060782366273933/21312500000000000000000000000000 : ℝ)*base68 + (172791897500523933/21312500000000000000000000000000 : ℝ)*base70 + (358654344168773933/21312500000000000000000000000000 : ℝ)*base72 + (5727746981303/852500000000000000000000000 : ℝ)*base73 + (187845115778148933/21312500000000000000000000000000 : ℝ)*base76 + (232017492939836433/21312500000000000000000000000000 : ℝ)*base78 + (197120527006336433/21312500000000000000000000000000 : ℝ)*base80 + (4667477290519/1705000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (99851307/10000000000000000000000 : ℝ)*base89 + (99851307/10000000000000000000000 : ℝ)*base91 + (99851307/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1353_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155162223/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9923/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5453/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14999/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1353_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1353_s4_0 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-63569759/312500000 : ℝ)*x 0 + (2707253091/5000000000 : ℝ)*x 1 + (1310688313/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63569759/312500000 : ℝ)^4313 ≤ (12390173626343/100000000000000 : ℝ)^3289 := by
    have hnat : (63569759 : ℕ)^4313*100000000000000^3289 ≤ 12390173626343^3289*312500000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63569759 312500000 12390173626343 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707253091/5000000000 : ℝ)^4313 ≤ (44730612548273/100000000000000 : ℝ)^3289 := by
    have hnat : (2707253091 : ℕ)^4313*100000000000000^3289 ≤ 44730612548273^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707253091 5000000000 44730612548273 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310688313/2500000000 : ℝ)^4313 ≤ (42879213809923/100000000000000 : ℝ)^3289 := by
    have hnat : (1310688313 : ℕ)^4313*100000000000000^3289 ≤ 42879213809923^3289*2500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310688313 2500000000 42879213809923 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-63569759/312500000 : ℝ), (2707253091/5000000000 : ℝ), (1310688313/2500000000 : ℝ)] ![(12390173626343/100000000000000 : ℝ), (44730612548273/100000000000000 : ℝ), (42879213809923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-63569759/312500000 : ℝ)|^4313 ≤ (12390173626343/100000000000000 : ℝ)^3289
        have hw : |(-63569759/312500000 : ℝ)|=(63569759/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707253091/5000000000 : ℝ)|^4313 ≤ (44730612548273/100000000000000 : ℝ)^3289
        have hw : |(2707253091/5000000000 : ℝ)|=(2707253091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310688313/2500000000 : ℝ)|^4313 ≤ (42879213809923/100000000000000 : ℝ)^3289
        have hw : |(1310688313/2500000000 : ℝ)|=(1310688313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s4_1 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349411893/10000000000 : ℝ)*x 0 + (-2121775259/10000000000 : ℝ)*x 1 + (5242753741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349411893/10000000000 : ℝ)^4313 ≤ (5503343587207/12500000000000 : ℝ)^3289 := by
    have hnat : (5349411893 : ℕ)^4313*12500000000000^3289 ≤ 5503343587207^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349411893 10000000000 5503343587207 12500000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2121775259/10000000000 : ℝ)^4313 ≤ (3273508056011/25000000000000 : ℝ)^3289 := by
    have hnat : (2121775259 : ℕ)^4313*25000000000000^3289 ≤ 3273508056011^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121775259 10000000000 3273508056011 25000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242753741/10000000000 : ℝ)^4313 ≤ (10719804763629/25000000000000 : ℝ)^3289 := by
    have hnat : (5242753741 : ℕ)^4313*25000000000000^3289 ≤ 10719804763629^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242753741 10000000000 10719804763629 25000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349411893/10000000000 : ℝ), (-2121775259/10000000000 : ℝ), (5242753741/10000000000 : ℝ)] ![(5503343587207/12500000000000 : ℝ), (3273508056011/25000000000000 : ℝ), (10719804763629/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349411893/10000000000 : ℝ)|^4313 ≤ (5503343587207/12500000000000 : ℝ)^3289
        have hw : |(5349411893/10000000000 : ℝ)|=(5349411893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2121775259/10000000000 : ℝ)|^4313 ≤ (3273508056011/25000000000000 : ℝ)^3289
        have hw : |(-2121775259/10000000000 : ℝ)|=(2121775259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242753741/10000000000 : ℝ)|^4313 ≤ (10719804763629/25000000000000 : ℝ)^3289
        have hw : |(5242753741/10000000000 : ℝ)|=(5242753741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s4_2 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349411453/10000000000 : ℝ)*x 0 + (209710163/400000000 : ℝ)*x 1 + (-424355081/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349411453/10000000000 : ℝ)^4313 ≤ (44026743948911/100000000000000 : ℝ)^3289 := by
    have hnat : (5349411453 : ℕ)^4313*100000000000000^3289 ≤ 44026743948911^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349411453 10000000000 44026743948911 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209710163/400000000 : ℝ)^4313 ≤ (42879222636713/100000000000000 : ℝ)^3289 := by
    have hnat : (209710163 : ℕ)^4313*100000000000000^3289 ≤ 42879222636713^3289*400000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209710163 400000000 42879222636713 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424355081/2000000000 : ℝ)^4313 ≤ (102297135981/781250000000 : ℝ)^3289 := by
    have hnat : (424355081 : ℕ)^4313*781250000000^3289 ≤ 102297135981^3289*2000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424355081 2000000000 102297135981 781250000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349411453/10000000000 : ℝ), (209710163/400000000 : ℝ), (-424355081/2000000000 : ℝ)] ![(44026743948911/100000000000000 : ℝ), (42879222636713/100000000000000 : ℝ), (102297135981/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349411453/10000000000 : ℝ)|^4313 ≤ (44026743948911/100000000000000 : ℝ)^3289
        have hw : |(5349411453/10000000000 : ℝ)|=(5349411453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209710163/400000000 : ℝ)|^4313 ≤ (42879222636713/100000000000000 : ℝ)^3289
        have hw : |(209710163/400000000 : ℝ)|=(209710163/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-424355081/2000000000 : ℝ)|^4313 ≤ (102297135981/781250000000 : ℝ)^3289
        have hw : |(-424355081/2000000000 : ℝ)|=(424355081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s4_3 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540448589/1250000000 : ℝ)*x 0 + (829295341/2000000000 : ℝ)*x 1 + (281732131/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540448589/1250000000 : ℝ)^4313 ≤ (33301811517249/100000000000000 : ℝ)^3289 := by
    have hnat : (540448589 : ℕ)^4313*100000000000000^3289 ≤ 33301811517249^3289*1250000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540448589 1250000000 33301811517249 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (829295341/2000000000 : ℝ)^4313 ≤ (15762212097299/50000000000000 : ℝ)^3289 := by
    have hnat : (829295341 : ℕ)^4313*50000000000000^3289 ≤ 15762212097299^3289*2000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829295341 2000000000 15762212097299 50000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281732131/625000000 : ℝ)^4313 ≤ (4396720533489/12500000000000 : ℝ)^3289 := by
    have hnat : (281732131 : ℕ)^4313*12500000000000^3289 ≤ 4396720533489^3289*625000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281732131 625000000 4396720533489 12500000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540448589/1250000000 : ℝ), (829295341/2000000000 : ℝ), (281732131/625000000 : ℝ)] ![(33301811517249/100000000000000 : ℝ), (15762212097299/50000000000000 : ℝ), (4396720533489/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540448589/1250000000 : ℝ)|^4313 ≤ (33301811517249/100000000000000 : ℝ)^3289
        have hw : |(540448589/1250000000 : ℝ)|=(540448589/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(829295341/2000000000 : ℝ)|^4313 ≤ (15762212097299/50000000000000 : ℝ)^3289
        have hw : |(829295341/2000000000 : ℝ)|=(829295341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(281732131/625000000 : ℝ)|^4313 ≤ (4396720533489/12500000000000 : ℝ)^3289
        have hw : |(281732131/625000000 : ℝ)|=(281732131/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s4_4 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1017122459/5000000000 : ℝ)*x 0 + (5243386029/10000000000 : ℝ)*x 1 + (5413870389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1017122459/5000000000 : ℝ)^4313 ≤ (6195137252141/50000000000000 : ℝ)^3289 := by
    have hnat : (1017122459 : ℕ)^4313*50000000000000^3289 ≤ 6195137252141^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017122459 5000000000 6195137252141 50000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243386029/10000000000 : ℝ)^4313 ≤ (10721500139877/25000000000000 : ℝ)^3289 := by
    have hnat : (5243386029 : ℕ)^4313*25000000000000^3289 ≤ 10721500139877^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243386029 10000000000 10721500139877 25000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413870389/10000000000 : ℝ)^4313 ≤ (44723724925087/100000000000000 : ℝ)^3289 := by
    have hnat : (5413870389 : ℕ)^4313*100000000000000^3289 ≤ 44723724925087^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413870389 10000000000 44723724925087 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1017122459/5000000000 : ℝ), (5243386029/10000000000 : ℝ), (5413870389/10000000000 : ℝ)] ![(6195137252141/50000000000000 : ℝ), (10721500139877/25000000000000 : ℝ), (44723724925087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1017122459/5000000000 : ℝ)|^4313 ≤ (6195137252141/50000000000000 : ℝ)^3289
        have hw : |(-1017122459/5000000000 : ℝ)|=(1017122459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243386029/10000000000 : ℝ)|^4313 ≤ (10721500139877/25000000000000 : ℝ)^3289
        have hw : |(5243386029/10000000000 : ℝ)|=(5243386029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413870389/10000000000 : ℝ)|^4313 ≤ (44723724925087/100000000000000 : ℝ)^3289
        have hw : |(5413870389/10000000000 : ℝ)|=(5413870389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s4_5 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305115881/10000000000 : ℝ)*x 0 + (-975329831/5000000000 : ℝ)*x 1 + (5413870627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305115881/10000000000 : ℝ)^4313 ≤ (8709859378971/20000000000000 : ℝ)^3289 := by
    have hnat : (5305115881 : ℕ)^4313*20000000000000^3289 ≤ 8709859378971^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305115881 10000000000 8709859378971 20000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (975329831/5000000000 : ℝ)^4313 ≤ (2931743897079/25000000000000 : ℝ)^3289 := by
    have hnat : (975329831 : ℕ)^4313*25000000000000^3289 ≤ 2931743897079^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975329831 5000000000 2931743897079 25000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413870627/10000000000 : ℝ)^4313 ≤ (22361863751661/50000000000000 : ℝ)^3289 := by
    have hnat : (5413870627 : ℕ)^4313*50000000000000^3289 ≤ 22361863751661^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413870627 10000000000 22361863751661 50000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305115881/10000000000 : ℝ), (-975329831/5000000000 : ℝ), (5413870627/10000000000 : ℝ)] ![(8709859378971/20000000000000 : ℝ), (2931743897079/25000000000000 : ℝ), (22361863751661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305115881/10000000000 : ℝ)|^4313 ≤ (8709859378971/20000000000000 : ℝ)^3289
        have hw : |(5305115881/10000000000 : ℝ)|=(5305115881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-975329831/5000000000 : ℝ)|^4313 ≤ (2931743897079/25000000000000 : ℝ)^3289
        have hw : |(-975329831/5000000000 : ℝ)|=(975329831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413870627/10000000000 : ℝ)|^4313 ≤ (22361863751661/50000000000000 : ℝ)^3289
        have hw : |(5413870627/10000000000 : ℝ)|=(5413870627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s4_6 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305116339/10000000000 : ℝ)*x 0 + (5413870371/10000000000 : ℝ)*x 1 + (-1950659387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305116339/10000000000 : ℝ)^4313 ≤ (43549301825087/100000000000000 : ℝ)^3289 := by
    have hnat : (5305116339 : ℕ)^4313*100000000000000^3289 ≤ 43549301825087^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305116339 10000000000 43549301825087 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413870371/10000000000 : ℝ)^4313 ≤ (22361862365047/50000000000000 : ℝ)^3289 := by
    have hnat : (5413870371 : ℕ)^4313*50000000000000^3289 ≤ 22361862365047^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413870371 10000000000 22361862365047 50000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1950659387/10000000000 : ℝ)^4313 ≤ (2931743355087/25000000000000 : ℝ)^3289 := by
    have hnat : (1950659387 : ℕ)^4313*25000000000000^3289 ≤ 2931743355087^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950659387 10000000000 2931743355087 25000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305116339/10000000000 : ℝ), (5413870371/10000000000 : ℝ), (-1950659387/10000000000 : ℝ)] ![(43549301825087/100000000000000 : ℝ), (22361862365047/50000000000000 : ℝ), (2931743355087/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305116339/10000000000 : ℝ)|^4313 ≤ (43549301825087/100000000000000 : ℝ)^3289
        have hw : |(5305116339/10000000000 : ℝ)|=(5305116339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413870371/10000000000 : ℝ)|^4313 ≤ (22361862365047/50000000000000 : ℝ)^3289
        have hw : |(5413870371/10000000000 : ℝ)|=(5413870371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1950659387/10000000000 : ℝ)|^4313 ≤ (2931743355087/25000000000000 : ℝ)^3289
        have hw : |(-1950659387/10000000000 : ℝ)|=(1950659387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s4_7 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4323615419/10000000000 : ℝ)*x 0 + (2253192523/5000000000 : ℝ)*x 1 + (2073906793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323615419/10000000000 : ℝ)^4313 ≤ (33302081269199/100000000000000 : ℝ)^3289 := by
    have hnat : (4323615419 : ℕ)^4313*100000000000000^3289 ≤ 33302081269199^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323615419 10000000000 33302081269199 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253192523/5000000000 : ℝ)^4313 ≤ (4395020687917/12500000000000 : ℝ)^3289 := by
    have hnat : (2253192523 : ℕ)^4313*12500000000000^3289 ≤ 4395020687917^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253192523 5000000000 4395020687917 12500000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2073906793/5000000000 : ℝ)^4313 ≤ (31537753209817/100000000000000 : ℝ)^3289 := by
    have hnat : (2073906793 : ℕ)^4313*100000000000000^3289 ≤ 31537753209817^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073906793 5000000000 31537753209817 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323615419/10000000000 : ℝ), (2253192523/5000000000 : ℝ), (2073906793/5000000000 : ℝ)] ![(33302081269199/100000000000000 : ℝ), (4395020687917/12500000000000 : ℝ), (31537753209817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323615419/10000000000 : ℝ)|^4313 ≤ (33302081269199/100000000000000 : ℝ)^3289
        have hw : |(4323615419/10000000000 : ℝ)|=(4323615419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253192523/5000000000 : ℝ)|^4313 ≤ (4395020687917/12500000000000 : ℝ)^3289
        have hw : |(2253192523/5000000000 : ℝ)|=(2253192523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2073906793/5000000000 : ℝ)|^4313 ≤ (31537753209817/100000000000000 : ℝ)^3289
        have hw : |(2073906793/5000000000 : ℝ)|=(2073906793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s4_8 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-32973471/5000000000 : ℝ)*x 0 + (1472054171/2500000000 : ℝ)*x 1 + (2944102639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32973471/5000000000 : ℝ)^4313 ≤ (27621731971/20000000000000 : ℝ)^3289 := by
    have hnat : (32973471 : ℕ)^4313*20000000000000^3289 ≤ 27621731971^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32973471 5000000000 27621731971 20000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1472054171/2500000000 : ℝ)^4313 ≤ (12482752270057/25000000000000 : ℝ)^3289 := by
    have hnat : (1472054171 : ℕ)^4313*25000000000000^3289 ≤ 12482752270057^3289*2500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1472054171 2500000000 12482752270057 25000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2944102639/5000000000 : ℝ)^4313 ≤ (24965441123159/50000000000000 : ℝ)^3289 := by
    have hnat : (2944102639 : ℕ)^4313*50000000000000^3289 ≤ 24965441123159^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2944102639 5000000000 24965441123159 50000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-32973471/5000000000 : ℝ), (1472054171/2500000000 : ℝ), (2944102639/5000000000 : ℝ)] ![(27621731971/20000000000000 : ℝ), (12482752270057/25000000000000 : ℝ), (24965441123159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-32973471/5000000000 : ℝ)|^4313 ≤ (27621731971/20000000000000 : ℝ)^3289
        have hw : |(-32973471/5000000000 : ℝ)|=(32973471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1472054171/2500000000 : ℝ)|^4313 ≤ (12482752270057/25000000000000 : ℝ)^3289
        have hw : |(1472054171/2500000000 : ℝ)|=(1472054171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2944102639/5000000000 : ℝ)|^4313 ≤ (24965441123159/50000000000000 : ℝ)^3289
        have hw : |(2944102639/5000000000 : ℝ)|=(2944102639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1353_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155162223/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5453/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1391/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3691/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5453/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14999/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5453/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5453/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14999/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5453/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5453/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14999/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5453/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5453/50000 : ℝ) ^ (539/128 : ℝ) ≤ (8864812176522879/100000000000000000000 : ℝ) := by
    have hpowers : (5453/50000 : ℝ)^539 ≤ (8864812176522879/100000000000000000000 : ℝ)^128 := by
      have hnat : (5453 : ℕ)^539*100000000000000000000^128 ≤ 8864812176522879^128*50000^539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5453 50000 8864812176522879 100000000000000000000 539 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5453/50000 : ℝ)) (X := (8864812176522879/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14999/100000 : ℝ) ^ (539/128 : ℝ) ≤ (33919532896540967/100000000000000000000 : ℝ) := by
    have hpowers : (14999/100000 : ℝ)^539 ≤ (33919532896540967/100000000000000000000 : ℝ)^128 := by
      have hnat : (14999 : ℕ)^539*100000000000000000000^128 ≤ 33919532896540967^128*100000^539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14999 100000 33919532896540967 100000000000000000000 539 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14999/100000 : ℝ)) (X := (33919532896540967/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008864812176522879/50000000000000000000 : ℝ) ≤ (10000421009003857/10000000000000000 : ℝ) ^ (539/128 : ℝ) := by
    have hpowers : (50008864812176522879/50000000000000000000 : ℝ)^128 ≤ (10000421009003857/10000000000000000 : ℝ)^539 := by
      have hnat : (50008864812176522879 : ℕ)^128*10000000000000000^539 ≤ 10000421009003857^539*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008864812176522879 50000000000000000000 10000421009003857 10000000000000000 128 539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000421009003857/10000000000000000 : ℝ)) (X := (50008864812176522879/50000000000000000000 : ℝ)) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021392172536531923/50000000000000000000 : ℝ) ≤ (5000507931640313/5000000000000000 : ℝ) ^ (539/128 : ℝ) := by
    have hpowers : (50021392172536531923/50000000000000000000 : ℝ)^128 ≤ (5000507931640313/5000000000000000 : ℝ)^539 := by
      have hnat : (50021392172536531923 : ℕ)^128*5000000000000000^539 ≤ 5000507931640313^539*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021392172536531923 50000000000000000000 5000507931640313 5000000000000000 128 539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000507931640313/5000000000000000 : ℝ)) (X := (50021392172536531923/50000000000000000000 : ℝ)) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033919532896540967/50000000000000000000 : ℝ) ≤ (2000322143511479/2000000000000000 : ℝ) ^ (539/128 : ℝ) := by
    have hpowers : (50033919532896540967/50000000000000000000 : ℝ)^128 ≤ (2000322143511479/2000000000000000 : ℝ)^539 := by
      have hnat : (50033919532896540967 : ℕ)^128*2000000000000000^539 ≤ 2000322143511479^539*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033919532896540967 50000000000000000000 2000322143511479 2000000000000000 128 539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000322143511479/2000000000000000 : ℝ)) (X := (50033919532896540967/50000000000000000000 : ℝ)) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8864812176522879/100000000000000000000 : ℝ) ≤ ((40918748228367901273/40930000000000000000 : ℝ)+2*(594854276769/409300000000000 : ℝ)*(5453/50000 : ℝ))^(539/128 : ℝ) := by
    rw [show (40918748228367901273/40930000000000000000 : ℝ)+2*(594854276769/409300000000000 : ℝ)*(5453/50000 : ℝ)=(10000421009003857/10000000000000000 : ℝ) by norm_num, show 1+2*(8864812176522879/100000000000000000000 : ℝ)=(50008864812176522879/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33919532896540967/100000000000000000000 : ℝ)+(8864812176522879/100000000000000000000 : ℝ) ≤ ((40918748228367901273/40930000000000000000 : ℝ)+(594854276769/409300000000000 : ℝ)*((14999/100000 : ℝ)+(5453/50000 : ℝ)))^(539/128 : ℝ) := by
    rw [show (40918748228367901273/40930000000000000000 : ℝ)+(594854276769/409300000000000 : ℝ)*((14999/100000 : ℝ)+(5453/50000 : ℝ))=(5000507931640313/5000000000000000 : ℝ) by norm_num, show 1+(33919532896540967/100000000000000000000 : ℝ)+(8864812176522879/100000000000000000000 : ℝ)=(50021392172536531923/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33919532896540967/100000000000000000000 : ℝ) ≤ ((40918748228367901273/40930000000000000000 : ℝ)+2*(594854276769/409300000000000 : ℝ)*(14999/100000 : ℝ))^(539/128 : ℝ) := by
    rw [show (40918748228367901273/40930000000000000000 : ℝ)+2*(594854276769/409300000000000 : ℝ)*(14999/100000 : ℝ)=(2000322143511479/2000000000000000 : ℝ) by norm_num, show 1+2*(33919532896540967/100000000000000000000 : ℝ)=(50033919532896540967/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (40918748228367901273/40930000000000000000 : ℝ)*(X 1 0+X 2 0)+(594854276769/409300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (539/128 : ℝ)) (lo := (5453/50000 : ℝ)) (hi := (14999/100000 : ℝ)) (c := (40918748228367901273/40930000000000000000 : ℝ)) (alpha := (594854276769/409300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (40918748228367901273/40930000000000000000 : ℝ)*(X 0 1+X 2 1)+(594854276769/409300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (539/128 : ℝ)) (lo := (5453/50000 : ℝ)) (hi := (14999/100000 : ℝ)) (c := (40918748228367901273/40930000000000000000 : ℝ)) (alpha := (594854276769/409300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (40918748228367901273/40930000000000000000 : ℝ)*(X 0 2+X 1 2)+(594854276769/409300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (539/128 : ℝ)) (lo := (5453/50000 : ℝ)) (hi := (14999/100000 : ℝ)) (c := (40918748228367901273/40930000000000000000 : ℝ)) (alpha := (594854276769/409300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-63569759/312500000 : ℝ)*X 0 0+(2707253091/5000000000 : ℝ)*X 0 1+(1310688313/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349411893/10000000000 : ℝ)*X 1 0+(-2121775259/10000000000 : ℝ)*X 1 1+(5242753741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349411453/10000000000 : ℝ)*X 2 0+(209710163/400000000 : ℝ)*X 2 1+(-424355081/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((540448589/1250000000 : ℝ)*X 0 0+(829295341/2000000000 : ℝ)*X 0 1+(281732131/625000000 : ℝ)*X 0 2+(540448589/1250000000 : ℝ)*X 1 0+(829295341/2000000000 : ℝ)*X 1 1+(281732131/625000000 : ℝ)*X 1 2+(540448589/1250000000 : ℝ)*X 2 0+(829295341/2000000000 : ℝ)*X 2 1+(281732131/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1017122459/5000000000 : ℝ)*X 0 0+(5243386029/10000000000 : ℝ)*X 0 1+(5413870389/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305115881/10000000000 : ℝ)*X 1 0+(-975329831/5000000000 : ℝ)*X 1 1+(5413870627/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305116339/10000000000 : ℝ)*X 2 0+(5413870371/10000000000 : ℝ)*X 2 1+(-1950659387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4323615419/10000000000 : ℝ)*X 0 0+(2253192523/5000000000 : ℝ)*X 0 1+(2073906793/5000000000 : ℝ)*X 0 2+(4323615419/10000000000 : ℝ)*X 1 0+(2253192523/5000000000 : ℝ)*X 1 1+(2073906793/5000000000 : ℝ)*X 1 2+(4323615419/10000000000 : ℝ)*X 2 0+(2253192523/5000000000 : ℝ)*X 2 1+(2073906793/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-32973471/5000000000 : ℝ)*X 0 0+(1472054171/2500000000 : ℝ)*X 0 1+(2944102639/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s4_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (836679621832469716971/204650000000000000000000000 : ℝ) := by norm_num
    linear_combination (754237431/100000000000000 : ℝ)*(lower2) + (53901831/20000000000000 : ℝ)*(lower3) + (997985847/100000000000000 : ℝ)*(lower4) + (17769809/6250000000000 : ℝ)*(lower5) + (214765152111527/5000000000000 : ℝ)*(major0) + (214765152111527/5000000000000 : ℝ)*(major1) + (214765152111527/5000000000000 : ℝ)*(major2) + (5822328815753407/100000000000000 : ℝ)*(sp0) + (582233715516619/10000000000000 : ℝ)*(sp1) + (5822339962311781/100000000000000 : ℝ)*(sp2) + (2768265985871149/100000000000000 : ℝ)*(sp3) + (154427141/6250000000000 : ℝ)*(sp4) + (2807145591/100000000000000 : ℝ)*(sp5) + (8675724117/100000000000000 : ℝ)*(sp8) + (2768265985871149/100000000000000 : ℝ)*(f.failure) + (5822339962311781/100000000000000 : ℝ)*(f.sum) + (39778392187801/2046500000000000000000000000 : ℝ)*base65 + (317771228242423871/204650000000000000000000000000000 : ℝ)*base67 + (2859287364899873871/204650000000000000000000000000000 : ℝ)*base69 + (469573571447276129/204650000000000000000000000000000 : ℝ)*base72 + (3170816017903/4093000000000000000000000000 : ℝ)*base73 + (552393425379576129/204650000000000000000000000000000 : ℝ)*base76 + (13576067665700923871/204650000000000000000000000000000 : ℝ)*base77 + (845381205485426129/204650000000000000000000000000000 : ℝ)*base80 + (1813332431829/818600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (70404227/10000000000000000000000 : ℝ)*base89 + (70404227/10000000000000000000000 : ℝ)*base91 + (70404227/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (370648130794398327894290217/25581250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (812331241/100000000000000 : ℝ)*(lower2) + (136950991/100000000000000 : ℝ)*(lower3) + (543684023/100000000000000 : ℝ)*(lower4) + (91556891/100000000000000 : ℝ)*(lower5) + (108181538370957/2500000000000 : ℝ)*(major0) + (108181538370957/2500000000000 : ℝ)*(major1) + (108181538370957/2500000000000 : ℝ)*(major2) + (750833211/100000000000000 : ℝ)*(sp0) + (3786398061/50000000000000 : ℝ)*(sp3) + (5865652923102647/100000000000000 : ℝ)*(sp4) + (1466414943786777/25000000000000 : ℝ)*(sp5) + (1466414943786777/25000000000000 : ℝ)*(sp6) + (1394427619382417/50000000000000 : ℝ)*(sp7) + (6101211251/100000000000000 : ℝ)*(sp8) + (697215702890239/25000000000000 : ℝ)*(f.failure) + (1466414943786777/25000000000000 : ℝ)*(f.sum) + (19020787054929/2046500000000000000000000000 : ℝ)*base66 + (817149527173646739/102325000000000000000000000000000 : ℝ)*base68 + (534218494034403261/102325000000000000000000000000000 : ℝ)*base69 + (135361027454978261/102325000000000000000000000000000 : ℝ)*base71 + (63385324619/409300000000000000000000000 : ℝ)*base74 + (637224765391428261/102325000000000000000000000000000 : ℝ)*base75 + (440558083101178261/102325000000000000000000000000000 : ℝ)*base77 + (595171207217178261/102325000000000000000000000000000 : ℝ)*base79 + (797501220809/255812500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (8241297/2500000000000000000000 : ℝ)*base89 + (8241297/2500000000000000000000 : ℝ)*base91 + (8241297/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1353_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155162223/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14999/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5453/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1391/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1353_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1353_s5_0 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-508615453/2500000000 : ℝ)*x 0 + (676561541/1250000000 : ℝ)*x 1 + (2622308133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (508615453/2500000000 : ℝ)^4313 ≤ (12392006903661/100000000000000 : ℝ)^3289 := by
    have hnat : (508615453 : ℕ)^4313*100000000000000^3289 ≤ 12392006903661^3289*2500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508615453 2500000000 12392006903661 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676561541/1250000000 : ℝ)^4313 ≤ (44708797086517/100000000000000 : ℝ)^3289 := by
    have hnat : (676561541 : ℕ)^4313*100000000000000^3289 ≤ 44708797086517^3289*1250000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676561541 1250000000 44708797086517 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622308133/5000000000 : ℝ)^4313 ≤ (42899196001587/100000000000000 : ℝ)^3289 := by
    have hnat : (2622308133 : ℕ)^4313*100000000000000^3289 ≤ 42899196001587^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622308133 5000000000 42899196001587 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-508615453/2500000000 : ℝ), (676561541/1250000000 : ℝ), (2622308133/5000000000 : ℝ)] ![(12392006903661/100000000000000 : ℝ), (44708797086517/100000000000000 : ℝ), (42899196001587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-508615453/2500000000 : ℝ)|^4313 ≤ (12392006903661/100000000000000 : ℝ)^3289
        have hw : |(-508615453/2500000000 : ℝ)|=(508615453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676561541/1250000000 : ℝ)|^4313 ≤ (44708797086517/100000000000000 : ℝ)^3289
        have hw : |(676561541/1250000000 : ℝ)|=(676561541/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622308133/5000000000 : ℝ)|^4313 ≤ (42899196001587/100000000000000 : ℝ)^3289
        have hw : |(2622308133/5000000000 : ℝ)|=(2622308133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s5_1 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348896761/10000000000 : ℝ)*x 0 + (-423998657/2000000000 : ℝ)*x 1 + (1311154103/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348896761/10000000000 : ℝ)^4313 ≤ (11005297291591/25000000000000 : ℝ)^3289 := by
    have hnat : (5348896761 : ℕ)^4313*25000000000000^3289 ≤ 11005297291591^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348896761 10000000000 11005297291591 25000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423998657/2000000000 : ℝ)^4313 ≤ (817475828503/6250000000000 : ℝ)^3289 := by
    have hnat : (423998657 : ℕ)^4313*6250000000000^3289 ≤ 817475828503^3289*2000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423998657 2000000000 817475828503 6250000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311154103/2500000000 : ℝ)^4313 ≤ (42899197567631/100000000000000 : ℝ)^3289 := by
    have hnat : (1311154103 : ℕ)^4313*100000000000000^3289 ≤ 42899197567631^3289*2500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311154103 2500000000 42899197567631 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348896761/10000000000 : ℝ), (-423998657/2000000000 : ℝ), (1311154103/2500000000 : ℝ)] ![(11005297291591/25000000000000 : ℝ), (817475828503/6250000000000 : ℝ), (42899197567631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348896761/10000000000 : ℝ)|^4313 ≤ (11005297291591/25000000000000 : ℝ)^3289
        have hw : |(5348896761/10000000000 : ℝ)|=(5348896761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-423998657/2000000000 : ℝ)|^4313 ≤ (817475828503/6250000000000 : ℝ)^3289
        have hw : |(-423998657/2000000000 : ℝ)|=(423998657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311154103/2500000000 : ℝ)|^4313 ≤ (42899197567631/100000000000000 : ℝ)^3289
        have hw : |(1311154103/2500000000 : ℝ)|=(1311154103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s5_2 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348896343/10000000000 : ℝ)*x 0 + (2622308223/5000000000 : ℝ)*x 1 + (-2119993797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348896343/10000000000 : ℝ)^4313 ≤ (44021184655191/100000000000000 : ℝ)^3289 := by
    have hnat : (5348896343 : ℕ)^4313*100000000000000^3289 ≤ 44021184655191^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348896343 10000000000 44021184655191 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622308223/5000000000 : ℝ)^4313 ≤ (21449598966163/50000000000000 : ℝ)^3289 := by
    have hnat : (2622308223 : ℕ)^4313*50000000000000^3289 ≤ 21449598966163^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622308223 5000000000 21449598966163 50000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119993797/10000000000 : ℝ)^4313 ≤ (1307961739839/10000000000000 : ℝ)^3289 := by
    have hnat : (2119993797 : ℕ)^4313*10000000000000^3289 ≤ 1307961739839^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119993797 10000000000 1307961739839 10000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348896343/10000000000 : ℝ), (2622308223/5000000000 : ℝ), (-2119993797/10000000000 : ℝ)] ![(44021184655191/100000000000000 : ℝ), (21449598966163/50000000000000 : ℝ), (1307961739839/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348896343/10000000000 : ℝ)|^4313 ≤ (44021184655191/100000000000000 : ℝ)^3289
        have hw : |(5348896343/10000000000 : ℝ)|=(5348896343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622308223/5000000000 : ℝ)|^4313 ≤ (21449598966163/50000000000000 : ℝ)^3289
        have hw : |(2622308223/5000000000 : ℝ)|=(2622308223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2119993797/10000000000 : ℝ)|^4313 ≤ (1307961739839/10000000000000 : ℝ)^3289
        have hw : |(-2119993797/10000000000 : ℝ)|=(2119993797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s5_3 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2161863157/5000000000 : ℝ)*x 0 + (2075268397/5000000000 : ℝ)*x 1 + (4503621227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161863157/5000000000 : ℝ)^4313 ≤ (16651600680481/50000000000000 : ℝ)^3289 := by
    have hnat : (2161863157 : ℕ)^4313*50000000000000^3289 ≤ 16651600680481^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161863157 5000000000 16651600680481 50000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2075268397/5000000000 : ℝ)^4313 ≤ (3945613545689/12500000000000 : ℝ)^3289 := by
    have hnat : (2075268397 : ℕ)^4313*12500000000000^3289 ≤ 3945613545689^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075268397 5000000000 3945613545689 12500000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503621227/10000000000 : ℝ)^4313 ≤ (7026378052347/20000000000000 : ℝ)^3289 := by
    have hnat : (4503621227 : ℕ)^4313*20000000000000^3289 ≤ 7026378052347^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503621227 10000000000 7026378052347 20000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2161863157/5000000000 : ℝ), (2075268397/5000000000 : ℝ), (4503621227/10000000000 : ℝ)] ![(16651600680481/50000000000000 : ℝ), (3945613545689/12500000000000 : ℝ), (7026378052347/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2161863157/5000000000 : ℝ)|^4313 ≤ (16651600680481/50000000000000 : ℝ)^3289
        have hw : |(2161863157/5000000000 : ℝ)|=(2161863157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2075268397/5000000000 : ℝ)|^4313 ≤ (3945613545689/12500000000000 : ℝ)^3289
        have hw : |(2075268397/5000000000 : ℝ)|=(2075268397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503621227/10000000000 : ℝ)|^4313 ≤ (7026378052347/20000000000000 : ℝ)^3289
        have hw : |(4503621227/10000000000 : ℝ)|=(4503621227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s5_4 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-40689477/200000000 : ℝ)*x 0 + (327826267/625000000 : ℝ)*x 1 + (5411885319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40689477/200000000 : ℝ)^4313 ≤ (12392103056571/100000000000000 : ℝ)^3289 := by
    have hnat : (40689477 : ℕ)^4313*100000000000000^3289 ≤ 12392103056571^3289*200000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40689477 200000000 12392103056571 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327826267/625000000 : ℝ)^4313 ≤ (21452837441707/50000000000000 : ℝ)^3289 := by
    have hnat : (327826267 : ℕ)^4313*50000000000000^3289 ≤ 21452837441707^3289*625000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327826267 625000000 21452837441707 50000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411885319/10000000000 : ℝ)^4313 ≤ (44702222040087/100000000000000 : ℝ)^3289 := by
    have hnat : (5411885319 : ℕ)^4313*100000000000000^3289 ≤ 44702222040087^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411885319 10000000000 44702222040087 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-40689477/200000000 : ℝ), (327826267/625000000 : ℝ), (5411885319/10000000000 : ℝ)] ![(12392103056571/100000000000000 : ℝ), (21452837441707/50000000000000 : ℝ), (44702222040087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-40689477/200000000 : ℝ)|^4313 ≤ (12392103056571/100000000000000 : ℝ)^3289
        have hw : |(-40689477/200000000 : ℝ)|=(40689477/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327826267/625000000 : ℝ)|^4313 ≤ (21452837441707/50000000000000 : ℝ)^3289
        have hw : |(327826267/625000000 : ℝ)|=(327826267/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411885319/10000000000 : ℝ)|^4313 ≤ (44702222040087/100000000000000 : ℝ)^3289
        have hw : |(5411885319/10000000000 : ℝ)|=(5411885319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s5_5 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326400329/2500000000 : ℝ)*x 0 + (-1952724357/10000000000 : ℝ)*x 1 + (5411885327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326400329/2500000000 : ℝ)^4313 ≤ (43554522530549/100000000000000 : ℝ)^3289 := by
    have hnat : (1326400329 : ℕ)^4313*100000000000000^3289 ≤ 43554522530549^3289*2500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326400329 2500000000 43554522530549 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1952724357/10000000000 : ℝ)^4313 ≤ (11743255331309/100000000000000 : ℝ)^3289 := by
    have hnat : (1952724357 : ℕ)^4313*100000000000000^3289 ≤ 11743255331309^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952724357 10000000000 11743255331309 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411885327/10000000000 : ℝ)^4313 ≤ (2235111106337/5000000000000 : ℝ)^3289 := by
    have hnat : (5411885327 : ℕ)^4313*5000000000000^3289 ≤ 2235111106337^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411885327 10000000000 2235111106337 5000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326400329/2500000000 : ℝ), (-1952724357/10000000000 : ℝ), (5411885327/10000000000 : ℝ)] ![(43554522530549/100000000000000 : ℝ), (11743255331309/100000000000000 : ℝ), (2235111106337/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326400329/2500000000 : ℝ)|^4313 ≤ (43554522530549/100000000000000 : ℝ)^3289
        have hw : |(1326400329/2500000000 : ℝ)|=(1326400329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1952724357/10000000000 : ℝ)|^4313 ≤ (11743255331309/100000000000000 : ℝ)^3289
        have hw : |(-1952724357/10000000000 : ℝ)|=(1952724357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411885327/10000000000 : ℝ)|^4313 ≤ (2235111106337/5000000000000 : ℝ)^3289
        have hw : |(5411885327/10000000000 : ℝ)|=(5411885327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s5_6 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165800041/312500000 : ℝ)*x 0 + (2705942663/5000000000 : ℝ)*x 1 + (-1952724363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165800041/312500000 : ℝ)^4313 ≤ (43554522487489/100000000000000 : ℝ)^3289 := by
    have hnat : (165800041 : ℕ)^4313*100000000000000^3289 ≤ 43554522487489^3289*312500000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165800041 312500000 43554522487489 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705942663/5000000000 : ℝ)^4313 ≤ (44702222115909/100000000000000 : ℝ)^3289 := by
    have hnat : (2705942663 : ℕ)^4313*100000000000000^3289 ≤ 44702222115909^3289*5000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705942663 5000000000 44702222115909 100000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1952724363/10000000000 : ℝ)^4313 ≤ (93946043029/800000000000 : ℝ)^3289 := by
    have hnat : (1952724363 : ℕ)^4313*800000000000^3289 ≤ 93946043029^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952724363 10000000000 93946043029 800000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165800041/312500000 : ℝ), (2705942663/5000000000 : ℝ), (-1952724363/10000000000 : ℝ)] ![(43554522487489/100000000000000 : ℝ), (44702222115909/100000000000000 : ℝ), (93946043029/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165800041/312500000 : ℝ)|^4313 ≤ (43554522487489/100000000000000 : ℝ)^3289
        have hw : |(165800041/312500000 : ℝ)|=(165800041/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705942663/5000000000 : ℝ)|^4313 ≤ (44702222115909/100000000000000 : ℝ)^3289
        have hw : |(2705942663/5000000000 : ℝ)|=(2705942663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1952724363/10000000000 : ℝ)|^4313 ≤ (93946043029/800000000000 : ℝ)^3289
        have hw : |(-1952724363/10000000000 : ℝ)|=(1952724363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1353_s5_7 (p : ℝ) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080938121/2500000000 : ℝ)*x 0 + (900470147/2000000000 : ℝ)*x 1 + (4151813371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080938121/2500000000 : ℝ)^4313 ≤ (83258664229/250000000000 : ℝ)^3289 := by
    have hnat : (1080938121 : ℕ)^4313*250000000000^3289 ≤ 83258664229^3289*2500000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080938121 2500000000 83258664229 250000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900470147/2000000000 : ℝ)^4313 ≤ (8779723577381/25000000000000 : ℝ)^3289 := by
    have hnat : (900470147 : ℕ)^4313*25000000000000^3289 ≤ 8779723577381^3289*2000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900470147 2000000000 8779723577381 25000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4151813371/10000000000 : ℝ)^4313 ≤ (15788819992593/50000000000000 : ℝ)^3289 := by
    have hnat : (4151813371 : ℕ)^4313*50000000000000^3289 ≤ 15788819992593^3289*10000000000^4313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151813371 10000000000 15788819992593 50000000000000 4313 3289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4313/1024 : ℝ)) 4313 3289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080938121/2500000000 : ℝ), (900470147/2000000000 : ℝ), (4151813371/10000000000 : ℝ)] ![(83258664229/250000000000 : ℝ), (8779723577381/25000000000000 : ℝ), (15788819992593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080938121/2500000000 : ℝ)|^4313 ≤ (83258664229/250000000000 : ℝ)^3289
        have hw : |(1080938121/2500000000 : ℝ)|=(1080938121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900470147/2000000000 : ℝ)|^4313 ≤ (8779723577381/25000000000000 : ℝ)^3289
        have hw : |(900470147/2000000000 : ℝ)|=(900470147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4151813371/10000000000 : ℝ)|^4313 ≤ (15788819992593/50000000000000 : ℝ)^3289
        have hw : |(4151813371/10000000000 : ℝ)|=(4151813371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1353_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155162223/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1391/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11167/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7361/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1391/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1391/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1391/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1391/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1391/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1391/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1391/12500 : ℝ) ^ (539/128 : ℝ) ≤ (2412470920964937/25000000000000000000 : ℝ) := by
    have hpowers : (1391/12500 : ℝ)^539 ≤ (2412470920964937/25000000000000000000 : ℝ)^128 := by
      have hnat : (1391 : ℕ)^539*25000000000000000000^128 ≤ 2412470920964937^128*12500^539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1391 12500 2412470920964937 25000000000000000000 539 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1391/12500 : ℝ)) (X := (2412470920964937/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hpowhi : (3691/25000 : ℝ) ^ (539/128 : ℝ) ≤ (15868655315180933/50000000000000000000 : ℝ) := by
    have hpowers : (3691/25000 : ℝ)^539 ≤ (15868655315180933/50000000000000000000 : ℝ)^128 := by
      have hnat : (3691 : ℕ)^539*50000000000000000000^128 ≤ 15868655315180933^128*25000^539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3691 25000 15868655315180933 50000000000000000000 539 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3691/25000 : ℝ)) (X := (15868655315180933/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502412470920964937/12500000000000000000 : ℝ) ≤ (10000458290995809/10000000000000000 : ℝ) ^ (539/128 : ℝ) := by
    have hpowers : (12502412470920964937/12500000000000000000 : ℝ)^128 ≤ (10000458290995809/10000000000000000 : ℝ)^539 := by
      have hnat : (12502412470920964937 : ℕ)^128*10000000000000000^539 ≤ 10000458290995809^539*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502412470920964937 12500000000000000000 10000458290995809 10000000000000000 128 539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000458290995809/10000000000000000 : ℝ)) (X := (12502412470920964937/12500000000000000000 : ℝ)) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020693597157110807/50000000000000000000 : ℝ) ≤ (1250122836854241/1250000000000000 : ℝ) ^ (539/128 : ℝ) := by
    have hpowers : (50020693597157110807/50000000000000000000 : ℝ)^128 ≤ (1250122836854241/1250000000000000 : ℝ)^539 := by
      have hnat : (50020693597157110807 : ℕ)^128*1250000000000000^539 ≤ 1250122836854241^539*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020693597157110807 50000000000000000000 1250122836854241 1250000000000000 128 539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250122836854241/1250000000000000 : ℝ)) (X := (50020693597157110807/50000000000000000000 : ℝ)) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015868655315180933/25000000000000000000 : ℝ) ≤ (10001507098672047/10000000000000000 : ℝ) ^ (539/128 : ℝ) := by
    have hpowers : (25015868655315180933/25000000000000000000 : ℝ)^128 ≤ (10001507098672047/10000000000000000 : ℝ)^539 := by
      have hnat : (25015868655315180933 : ℕ)^128*10000000000000000^539 ≤ 10001507098672047^539*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015868655315180933 25000000000000000000 10001507098672047 10000000000000000 128 539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001507098672047/10000000000000000 : ℝ)) (X := (25015868655315180933/25000000000000000000 : ℝ)) (by norm_num) 539 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2412470920964937/25000000000000000000 : ℝ) ≤ ((605833253570659751/606000000000000000 : ℝ)+2*(174801279373/121200000000000 : ℝ)*(1391/12500 : ℝ))^(539/128 : ℝ) := by
    rw [show (605833253570659751/606000000000000000 : ℝ)+2*(174801279373/121200000000000 : ℝ)*(1391/12500 : ℝ)=(10000458290995809/10000000000000000 : ℝ) by norm_num, show 1+2*(2412470920964937/25000000000000000000 : ℝ)=(12502412470920964937/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15868655315180933/50000000000000000000 : ℝ)+(2412470920964937/25000000000000000000 : ℝ) ≤ ((605833253570659751/606000000000000000 : ℝ)+(174801279373/121200000000000 : ℝ)*((3691/25000 : ℝ)+(1391/12500 : ℝ)))^(539/128 : ℝ) := by
    rw [show (605833253570659751/606000000000000000 : ℝ)+(174801279373/121200000000000 : ℝ)*((3691/25000 : ℝ)+(1391/12500 : ℝ))=(1250122836854241/1250000000000000 : ℝ) by norm_num, show 1+(15868655315180933/50000000000000000000 : ℝ)+(2412470920964937/25000000000000000000 : ℝ)=(50020693597157110807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15868655315180933/50000000000000000000 : ℝ) ≤ ((605833253570659751/606000000000000000 : ℝ)+2*(174801279373/121200000000000 : ℝ)*(3691/25000 : ℝ))^(539/128 : ℝ) := by
    rw [show (605833253570659751/606000000000000000 : ℝ)+2*(174801279373/121200000000000 : ℝ)*(3691/25000 : ℝ)=(10001507098672047/10000000000000000 : ℝ) by norm_num, show 1+2*(15868655315180933/50000000000000000000 : ℝ)=(25015868655315180933/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (605833253570659751/606000000000000000 : ℝ)*(X 1 0+X 2 0)+(174801279373/121200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (539/128 : ℝ)) (lo := (1391/12500 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (605833253570659751/606000000000000000 : ℝ)) (alpha := (174801279373/121200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (605833253570659751/606000000000000000 : ℝ)*(X 0 1+X 2 1)+(174801279373/121200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (539/128 : ℝ)) (lo := (1391/12500 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (605833253570659751/606000000000000000 : ℝ)) (alpha := (174801279373/121200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (605833253570659751/606000000000000000 : ℝ)*(X 0 2+X 1 2)+(174801279373/121200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (539/128 : ℝ)) (lo := (1391/12500 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (605833253570659751/606000000000000000 : ℝ)) (alpha := (174801279373/121200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-508615453/2500000000 : ℝ)*X 0 0+(676561541/1250000000 : ℝ)*X 0 1+(2622308133/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348896761/10000000000 : ℝ)*X 1 0+(-423998657/2000000000 : ℝ)*X 1 1+(1311154103/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348896343/10000000000 : ℝ)*X 2 0+(2622308223/5000000000 : ℝ)*X 2 1+(-2119993797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2161863157/5000000000 : ℝ)*X 0 0+(2075268397/5000000000 : ℝ)*X 0 1+(4503621227/10000000000 : ℝ)*X 0 2+(2161863157/5000000000 : ℝ)*X 1 0+(2075268397/5000000000 : ℝ)*X 1 1+(4503621227/10000000000 : ℝ)*X 1 2+(2161863157/5000000000 : ℝ)*X 2 0+(2075268397/5000000000 : ℝ)*X 2 1+(4503621227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-40689477/200000000 : ℝ)*X 0 0+(327826267/625000000 : ℝ)*X 0 1+(5411885319/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326400329/2500000000 : ℝ)*X 1 0+(-1952724357/10000000000 : ℝ)*X 1 1+(5411885327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165800041/312500000 : ℝ)*X 2 0+(2705942663/5000000000 : ℝ)*X 2 1+(-1952724363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1080938121/2500000000 : ℝ)*X 0 0+(900470147/2000000000 : ℝ)*X 0 1+(4151813371/10000000000 : ℝ)*X 0 2+(1080938121/2500000000 : ℝ)*X 1 0+(900470147/2000000000 : ℝ)*X 1 1+(4151813371/10000000000 : ℝ)*X 1 2+(1080938121/2500000000 : ℝ)*X 2 0+(900470147/2000000000 : ℝ)*X 2 1+(4151813371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1353_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2606981710639461949755401/202000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1788178147/100000000000000 : ℝ)*(base19) + (161457119/10000000000000 : ℝ)*(base23) + (163549193/100000000000000 : ℝ)*(upper2) + (501138889/100000000000000 : ℝ)*(upper3) + (7413353/100000000000000 : ℝ)*(upper4) + (87890753513717/2000000000000 : ℝ)*(major0) + (87890753513717/2000000000000 : ℝ)*(major1) + (87890753513717/2000000000000 : ℝ)*(major2) + (5956827450411441/100000000000000 : ℝ)*(sp0) + (1191370347738629/20000000000000 : ℝ)*(sp1) + (2978425956150051/50000000000000 : ℝ)*(sp2) + (56644004972151/2000000000000 : ℝ)*(sp3) + (521529197/2000000000000 : ℝ)*(sp4) + (2643212231/12500000000000 : ℝ)*(sp7) + (1416110697152699/50000000000000 : ℝ)*(f.failure) + (5956853526871291/100000000000000 : ℝ)*(f.sum) + (572154979207/121200000000000000000000000 : ℝ)*base66 + (2664801180026533/1212000000000000000000000000000 : ℝ)*base68 + (9509588252258533/1212000000000000000000000000000 : ℝ)*base70 + (19976780898614533/1212000000000000000000000000000 : ℝ)*base72 + (47948640571/24240000000000000000000000 : ℝ)*base73 + (7242971644466533/1212000000000000000000000000000 : ℝ)*base76 + (8636004351506533/1212000000000000000000000000000 : ℝ)*base78 + (17895609636554533/1212000000000000000000000000000 : ℝ)*base80 + (1146636065821/606000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (47289877/5000000000000000000000 : ℝ)*base89 + (47289877/5000000000000000000000 : ℝ)*base91 + (47289877/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11233792882596118300446731/1010000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1979102927/100000000000000 : ℝ)*(base19) + (420399253/20000000000000 : ℝ)*(base23) + (29565253/12500000000000 : ℝ)*(upper3) + (2892831/5000000000000 : ℝ)*(lower4) + (9199247/4000000000000 : ℝ)*(upper5) + (442640991511981/10000000000000 : ℝ)*(major0) + (442640991511981/10000000000000 : ℝ)*(major1) + (442640991511981/10000000000000 : ℝ)*(major2) + (40432685237/100000000000000 : ℝ)*(sp1) + (21342035601/50000000000000 : ℝ)*(sp2) + (750007103565197/12500000000000 : ℝ)*(sp4) + (6000014416733411/100000000000000 : ℝ)*(sp5) + (6000012042454109/100000000000000 : ℝ)*(sp6) + (89148832217681/3125000000000 : ℝ)*(sp7) + (89148832217681/3125000000000 : ℝ)*(f.failure) + (750007103565197/12500000000000 : ℝ)*(f.sum) + (823407278549/121200000000000000000000000 : ℝ)*base65 + (26868895968978269/6060000000000000000000000000000 : ℝ)*base68 + (100208844780018269/6060000000000000000000000000000 : ℝ)*base70 + (96382003350881731/6060000000000000000000000000000 : ℝ)*base71 + (105759054721/24240000000000000000000000 : ℝ)*base73 + (87075172199838269/6060000000000000000000000000000 : ℝ)*base76 + (4183812158778269/6060000000000000000000000000000 : ℝ)*base78 + (24367774069781731/6060000000000000000000000000000 : ℝ)*base79 + (744824974313/606000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2385137/312500000000000000000 : ℝ)*base90 + (2385137/312500000000000000000 : ℝ)*base92 + (2385137/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1353_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155162223/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1391/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7361/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1353_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1353_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155162223/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9923/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7361/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1353_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1353_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1353_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (539/128 : ℝ) ≤ p) (hpb : p ≤ (4313/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155162223/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9923/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7361/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1353_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
