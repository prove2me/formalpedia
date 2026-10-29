-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1463_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:08:37.209616+00:00
-- url     : https://prove2.me/submissions/7b22090d-7f89-4b5d-9505-47a8ecb72ebe

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
theorem support_rectangle_w1463_s0_0 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-869862257/5000000000 : ℝ)*x 0 + (5946275373/10000000000 : ℝ)*x 1 + (4838948541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869862257/5000000000 : ℝ)^4423 ≤ (2054441466539/20000000000000 : ℝ)^3399 := by
    have hnat : (869862257 : ℕ)^4423*20000000000000^3399 ≤ 2054441466539^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869862257 5000000000 2054441466539 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5946275373/10000000000 : ℝ)^4423 ≤ (10168641137357/20000000000000 : ℝ)^3399 := by
    have hnat : (5946275373 : ℕ)^4423*20000000000000^3399 ≤ 10168641137357^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5946275373 10000000000 10168641137357 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4838948541/10000000000 : ℝ)^4423 ≤ (38884586969003/100000000000000 : ℝ)^3399 := by
    have hnat : (4838948541 : ℕ)^4423*100000000000000^3399 ≤ 38884586969003^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4838948541 10000000000 38884586969003 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-869862257/5000000000 : ℝ), (5946275373/10000000000 : ℝ), (4838948541/10000000000 : ℝ)] ![(2054441466539/20000000000000 : ℝ), (10168641137357/20000000000000 : ℝ), (38884586969003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-869862257/5000000000 : ℝ)|^4423 ≤ (2054441466539/20000000000000 : ℝ)^3399
        have hw : |(-869862257/5000000000 : ℝ)|=(869862257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5946275373/10000000000 : ℝ)|^4423 ≤ (10168641137357/20000000000000 : ℝ)^3399
        have hw : |(5946275373/10000000000 : ℝ)|=(5946275373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4838948541/10000000000 : ℝ)|^4423 ≤ (38884586969003/100000000000000 : ℝ)^3399
        have hw : |(4838948541/10000000000 : ℝ)|=(4838948541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s0_1 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (343020281/625000000 : ℝ)*x 0 + (-1181895887/5000000000 : ℝ)*x 1 + (1209737127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343020281/625000000 : ℝ)^4423 ≤ (9161615941019/20000000000000 : ℝ)^3399 := by
    have hnat : (343020281 : ℕ)^4423*20000000000000^3399 ≤ 9161615941019^3399*625000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343020281 625000000 9161615941019 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1181895887/5000000000 : ℝ)^4423 ≤ (191341670791/1250000000000 : ℝ)^3399 := by
    have hnat : (1181895887 : ℕ)^4423*1250000000000^3399 ≤ 191341670791^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181895887 5000000000 191341670791 1250000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1209737127/2500000000 : ℝ)^4423 ≤ (19442293311967/50000000000000 : ℝ)^3399 := by
    have hnat : (1209737127 : ℕ)^4423*50000000000000^3399 ≤ 19442293311967^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209737127 2500000000 19442293311967 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(343020281/625000000 : ℝ), (-1181895887/5000000000 : ℝ), (1209737127/2500000000 : ℝ)] ![(9161615941019/20000000000000 : ℝ), (191341670791/1250000000000 : ℝ), (19442293311967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(343020281/625000000 : ℝ)|^4423 ≤ (9161615941019/20000000000000 : ℝ)^3399
        have hw : |(343020281/625000000 : ℝ)|=(343020281/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1181895887/5000000000 : ℝ)|^4423 ≤ (191341670791/1250000000000 : ℝ)^3399
        have hw : |(-1181895887/5000000000 : ℝ)|=(1181895887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1209737127/2500000000 : ℝ)|^4423 ≤ (19442293311967/50000000000000 : ℝ)^3399
        have hw : |(1209737127/2500000000 : ℝ)|=(1209737127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s0_2 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5488324847/10000000000 : ℝ)*x 0 + (1209737127/2500000000 : ℝ)*x 1 + (-2363791321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5488324847/10000000000 : ℝ)^4423 ≤ (45808083517291/100000000000000 : ℝ)^3399 := by
    have hnat : (5488324847 : ℕ)^4423*100000000000000^3399 ≤ 45808083517291^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488324847 10000000000 45808083517291 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1209737127/2500000000 : ℝ)^4423 ≤ (19442293311967/50000000000000 : ℝ)^3399 := by
    have hnat : (1209737127 : ℕ)^4423*50000000000000^3399 ≤ 19442293311967^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209737127 2500000000 19442293311967 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2363791321/10000000000 : ℝ)^4423 ≤ (15307329845997/100000000000000 : ℝ)^3399 := by
    have hnat : (2363791321 : ℕ)^4423*100000000000000^3399 ≤ 15307329845997^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2363791321 10000000000 15307329845997 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5488324847/10000000000 : ℝ), (1209737127/2500000000 : ℝ), (-2363791321/10000000000 : ℝ)] ![(45808083517291/100000000000000 : ℝ), (19442293311967/50000000000000 : ℝ), (15307329845997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5488324847/10000000000 : ℝ)|^4423 ≤ (45808083517291/100000000000000 : ℝ)^3399
        have hw : |(5488324847/10000000000 : ℝ)|=(5488324847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1209737127/2500000000 : ℝ)|^4423 ≤ (19442293311967/50000000000000 : ℝ)^3399
        have hw : |(1209737127/2500000000 : ℝ)|=(1209737127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2363791321/10000000000 : ℝ)|^4423 ≤ (15307329845997/100000000000000 : ℝ)^3399
        have hw : |(-2363791321/10000000000 : ℝ)|=(2363791321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s0_3 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (520145223/1250000000 : ℝ)*x 0 + (3102671881/10000000000 : ℝ)*x 1 + (5528065029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520145223/1250000000 : ℝ)^4423 ≤ (15975970973107/50000000000000 : ℝ)^3399 := by
    have hnat : (520145223 : ℕ)^4423*50000000000000^3399 ≤ 15975970973107^3399*1250000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520145223 1250000000 15975970973107 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3102671881/10000000000 : ℝ)^4423 ≤ (21807888143467/100000000000000 : ℝ)^3399 := by
    have hnat : (3102671881 : ℕ)^4423*100000000000000^3399 ≤ 21807888143467^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3102671881 10000000000 21807888143467 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5528065029/10000000000 : ℝ)^4423 ≤ (46240169895727/100000000000000 : ℝ)^3399 := by
    have hnat : (5528065029 : ℕ)^4423*100000000000000^3399 ≤ 46240169895727^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528065029 10000000000 46240169895727 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(520145223/1250000000 : ℝ), (3102671881/10000000000 : ℝ), (5528065029/10000000000 : ℝ)] ![(15975970973107/50000000000000 : ℝ), (21807888143467/100000000000000 : ℝ), (46240169895727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(520145223/1250000000 : ℝ)|^4423 ≤ (15975970973107/50000000000000 : ℝ)^3399
        have hw : |(520145223/1250000000 : ℝ)|=(520145223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3102671881/10000000000 : ℝ)|^4423 ≤ (21807888143467/100000000000000 : ℝ)^3399
        have hw : |(3102671881/10000000000 : ℝ)|=(3102671881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5528065029/10000000000 : ℝ)|^4423 ≤ (46240169895727/100000000000000 : ℝ)^3399
        have hw : |(5528065029/10000000000 : ℝ)|=(5528065029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s0_4 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-69743233/400000000 : ℝ)*x 0 + (4867203553/10000000000 : ℝ)*x 1 + (1479253053/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69743233/400000000 : ℝ)^4423 ≤ (10301846502129/100000000000000 : ℝ)^3399 := by
    have hnat : (69743233 : ℕ)^4423*100000000000000^3399 ≤ 10301846502129^3399*400000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69743233 400000000 10301846502129 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4867203553/10000000000 : ℝ)^4423 ≤ (19590149521727/50000000000000 : ℝ)^3399 := by
    have hnat : (4867203553 : ℕ)^4423*50000000000000^3399 ≤ 19590149521727^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4867203553 10000000000 19590149521727 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1479253053/2500000000 : ℝ)^4423 ≤ (25258927215851/50000000000000 : ℝ)^3399 := by
    have hnat : (1479253053 : ℕ)^4423*50000000000000^3399 ≤ 25258927215851^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479253053 2500000000 25258927215851 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69743233/400000000 : ℝ), (4867203553/10000000000 : ℝ), (1479253053/2500000000 : ℝ)] ![(10301846502129/100000000000000 : ℝ), (19590149521727/50000000000000 : ℝ), (25258927215851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69743233/400000000 : ℝ)|^4423 ≤ (10301846502129/100000000000000 : ℝ)^3399
        have hw : |(-69743233/400000000 : ℝ)|=(69743233/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4867203553/10000000000 : ℝ)|^4423 ≤ (19590149521727/50000000000000 : ℝ)^3399
        have hw : |(4867203553/10000000000 : ℝ)|=(4867203553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1479253053/2500000000 : ℝ)|^4423 ≤ (25258927215851/50000000000000 : ℝ)^3399
        have hw : |(1479253053/2500000000 : ℝ)|=(1479253053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s0_5 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (324121847/625000000 : ℝ)*x 0 + (-321431879/2500000000 : ℝ)*x 1 + (2958506173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324121847/625000000 : ℝ)^4423 ≤ (21275805622413/50000000000000 : ℝ)^3399 := by
    have hnat : (324121847 : ℕ)^4423*50000000000000^3399 ≤ 21275805622413^3399*625000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324121847 625000000 21275805622413 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321431879/2500000000 : ℝ)^4423 ≤ (6930532809837/100000000000000 : ℝ)^3399 := by
    have hnat : (321431879 : ℕ)^4423*100000000000000^3399 ≤ 6930532809837^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321431879 2500000000 6930532809837 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2958506173/5000000000 : ℝ)^4423 ≤ (25258927960211/50000000000000 : ℝ)^3399 := by
    have hnat : (2958506173 : ℕ)^4423*50000000000000^3399 ≤ 25258927960211^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2958506173 5000000000 25258927960211 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324121847/625000000 : ℝ), (-321431879/2500000000 : ℝ), (2958506173/5000000000 : ℝ)] ![(21275805622413/50000000000000 : ℝ), (6930532809837/100000000000000 : ℝ), (25258927960211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324121847/625000000 : ℝ)|^4423 ≤ (21275805622413/50000000000000 : ℝ)^3399
        have hw : |(324121847/625000000 : ℝ)|=(324121847/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-321431879/2500000000 : ℝ)|^4423 ≤ (6930532809837/100000000000000 : ℝ)^3399
        have hw : |(-321431879/2500000000 : ℝ)|=(321431879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2958506173/5000000000 : ℝ)|^4423 ≤ (25258927960211/50000000000000 : ℝ)^3399
        have hw : |(2958506173/5000000000 : ℝ)|=(2958506173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s0_6 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5185949459/10000000000 : ℝ)*x 0 + (1479253057/2500000000 : ℝ)*x 1 + (-321431961/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5185949459/10000000000 : ℝ)^4423 ≤ (8510322050371/20000000000000 : ℝ)^3399 := by
    have hnat : (5185949459 : ℕ)^4423*20000000000000^3399 ≤ 8510322050371^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185949459 10000000000 8510322050371 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1479253057/2500000000 : ℝ)^4423 ≤ (50517854609459/100000000000000 : ℝ)^3399 := by
    have hnat : (1479253057 : ℕ)^4423*100000000000000^3399 ≤ 50517854609459^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479253057 2500000000 50517854609459 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321431961/2500000000 : ℝ)^4423 ≤ (6930535110523/100000000000000 : ℝ)^3399 := by
    have hnat : (321431961 : ℕ)^4423*100000000000000^3399 ≤ 6930535110523^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321431961 2500000000 6930535110523 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5185949459/10000000000 : ℝ), (1479253057/2500000000 : ℝ), (-321431961/2500000000 : ℝ)] ![(8510322050371/20000000000000 : ℝ), (50517854609459/100000000000000 : ℝ), (6930535110523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5185949459/10000000000 : ℝ)|^4423 ≤ (8510322050371/20000000000000 : ℝ)^3399
        have hw : |(5185949459/10000000000 : ℝ)|=(5185949459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1479253057/2500000000 : ℝ)|^4423 ≤ (50517854609459/100000000000000 : ℝ)^3399
        have hw : |(1479253057/2500000000 : ℝ)|=(1479253057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-321431961/2500000000 : ℝ)|^4423 ≤ (6930535110523/100000000000000 : ℝ)^3399
        have hw : |(-321431961/2500000000 : ℝ)|=(321431961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s0_7 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1042402359/2500000000 : ℝ)*x 0 + (5466176759/10000000000 : ℝ)*x 1 + (197923001/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042402359/2500000000 : ℝ)^4423 ≤ (32036375908831/100000000000000 : ℝ)^3399 := by
    have hnat : (1042402359 : ℕ)^4423*100000000000000^3399 ≤ 32036375908831^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042402359 2500000000 32036375908831 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5466176759/10000000000 : ℝ)^4423 ≤ (45567680451079/100000000000000 : ℝ)^3399 := by
    have hnat : (5466176759 : ℕ)^4423*100000000000000^3399 ≤ 45567680451079^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466176759 10000000000 45567680451079 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197923001/625000000 : ℝ)^4423 ≤ (5598985905689/25000000000000 : ℝ)^3399 := by
    have hnat : (197923001 : ℕ)^4423*25000000000000^3399 ≤ 5598985905689^3399*625000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197923001 625000000 5598985905689 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042402359/2500000000 : ℝ), (5466176759/10000000000 : ℝ), (197923001/625000000 : ℝ)] ![(32036375908831/100000000000000 : ℝ), (45567680451079/100000000000000 : ℝ), (5598985905689/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042402359/2500000000 : ℝ)|^4423 ≤ (32036375908831/100000000000000 : ℝ)^3399
        have hw : |(1042402359/2500000000 : ℝ)|=(1042402359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5466176759/10000000000 : ℝ)|^4423 ≤ (45567680451079/100000000000000 : ℝ)^3399
        have hw : |(5466176759/10000000000 : ℝ)|=(5466176759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(197923001/625000000 : ℝ)|^4423 ≤ (5598985905689/25000000000000 : ℝ)^3399
        have hw : |(197923001/625000000 : ℝ)|=(197923001/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1463_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (457/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1041/4000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2211/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2211 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2211*1^512 ≤ 0^512*1^2211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2211 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2211/512 : ℝ) ≤ (1912282421620511267/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2211 ≤ (1912282421620511267/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2211*100000000000000000000^512 ≤ 1912282421620511267^512*5^2211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1912282421620511267 100000000000000000000 2211 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1912282421620511267/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2211 := by
      have hnat : (1 : ℕ)^512*1^2211 ≤ 1^2211*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (101912282421620511267/100000000000000000000 : ℝ) ≤ (156936888704523/156250000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (101912282421620511267/100000000000000000000 : ℝ)^512 ≤ (156936888704523/156250000000000 : ℝ)^2211 := by
      have hnat : (101912282421620511267 : ℕ)^512*156250000000000^2211 ≤ 156936888704523^2211*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101912282421620511267 100000000000000000000 156936888704523 156250000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156936888704523/156250000000000 : ℝ)) (X := (101912282421620511267/100000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (51912282421620511267/50000000000000000000 : ℝ) ≤ (78811888704523/78125000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (51912282421620511267/50000000000000000000 : ℝ)^512 ≤ (78811888704523/78125000000000 : ℝ)^2211 := by
      have hnat : (51912282421620511267 : ℕ)^512*78125000000000^2211 ≤ 78811888704523^2211*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51912282421620511267 50000000000000000000 78811888704523 78125000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78811888704523/78125000000000 : ℝ)) (X := (51912282421620511267/50000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(686888704523/62500000000000 : ℝ)*(0 : ℝ))^(2211/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(686888704523/62500000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1912282421620511267/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(686888704523/62500000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2211/512 : ℝ) := by
    rw [show (1 : ℝ)+(686888704523/62500000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(156936888704523/156250000000000 : ℝ) by norm_num, show 1+(1912282421620511267/100000000000000000000 : ℝ)+(0 : ℝ)=(101912282421620511267/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1912282421620511267/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(686888704523/62500000000000 : ℝ)*(2/5 : ℝ))^(2211/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(686888704523/62500000000000 : ℝ)*(2/5 : ℝ)=(78811888704523/78125000000000 : ℝ) by norm_num, show 1+2*(1912282421620511267/100000000000000000000 : ℝ)=(51912282421620511267/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(686888704523/62500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (686888704523/62500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(686888704523/62500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (686888704523/62500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(686888704523/62500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (686888704523/62500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-869862257/5000000000 : ℝ)*X 0 0+(5946275373/10000000000 : ℝ)*X 0 1+(4838948541/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((343020281/625000000 : ℝ)*X 1 0+(-1181895887/5000000000 : ℝ)*X 1 1+(1209737127/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5488324847/10000000000 : ℝ)*X 2 0+(1209737127/2500000000 : ℝ)*X 2 1+(-2363791321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((520145223/1250000000 : ℝ)*X 0 0+(3102671881/10000000000 : ℝ)*X 0 1+(5528065029/10000000000 : ℝ)*X 0 2+(520145223/1250000000 : ℝ)*X 1 0+(3102671881/10000000000 : ℝ)*X 1 1+(5528065029/10000000000 : ℝ)*X 1 2+(520145223/1250000000 : ℝ)*X 2 0+(3102671881/10000000000 : ℝ)*X 2 1+(5528065029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-69743233/400000000 : ℝ)*X 0 0+(4867203553/10000000000 : ℝ)*X 0 1+(1479253053/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((324121847/625000000 : ℝ)*X 1 0+(-321431879/2500000000 : ℝ)*X 1 1+(2958506173/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5185949459/10000000000 : ℝ)*X 2 0+(1479253057/2500000000 : ℝ)*X 2 1+(-321431961/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1042402359/2500000000 : ℝ)*X 0 0+(5466176759/10000000000 : ℝ)*X 0 1+(197923001/625000000 : ℝ)*X 0 2+(1042402359/2500000000 : ℝ)*X 1 0+(5466176759/10000000000 : ℝ)*X 1 1+(197923001/625000000 : ℝ)*X 1 2+(1042402359/2500000000 : ℝ)*X 2 0+(5466176759/10000000000 : ℝ)*X 2 1+(197923001/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (518934432112384838307/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37030907/4000000000000 : ℝ)*(base19) + (195145877/20000000000000 : ℝ)*(base23) + (50620911/100000000000000 : ℝ)*(upper3) + (535037/12500000000000 : ℝ)*(upper4) + (184309827/100000000000000 : ℝ)*(upper5) + (13153902300669/2000000000000 : ℝ)*(major0) + (13153902300669/2000000000000 : ℝ)*(major1) + (13153902300669/2000000000000 : ℝ)*(major2) + (451539248762731/50000000000000 : ℝ)*(sp0) + (903081506538581/100000000000000 : ℝ)*(sp1) + (903081456581871/100000000000000 : ℝ)*(sp2) + (412306101169063/100000000000000 : ℝ)*(sp3) + (1967392897/50000000000000 : ℝ)*(sp4) + (1558204061/100000000000000 : ℝ)*(sp7) + (103076914843281/25000000000000 : ℝ)*(f.failure) + (112885304038907/12500000000000 : ℝ)*(f.sum) + (9644712609/1953125000000000000000000 : ℝ)*base66 + (860929925363/125000000000000000000000000 : ℝ)*base68 + (375706766619/62500000000000000000000000 : ℝ)*base70 + (975002294613/125000000000000000000000000 : ℝ)*base72 + (238441468363/62500000000000000000000000 : ℝ)*base74 + (113385254497/31250000000000000000000000 : ℝ)*base76 + (239230432369/62500000000000000000000000 : ℝ)*base78 + (670120557863/125000000000000000000000000 : ℝ)*base80 + (171814349863/62500000000000000000000000 : ℝ)*base82 + (6705939/2500000000000000000000 : ℝ)*base89 + (6705939/2500000000000000000000 : ℝ)*base91 + (6705939/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (892192801952352744957/390625000000000000000000000 : ℝ) := by norm_num
    linear_combination (549804753/100000000000000 : ℝ)*(base19) + (262338893/50000000000000 : ℝ)*(base23) + (39043627/50000000000000 : ℝ)*(base32) + (83275979/100000000000000 : ℝ)*(upper3) + (4946061/12500000000000 : ℝ)*(upper5) + (43357765888109/6250000000000 : ℝ)*(major0) + (43357765888109/6250000000000 : ℝ)*(major1) + (43357765888109/6250000000000 : ℝ)*(major2) + (71411749/5000000000000 : ℝ)*(sp1) + (645129857/50000000000000 : ℝ)*(sp2) + (476277091353851/50000000000000 : ℝ)*(sp4) + (952552204667969/100000000000000 : ℝ)*(sp5) + (952552367770201/100000000000000 : ℝ)*(sp6) + (434894171490741/100000000000000 : ℝ)*(sp7) + (86978849915599/20000000000000 : ℝ)*(f.failure) + (476277091353851/50000000000000 : ℝ)*(f.sum) + (1328238726681/1562500000000000000000000000 : ℝ)*base65 + (2222213342069/3125000000000000000000000000 : ℝ)*base68 + (559032944441/195312500000000000000000000 : ℝ)*base69 + (1311752587139/781250000000000000000000000 : ℝ)*base71 + (1673724425237/3125000000000000000000000000 : ℝ)*base73 + (3321015022597/1562500000000000000000000000 : ℝ)*base76 + (13311963320431/3125000000000000000000000000 : ℝ)*base77 + (22562288739181/3125000000000000000000000000 : ℝ)*base79 + (4207296395431/1562500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (7759219/2000000000000000000000 : ℝ)*base90 + (7759219/2000000000000000000000 : ℝ)*base92 + (7759219/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1463_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (457/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1041/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1463_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1463_s1_0 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-59602713/312500000 : ℝ)*x 0 + (698986853/1250000000 : ℝ)*x 1 + (1017169739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59602713/312500000 : ℝ)^4423 ≤ (11577918254661/100000000000000 : ℝ)^3399 := by
    have hnat : (59602713 : ℕ)^4423*100000000000000^3399 ≤ 11577918254661^3399*312500000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59602713 312500000 11577918254661 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (698986853/1250000000 : ℝ)^4423 ≤ (9387227231597/20000000000000 : ℝ)^3399 := by
    have hnat : (698986853 : ℕ)^4423*20000000000000^3399 ≤ 9387227231597^3399*1250000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698986853 1250000000 9387227231597 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1017169739/2000000000 : ℝ)^4423 ≤ (2592871598307/6250000000000 : ℝ)^3399 := by
    have hnat : (1017169739 : ℕ)^4423*6250000000000^3399 ≤ 2592871598307^3399*2000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017169739 2000000000 2592871598307 6250000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-59602713/312500000 : ℝ), (698986853/1250000000 : ℝ), (1017169739/2000000000 : ℝ)] ![(11577918254661/100000000000000 : ℝ), (9387227231597/20000000000000 : ℝ), (2592871598307/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-59602713/312500000 : ℝ)|^4423 ≤ (11577918254661/100000000000000 : ℝ)^3399
        have hw : |(-59602713/312500000 : ℝ)|=(59602713/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(698986853/1250000000 : ℝ)|^4423 ≤ (9387227231597/20000000000000 : ℝ)^3399
        have hw : |(698986853/1250000000 : ℝ)|=(698986853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1017169739/2000000000 : ℝ)|^4423 ≤ (2592871598307/6250000000000 : ℝ)^3399
        have hw : |(1017169739/2000000000 : ℝ)|=(1017169739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s1_1 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5393425973/10000000000 : ℝ)*x 0 + (-2174755343/10000000000 : ℝ)*x 1 + (40686807/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5393425973/10000000000 : ℝ)^4423 ≤ (4478008636849/10000000000000 : ℝ)^3399 := by
    have hnat : (5393425973 : ℕ)^4423*10000000000000^3399 ≤ 4478008636849^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393425973 10000000000 4478008636849 10000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2174755343/10000000000 : ℝ)^4423 ≤ (13733944908543/100000000000000 : ℝ)^3399 := by
    have hnat : (2174755343 : ℕ)^4423*100000000000000^3399 ≤ 13733944908543^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174755343 10000000000 13733944908543 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40686807/80000000 : ℝ)^4423 ≤ (20742984356363/50000000000000 : ℝ)^3399 := by
    have hnat : (40686807 : ℕ)^4423*50000000000000^3399 ≤ 20742984356363^3399*80000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40686807 80000000 20742984356363 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5393425973/10000000000 : ℝ), (-2174755343/10000000000 : ℝ), (40686807/80000000 : ℝ)] ![(4478008636849/10000000000000 : ℝ), (13733944908543/100000000000000 : ℝ), (20742984356363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5393425973/10000000000 : ℝ)|^4423 ≤ (4478008636849/10000000000000 : ℝ)^3399
        have hw : |(5393425973/10000000000 : ℝ)|=(5393425973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2174755343/10000000000 : ℝ)|^4423 ≤ (13733944908543/100000000000000 : ℝ)^3399
        have hw : |(-2174755343/10000000000 : ℝ)|=(2174755343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40686807/80000000 : ℝ)|^4423 ≤ (20742984356363/50000000000000 : ℝ)^3399
        have hw : |(40686807/80000000 : ℝ)|=(40686807/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s1_2 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539342781/1000000000 : ℝ)*x 0 + (5085848861/10000000000 : ℝ)*x 1 + (-2174755529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539342781/1000000000 : ℝ)^4423 ≤ (44780106215503/100000000000000 : ℝ)^3399 := by
    have hnat : (539342781 : ℕ)^4423*100000000000000^3399 ≤ 44780106215503^3399*1000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539342781 1000000000 44780106215503 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5085848861/10000000000 : ℝ)^4423 ≤ (8297189466987/20000000000000 : ℝ)^3399 := by
    have hnat : (5085848861 : ℕ)^4423*20000000000000^3399 ≤ 8297189466987^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085848861 10000000000 8297189466987 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2174755529/10000000000 : ℝ)^4423 ≤ (3433486609259/25000000000000 : ℝ)^3399 := by
    have hnat : (2174755529 : ℕ)^4423*25000000000000^3399 ≤ 3433486609259^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174755529 10000000000 3433486609259 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539342781/1000000000 : ℝ), (5085848861/10000000000 : ℝ), (-2174755529/10000000000 : ℝ)] ![(44780106215503/100000000000000 : ℝ), (8297189466987/20000000000000 : ℝ), (3433486609259/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539342781/1000000000 : ℝ)|^4423 ≤ (44780106215503/100000000000000 : ℝ)^3399
        have hw : |(539342781/1000000000 : ℝ)|=(539342781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5085848861/10000000000 : ℝ)|^4423 ≤ (8297189466987/20000000000000 : ℝ)^3399
        have hw : |(5085848861/10000000000 : ℝ)|=(5085848861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2174755529/10000000000 : ℝ)|^4423 ≤ (3433486609259/25000000000000 : ℝ)^3399
        have hw : |(-2174755529/10000000000 : ℝ)|=(2174755529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s1_3 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4270443307/10000000000 : ℝ)*x 0 + (46848647/125000000 : ℝ)*x 1 + (4856286251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4270443307/10000000000 : ℝ)^4423 ≤ (33048166377433/100000000000000 : ℝ)^3399 := by
    have hnat : (4270443307 : ℕ)^4423*100000000000000^3399 ≤ 33048166377433^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4270443307 10000000000 33048166377433 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46848647/125000000 : ℝ)^4423 ≤ (2788585464039/10000000000000 : ℝ)^3399 := by
    have hnat : (46848647 : ℕ)^4423*10000000000000^3399 ≤ 2788585464039^3399*125000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46848647 125000000 2788585464039 10000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4856286251/10000000000 : ℝ)^4423 ≤ (39065978969259/100000000000000 : ℝ)^3399 := by
    have hnat : (4856286251 : ℕ)^4423*100000000000000^3399 ≤ 39065978969259^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4856286251 10000000000 39065978969259 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4270443307/10000000000 : ℝ), (46848647/125000000 : ℝ), (4856286251/10000000000 : ℝ)] ![(33048166377433/100000000000000 : ℝ), (2788585464039/10000000000000 : ℝ), (39065978969259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4270443307/10000000000 : ℝ)|^4423 ≤ (33048166377433/100000000000000 : ℝ)^3399
        have hw : |(4270443307/10000000000 : ℝ)|=(4270443307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(46848647/125000000 : ℝ)|^4423 ≤ (2788585464039/10000000000000 : ℝ)^3399
        have hw : |(46848647/125000000 : ℝ)|=(46848647/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4856286251/10000000000 : ℝ)|^4423 ≤ (39065978969259/100000000000000 : ℝ)^3399
        have hw : |(4856286251/10000000000 : ℝ)|=(4856286251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s1_4 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-238455127/1250000000 : ℝ)*x 0 + (5091626167/10000000000 : ℝ)*x 1 + (5586022059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (238455127/1250000000 : ℝ)^4423 ≤ (11580716211121/100000000000000 : ℝ)^3399 := by
    have hnat : (238455127 : ℕ)^4423*100000000000000^3399 ≤ 11580716211121^3399*1250000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238455127 1250000000 11580716211121 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5091626167/10000000000 : ℝ)^4423 ≤ (4154728157583/10000000000000 : ℝ)^3399 := by
    have hnat : (5091626167 : ℕ)^4423*10000000000000^3399 ≤ 4154728157583^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5091626167 10000000000 4154728157583 10000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5586022059/10000000000 : ℝ)^4423 ≤ (11718000551167/25000000000000 : ℝ)^3399 := by
    have hnat : (5586022059 : ℕ)^4423*25000000000000^3399 ≤ 11718000551167^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5586022059 10000000000 11718000551167 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-238455127/1250000000 : ℝ), (5091626167/10000000000 : ℝ), (5586022059/10000000000 : ℝ)] ![(11580716211121/100000000000000 : ℝ), (4154728157583/10000000000000 : ℝ), (11718000551167/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-238455127/1250000000 : ℝ)|^4423 ≤ (11580716211121/100000000000000 : ℝ)^3399
        have hw : |(-238455127/1250000000 : ℝ)|=(238455127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5091626167/10000000000 : ℝ)|^4423 ≤ (4154728157583/10000000000000 : ℝ)^3399
        have hw : |(5091626167/10000000000 : ℝ)|=(5091626167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5586022059/10000000000 : ℝ)|^4423 ≤ (11718000551167/25000000000000 : ℝ)^3399
        have hw : |(5586022059/10000000000 : ℝ)|=(5586022059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s1_5 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1315221303/2500000000 : ℝ)*x 0 + (-334916667/2000000000 : ℝ)*x 1 + (349126381/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1315221303/2500000000 : ℝ)^4423 ≤ (21676721394313/50000000000000 : ℝ)^3399 := by
    have hnat : (1315221303 : ℕ)^4423*50000000000000^3399 ≤ 21676721394313^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315221303 2500000000 21676721394313 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (334916667/2000000000 : ℝ)^4423 ≤ (9774554578441/100000000000000 : ℝ)^3399 := by
    have hnat : (334916667 : ℕ)^4423*100000000000000^3399 ≤ 9774554578441^3399*2000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334916667 2000000000 9774554578441 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (349126381/625000000 : ℝ)^4423 ≤ (9374400521733/20000000000000 : ℝ)^3399 := by
    have hnat : (349126381 : ℕ)^4423*20000000000000^3399 ≤ 9374400521733^3399*625000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349126381 625000000 9374400521733 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1315221303/2500000000 : ℝ), (-334916667/2000000000 : ℝ), (349126381/625000000 : ℝ)] ![(21676721394313/50000000000000 : ℝ), (9774554578441/100000000000000 : ℝ), (9374400521733/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1315221303/2500000000 : ℝ)|^4423 ≤ (21676721394313/50000000000000 : ℝ)^3399
        have hw : |(1315221303/2500000000 : ℝ)|=(1315221303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-334916667/2000000000 : ℝ)|^4423 ≤ (9774554578441/100000000000000 : ℝ)^3399
        have hw : |(-334916667/2000000000 : ℝ)|=(334916667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(349126381/625000000 : ℝ)|^4423 ≤ (9374400521733/20000000000000 : ℝ)^3399
        have hw : |(349126381/625000000 : ℝ)|=(349126381/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s1_6 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2630442543/5000000000 : ℝ)*x 0 + (2793011033/5000000000 : ℝ)*x 1 + (-837291779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2630442543/5000000000 : ℝ)^4423 ≤ (43353441437483/100000000000000 : ℝ)^3399 := by
    have hnat : (2630442543 : ℕ)^4423*100000000000000^3399 ≤ 43353441437483^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630442543 5000000000 43353441437483 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2793011033/5000000000 : ℝ)^4423 ≤ (468720022811/1000000000000 : ℝ)^3399 := by
    have hnat : (2793011033 : ℕ)^4423*1000000000000^3399 ≤ 468720022811^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2793011033 5000000000 468720022811 1000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (837291779/5000000000 : ℝ)^4423 ≤ (2443639068059/25000000000000 : ℝ)^3399 := by
    have hnat : (837291779 : ℕ)^4423*25000000000000^3399 ≤ 2443639068059^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837291779 5000000000 2443639068059 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2630442543/5000000000 : ℝ), (2793011033/5000000000 : ℝ), (-837291779/5000000000 : ℝ)] ![(43353441437483/100000000000000 : ℝ), (468720022811/1000000000000 : ℝ), (2443639068059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2630442543/5000000000 : ℝ)|^4423 ≤ (43353441437483/100000000000000 : ℝ)^3399
        have hw : |(2630442543/5000000000 : ℝ)|=(2630442543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2793011033/5000000000 : ℝ)|^4423 ≤ (468720022811/1000000000000 : ℝ)^3399
        have hw : |(2793011033/5000000000 : ℝ)|=(2793011033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-837291779/5000000000 : ℝ)|^4423 ≤ (2443639068059/25000000000000 : ℝ)^3399
        have hw : |(-837291779/5000000000 : ℝ)|=(837291779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s1_7 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2135609977/5000000000 : ℝ)*x 0 + (484363367/1000000000 : ℝ)*x 1 + (3760751631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135609977/5000000000 : ℝ)^4423 ≤ (16527993809937/50000000000000 : ℝ)^3399 := by
    have hnat : (2135609977 : ℕ)^4423*50000000000000^3399 ≤ 16527993809937^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135609977 5000000000 16527993809937 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (484363367/1000000000 : ℝ)^4423 ≤ (9733396207887/25000000000000 : ℝ)^3399 := by
    have hnat : (484363367 : ℕ)^4423*25000000000000^3399 ≤ 9733396207887^3399*1000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484363367 1000000000 9733396207887 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3760751631/10000000000 : ℝ)^4423 ≤ (7002606882341/25000000000000 : ℝ)^3399 := by
    have hnat : (3760751631 : ℕ)^4423*25000000000000^3399 ≤ 7002606882341^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3760751631 10000000000 7002606882341 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2135609977/5000000000 : ℝ), (484363367/1000000000 : ℝ), (3760751631/10000000000 : ℝ)] ![(16527993809937/50000000000000 : ℝ), (9733396207887/25000000000000 : ℝ), (7002606882341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2135609977/5000000000 : ℝ)|^4423 ≤ (16527993809937/50000000000000 : ℝ)^3399
        have hw : |(2135609977/5000000000 : ℝ)|=(2135609977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(484363367/1000000000 : ℝ)|^4423 ≤ (9733396207887/25000000000000 : ℝ)^3399
        have hw : |(484363367/1000000000 : ℝ)|=(484363367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3760751631/10000000000 : ℝ)|^4423 ≤ (7002606882341/25000000000000 : ℝ)^3399
        have hw : |(3760751631/10000000000 : ℝ)|=(3760751631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1463_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1041/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (457/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (317/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (149/800 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1041/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (457/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1041/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (457/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1041/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (457/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1041/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (457/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1041/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (457/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1041/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (457/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (457/20000 : ℝ) ^ (2211/512 : ℝ) ≤ (1023271476367/12500000000000000000 : ℝ) := by
    have hpowers : (457/20000 : ℝ)^2211 ≤ (1023271476367/12500000000000000000 : ℝ)^512 := by
      have hnat : (457 : ℕ)^2211*12500000000000000000^512 ≤ 1023271476367^512*20000^2211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        457 20000 1023271476367 12500000000000000000 2211 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (457/20000 : ℝ)) (X := (1023271476367/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1041/4000 : ℝ) ^ (2211/512 : ℝ) ≤ (37355721293767033/12500000000000000000 : ℝ) := by
    have hpowers : (1041/4000 : ℝ)^2211 ≤ (37355721293767033/12500000000000000000 : ℝ)^512 := by
      have hnat : (1041 : ℕ)^2211*12500000000000000000^512 ≤ 37355721293767033^512*4000^2211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1041 4000 37355721293767033 12500000000000000000 2211 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1041/4000 : ℝ)) (X := (37355721293767033/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250001023271476367/6250000000000000000 : ℝ) ≤ (10000000379133397/10000000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (6250001023271476367/6250000000000000000 : ℝ)^512 ≤ (10000000379133397/10000000000000000 : ℝ)^2211 := by
      have hnat : (6250001023271476367 : ℕ)^512*10000000000000000^2211 ≤ 10000000379133397^2211*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250001023271476367 6250000000000000000 10000000379133397 10000000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000379133397/10000000000000000 : ℝ)) (X := (6250001023271476367/6250000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (62686783722826217/62500000000000000 : ℝ) ≤ (10006912611411941/10000000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (62686783722826217/62500000000000000 : ℝ)^512 ≤ (10006912611411941/10000000000000000 : ℝ)^2211 := by
      have hnat : (62686783722826217 : ℕ)^512*10000000000000000^2211 ≤ 10006912611411941^2211*62500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62686783722826217 62500000000000000 10006912611411941 10000000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006912611411941/10000000000000000 : ℝ)) (X := (62686783722826217/62500000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6287355721293767033/6250000000000000000 : ℝ) ≤ (2002764968738097/2000000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (6287355721293767033/6250000000000000000 : ℝ)^512 ≤ (2002764968738097/2000000000000000 : ℝ)^2211 := by
      have hnat : (6287355721293767033 : ℕ)^512*2000000000000000^2211 ≤ 2002764968738097^2211*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6287355721293767033 6250000000000000000 2002764968738097 2000000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002764968738097/2000000000000000 : ℝ)) (X := (6287355721293767033/6250000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1023271476367/12500000000000000000 : ℝ) ≤ ((2373684200991138987/2374000000000000000 : ℝ)+2*(432014517409/148375000000000 : ℝ)*(457/20000 : ℝ))^(2211/512 : ℝ) := by
    rw [show (2373684200991138987/2374000000000000000 : ℝ)+2*(432014517409/148375000000000 : ℝ)*(457/20000 : ℝ)=(10000000379133397/10000000000000000 : ℝ) by norm_num, show 1+2*(1023271476367/12500000000000000000 : ℝ)=(6250001023271476367/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37355721293767033/12500000000000000000 : ℝ)+(1023271476367/12500000000000000000 : ℝ) ≤ ((2373684200991138987/2374000000000000000 : ℝ)+(432014517409/148375000000000 : ℝ)*((1041/4000 : ℝ)+(457/20000 : ℝ)))^(2211/512 : ℝ) := by
    rw [show (2373684200991138987/2374000000000000000 : ℝ)+(432014517409/148375000000000 : ℝ)*((1041/4000 : ℝ)+(457/20000 : ℝ))=(10006912611411941/10000000000000000 : ℝ) by norm_num, show 1+(37355721293767033/12500000000000000000 : ℝ)+(1023271476367/12500000000000000000 : ℝ)=(62686783722826217/62500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37355721293767033/12500000000000000000 : ℝ) ≤ ((2373684200991138987/2374000000000000000 : ℝ)+2*(432014517409/148375000000000 : ℝ)*(1041/4000 : ℝ))^(2211/512 : ℝ) := by
    rw [show (2373684200991138987/2374000000000000000 : ℝ)+2*(432014517409/148375000000000 : ℝ)*(1041/4000 : ℝ)=(2002764968738097/2000000000000000 : ℝ) by norm_num, show 1+2*(37355721293767033/12500000000000000000 : ℝ)=(6287355721293767033/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2373684200991138987/2374000000000000000 : ℝ)*(X 1 0+X 2 0)+(432014517409/148375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (457/20000 : ℝ)) (hi := (1041/4000 : ℝ)) (c := (2373684200991138987/2374000000000000000 : ℝ)) (alpha := (432014517409/148375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2373684200991138987/2374000000000000000 : ℝ)*(X 0 1+X 2 1)+(432014517409/148375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (457/20000 : ℝ)) (hi := (1041/4000 : ℝ)) (c := (2373684200991138987/2374000000000000000 : ℝ)) (alpha := (432014517409/148375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2373684200991138987/2374000000000000000 : ℝ)*(X 0 2+X 1 2)+(432014517409/148375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (457/20000 : ℝ)) (hi := (1041/4000 : ℝ)) (c := (2373684200991138987/2374000000000000000 : ℝ)) (alpha := (432014517409/148375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-59602713/312500000 : ℝ)*X 0 0+(698986853/1250000000 : ℝ)*X 0 1+(1017169739/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5393425973/10000000000 : ℝ)*X 1 0+(-2174755343/10000000000 : ℝ)*X 1 1+(40686807/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((539342781/1000000000 : ℝ)*X 2 0+(5085848861/10000000000 : ℝ)*X 2 1+(-2174755529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4270443307/10000000000 : ℝ)*X 0 0+(46848647/125000000 : ℝ)*X 0 1+(4856286251/10000000000 : ℝ)*X 0 2+(4270443307/10000000000 : ℝ)*X 1 0+(46848647/125000000 : ℝ)*X 1 1+(4856286251/10000000000 : ℝ)*X 1 2+(4270443307/10000000000 : ℝ)*X 2 0+(46848647/125000000 : ℝ)*X 2 1+(4856286251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-238455127/1250000000 : ℝ)*X 0 0+(5091626167/10000000000 : ℝ)*X 0 1+(5586022059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1315221303/2500000000 : ℝ)*X 1 0+(-334916667/2000000000 : ℝ)*X 1 1+(349126381/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2630442543/5000000000 : ℝ)*X 2 0+(2793011033/5000000000 : ℝ)*X 2 1+(-837291779/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2135609977/5000000000 : ℝ)*X 0 0+(484363367/1000000000 : ℝ)*X 0 1+(3760751631/10000000000 : ℝ)*X 0 2+(2135609977/5000000000 : ℝ)*X 1 0+(484363367/1000000000 : ℝ)*X 1 1+(3760751631/10000000000 : ℝ)*X 1 2+(2135609977/5000000000 : ℝ)*X 2 0+(484363367/1000000000 : ℝ)*X 2 1+(3760751631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (762260700979113162778655757/118700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (983703693/100000000000000 : ℝ)*(base19) + (1562397251/100000000000000 : ℝ)*(base23) + (78648123/100000000000000 : ℝ)*(upper3) + (50901721/100000000000000 : ℝ)*(upper4) + (1981581/3125000000000 : ℝ)*(upper5) + (719588030694119/50000000000000 : ℝ)*(major0) + (719588030694119/50000000000000 : ℝ)*(major1) + (1439176061388239/100000000000000 : ℝ)*(major2) + (494029703008667/25000000000000 : ℝ)*(sp0) + (1976134533660451/100000000000000 : ℝ)*(sp1) + (988066977483447/50000000000000 : ℝ)*(sp2) + (1409704040581/156250000000 : ℝ)*(sp3) + (4176332369/25000000000000 : ℝ)*(sp4) + (5805382437/100000000000000 : ℝ)*(sp7) + (451108195677139/50000000000000 : ℝ)*(f.failure) + (123508469835259/6250000000000 : ℝ)*(f.sum) + (41994723507559/7418750000000000000000000000 : ℝ)*base65 + (241234218997274547/118700000000000000000000000000000 : ℝ)*base68 + (2028049986362245893/237400000000000000000000000000000 : ℝ)*base69 + (236980899704174547/118700000000000000000000000000000 : ℝ)*base72 + (122381641527711/29675000000000000000000000000 : ℝ)*base73 + (2187161334652845893/237400000000000000000000000000000 : ℝ)*base75 + (779646997071346547/118700000000000000000000000000000 : ℝ)*base78 + (2130459526283546547/118700000000000000000000000000000 : ℝ)*base80 + (174773341901193/29675000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (51734041/5000000000000000000000 : ℝ)*base89 + (51734041/5000000000000000000000 : ℝ)*base91 + (1734041/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (424263671822730302919/185468750000000000000000000 : ℝ) := by norm_num
    linear_combination (330293647/50000000000000 : ℝ)*(base19) + (602196883/100000000000000 : ℝ)*(base23) + (444959/25000000000000 : ℝ)*(upper2) + (14645397/20000000000000 : ℝ)*(upper3) + (13460529/50000000000000 : ℝ)*(upper5) + (73653288997141/5000000000000 : ℝ)*(major0) + (73653288997141/5000000000000 : ℝ)*(major1) + (73653288997141/5000000000000 : ℝ)*(major2) + (4515227083/100000000000000 : ℝ)*(sp1) + (249129259/6250000000000 : ℝ)*(sp2) + (2022669700282659/100000000000000 : ℝ)*(sp4) + (1011332262234141/50000000000000 : ℝ)*(sp5) + (2022665112017631/100000000000000 : ℝ)*(sp6) + (36938471334091/4000000000000 : ℝ)*(sp7) + (36938471334091/4000000000000 : ℝ)*(f.failure) + (2022669700282659/100000000000000 : ℝ)*(f.sum) + (4495408402047/2967500000000000000000000000 : ℝ)*base65 + (26361857567269833/11870000000000000000000000000000 : ℝ)*base68 + (5573310549879833/11870000000000000000000000000000 : ℝ)*base70 + (27005299329430167/11870000000000000000000000000000 : ℝ)*base71 + (765437956919/5935000000000000000000000000 : ℝ)*base73 + (66029972205799833/11870000000000000000000000000000 : ℝ)*base76 + (94432082210620167/11870000000000000000000000000000 : ℝ)*base77 + (36346265413740167/11870000000000000000000000000000 : ℝ)*base79 + (13271234331981/5935000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1667329/400000000000000000000 : ℝ)*base89 + (1667329/400000000000000000000 : ℝ)*base91 + (1667329/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1463_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1041/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (457/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (317/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (149/800 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1463_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1463_s2_0 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-193796251/1000000000 : ℝ)*x 0 + (5450840137/10000000000 : ℝ)*x 1 + (260356059/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (193796251/1000000000 : ℝ)^4423 ≤ (2364162992151/20000000000000 : ℝ)^3399 := by
    have hnat : (193796251 : ℕ)^4423*20000000000000^3399 ≤ 2364162992151^3399*1000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193796251 1000000000 2364162992151 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5450840137/10000000000 : ℝ)^4423 ≤ (45401383214463/100000000000000 : ℝ)^3399 := by
    have hnat : (5450840137 : ℕ)^4423*100000000000000^3399 ≤ 45401383214463^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450840137 10000000000 45401383214463 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260356059/500000000 : ℝ)^4423 ≤ (42777801811273/100000000000000 : ℝ)^3399 := by
    have hnat : (260356059 : ℕ)^4423*100000000000000^3399 ≤ 42777801811273^3399*500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260356059 500000000 42777801811273 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-193796251/1000000000 : ℝ), (5450840137/10000000000 : ℝ), (260356059/500000000 : ℝ)] ![(2364162992151/20000000000000 : ℝ), (45401383214463/100000000000000 : ℝ), (42777801811273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-193796251/1000000000 : ℝ)|^4423 ≤ (2364162992151/20000000000000 : ℝ)^3399
        have hw : |(-193796251/1000000000 : ℝ)|=(193796251/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5450840137/10000000000 : ℝ)|^4423 ≤ (45401383214463/100000000000000 : ℝ)^3399
        have hw : |(5450840137/10000000000 : ℝ)|=(5450840137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260356059/500000000 : ℝ)|^4423 ≤ (42777801811273/100000000000000 : ℝ)^3399
        have hw : |(260356059/500000000 : ℝ)|=(260356059/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s2_1 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358028069/10000000000 : ℝ)*x 0 + (-2063177957/10000000000 : ℝ)*x 1 + (5207117997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358028069/10000000000 : ℝ)^4423 ≤ (44398024846931/100000000000000 : ℝ)^3399 := by
    have hnat : (5358028069 : ℕ)^4423*100000000000000^3399 ≤ 44398024846931^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358028069 10000000000 44398024846931 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063177957/10000000000 : ℝ)^4423 ≤ (3206051837591/25000000000000 : ℝ)^3399 := by
    have hnat : (2063177957 : ℕ)^4423*25000000000000^3399 ≤ 3206051837591^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063177957 10000000000 3206051837591 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5207117997/10000000000 : ℝ)^4423 ≤ (42777767784313/100000000000000 : ℝ)^3399 := by
    have hnat : (5207117997 : ℕ)^4423*100000000000000^3399 ≤ 42777767784313^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207117997 10000000000 42777767784313 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358028069/10000000000 : ℝ), (-2063177957/10000000000 : ℝ), (5207117997/10000000000 : ℝ)] ![(44398024846931/100000000000000 : ℝ), (3206051837591/25000000000000 : ℝ), (42777767784313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358028069/10000000000 : ℝ)|^4423 ≤ (44398024846931/100000000000000 : ℝ)^3399
        have hw : |(5358028069/10000000000 : ℝ)|=(5358028069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2063177957/10000000000 : ℝ)|^4423 ≤ (3206051837591/25000000000000 : ℝ)^3399
        have hw : |(-2063177957/10000000000 : ℝ)|=(2063177957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5207117997/10000000000 : ℝ)|^4423 ≤ (42777767784313/100000000000000 : ℝ)^3399
        have hw : |(5207117997/10000000000 : ℝ)|=(5207117997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s2_2 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679013061/5000000000 : ℝ)*x 0 + (5207119583/10000000000 : ℝ)*x 1 + (-257897307/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679013061/5000000000 : ℝ)^4423 ≤ (11099500963291/25000000000000 : ℝ)^3399 := by
    have hnat : (2679013061 : ℕ)^4423*25000000000000^3399 ≤ 11099500963291^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679013061 5000000000 11099500963291 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5207119583/10000000000 : ℝ)^4423 ≤ (10694446184749/25000000000000 : ℝ)^3399 := by
    have hnat : (5207119583 : ℕ)^4423*25000000000000^3399 ≤ 10694446184749^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207119583 10000000000 10694446184749 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257897307/1250000000 : ℝ)^4423 ≤ (12824211386447/100000000000000 : ℝ)^3399 := by
    have hnat : (257897307 : ℕ)^4423*100000000000000^3399 ≤ 12824211386447^3399*1250000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257897307 1250000000 12824211386447 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679013061/5000000000 : ℝ), (5207119583/10000000000 : ℝ), (-257897307/1250000000 : ℝ)] ![(11099500963291/25000000000000 : ℝ), (10694446184749/25000000000000 : ℝ), (12824211386447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679013061/5000000000 : ℝ)|^4423 ≤ (11099500963291/25000000000000 : ℝ)^3399
        have hw : |(2679013061/5000000000 : ℝ)|=(2679013061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5207119583/10000000000 : ℝ)|^4423 ≤ (10694446184749/25000000000000 : ℝ)^3399
        have hw : |(5207119583/10000000000 : ℝ)|=(5207119583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-257897307/1250000000 : ℝ)|^4423 ≤ (12824211386447/100000000000000 : ℝ)^3399
        have hw : |(-257897307/1250000000 : ℝ)|=(257897307/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s2_3 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073043441/2500000000 : ℝ)*x 0 + (2016300293/5000000000 : ℝ)*x 1 + (2283214307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073043441/2500000000 : ℝ)^4423 ≤ (66534330027/200000000000 : ℝ)^3399 := by
    have hnat : (1073043441 : ℕ)^4423*200000000000^3399 ≤ 66534330027^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073043441 2500000000 66534330027 200000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2016300293/5000000000 : ℝ)^4423 ≤ (6134678417651/20000000000000 : ℝ)^3399 := by
    have hnat : (2016300293 : ℕ)^4423*20000000000000^3399 ≤ 6134678417651^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016300293 5000000000 6134678417651 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2283214307/5000000000 : ℝ)^4423 ≤ (36059442882237/100000000000000 : ℝ)^3399 := by
    have hnat : (2283214307 : ℕ)^4423*100000000000000^3399 ≤ 36059442882237^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283214307 5000000000 36059442882237 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073043441/2500000000 : ℝ), (2016300293/5000000000 : ℝ), (2283214307/5000000000 : ℝ)] ![(66534330027/200000000000 : ℝ), (6134678417651/20000000000000 : ℝ), (36059442882237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073043441/2500000000 : ℝ)|^4423 ≤ (66534330027/200000000000 : ℝ)^3399
        have hw : |(1073043441/2500000000 : ℝ)|=(1073043441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2016300293/5000000000 : ℝ)|^4423 ≤ (6134678417651/20000000000000 : ℝ)^3399
        have hw : |(2016300293/5000000000 : ℝ)|=(2016300293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2283214307/5000000000 : ℝ)|^4423 ≤ (36059442882237/100000000000000 : ℝ)^3399
        have hw : |(2283214307/5000000000 : ℝ)|=(2283214307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s2_4 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-38760051/200000000 : ℝ)*x 0 + (5208467783/10000000000 : ℝ)*x 1 + (5449482539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38760051/200000000 : ℝ)^4423 ≤ (11821132767597/100000000000000 : ℝ)^3399 := by
    have hnat : (38760051 : ℕ)^4423*100000000000000^3399 ≤ 11821132767597^3399*200000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38760051 200000000 11821132767597 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5208467783/10000000000 : ℝ)^4423 ≤ (21396098925697/50000000000000 : ℝ)^3399 := by
    have hnat : (5208467783 : ℕ)^4423*50000000000000^3399 ≤ 21396098925697^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5208467783 10000000000 21396098925697 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5449482539/10000000000 : ℝ)^4423 ≤ (5673333670623/12500000000000 : ℝ)^3399 := by
    have hnat : (5449482539 : ℕ)^4423*12500000000000^3399 ≤ 5673333670623^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449482539 10000000000 5673333670623 12500000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38760051/200000000 : ℝ), (5208467783/10000000000 : ℝ), (5449482539/10000000000 : ℝ)] ![(11821132767597/100000000000000 : ℝ), (21396098925697/50000000000000 : ℝ), (5673333670623/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38760051/200000000 : ℝ)|^4423 ≤ (11821132767597/100000000000000 : ℝ)^3399
        have hw : |(-38760051/200000000 : ℝ)|=(38760051/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5208467783/10000000000 : ℝ)|^4423 ≤ (21396098925697/50000000000000 : ℝ)^3399
        have hw : |(5208467783/10000000000 : ℝ)|=(5208467783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5449482539/10000000000 : ℝ)|^4423 ≤ (5673333670623/12500000000000 : ℝ)^3399
        have hw : |(5449482539/10000000000 : ℝ)|=(5449482539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s2_5 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661806789/1250000000 : ℝ)*x 0 + (-1820813297/10000000000 : ℝ)*x 1 + (5449482793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661806789/1250000000 : ℝ)^4423 ≤ (4371376152831/10000000000000 : ℝ)^3399 := by
    have hnat : (661806789 : ℕ)^4423*10000000000000^3399 ≤ 4371376152831^3399*1250000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661806789 1250000000 4371376152831 10000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1820813297/10000000000 : ℝ)^4423 ≤ (1089956634493/10000000000000 : ℝ)^3399 := by
    have hnat : (1820813297 : ℕ)^4423*10000000000000^3399 ≤ 1089956634493^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1820813297 10000000000 1089956634493 10000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5449482793/10000000000 : ℝ)^4423 ≤ (45386672117771/100000000000000 : ℝ)^3399 := by
    have hnat : (5449482793 : ℕ)^4423*100000000000000^3399 ≤ 45386672117771^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449482793 10000000000 45386672117771 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661806789/1250000000 : ℝ), (-1820813297/10000000000 : ℝ), (5449482793/10000000000 : ℝ)] ![(4371376152831/10000000000000 : ℝ), (1089956634493/10000000000000 : ℝ), (45386672117771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661806789/1250000000 : ℝ)|^4423 ≤ (4371376152831/10000000000000 : ℝ)^3399
        have hw : |(661806789/1250000000 : ℝ)|=(661806789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1820813297/10000000000 : ℝ)|^4423 ≤ (1089956634493/10000000000000 : ℝ)^3399
        have hw : |(-1820813297/10000000000 : ℝ)|=(1820813297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5449482793/10000000000 : ℝ)|^4423 ≤ (45386672117771/100000000000000 : ℝ)^3399
        have hw : |(5449482793/10000000000 : ℝ)|=(5449482793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s2_6 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26472271/50000000 : ℝ)*x 0 + (681185353/1250000000 : ℝ)*x 1 + (-56900419/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26472271/50000000 : ℝ)^4423 ≤ (43713760324991/100000000000000 : ℝ)^3399 := by
    have hnat : (26472271 : ℕ)^4423*100000000000000^3399 ≤ 43713760324991^3399*50000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26472271 50000000 43713760324991 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (681185353/1250000000 : ℝ)^4423 ≤ (45386672453741/100000000000000 : ℝ)^3399 := by
    have hnat : (681185353 : ℕ)^4423*100000000000000^3399 ≤ 45386672453741^3399*1250000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681185353 1250000000 45386672453741 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56900419/312500000 : ℝ)^4423 ≤ (2724891802391/25000000000000 : ℝ)^3399 := by
    have hnat : (56900419 : ℕ)^4423*25000000000000^3399 ≤ 2724891802391^3399*312500000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56900419 312500000 2724891802391 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26472271/50000000 : ℝ), (681185353/1250000000 : ℝ), (-56900419/312500000 : ℝ)] ![(43713760324991/100000000000000 : ℝ), (45386672453741/100000000000000 : ℝ), (2724891802391/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26472271/50000000 : ℝ)|^4423 ≤ (43713760324991/100000000000000 : ℝ)^3399
        have hw : |(26472271/50000000 : ℝ)|=(26472271/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(681185353/1250000000 : ℝ)|^4423 ≤ (45386672453741/100000000000000 : ℝ)^3399
        have hw : |(681185353/1250000000 : ℝ)|=(681185353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-56900419/312500000 : ℝ)|^4423 ≤ (2724891802391/25000000000000 : ℝ)^3399
        have hw : |(-56900419/312500000 : ℝ)|=(56900419/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s2_7 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2146129589/5000000000 : ℝ)*x 0 + (285217261/625000000 : ℝ)*x 1 + (807115607/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146129589/5000000000 : ℝ)^4423 ≤ (16634013236271/50000000000000 : ℝ)^3399 := by
    have hnat : (2146129589 : ℕ)^4423*50000000000000^3399 ≤ 16634013236271^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146129589 5000000000 16634013236271 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285217261/625000000 : ℝ)^4423 ≤ (9007276925219/25000000000000 : ℝ)^3399 := by
    have hnat : (285217261 : ℕ)^4423*25000000000000^3399 ≤ 9007276925219^3399*625000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285217261 625000000 9007276925219 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (807115607/2000000000 : ℝ)^4423 ≤ (479732278297/1562500000000 : ℝ)^3399 := by
    have hnat : (807115607 : ℕ)^4423*1562500000000^3399 ≤ 479732278297^3399*2000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807115607 2000000000 479732278297 1562500000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2146129589/5000000000 : ℝ), (285217261/625000000 : ℝ), (807115607/2000000000 : ℝ)] ![(16634013236271/50000000000000 : ℝ), (9007276925219/25000000000000 : ℝ), (479732278297/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2146129589/5000000000 : ℝ)|^4423 ≤ (16634013236271/50000000000000 : ℝ)^3399
        have hw : |(2146129589/5000000000 : ℝ)|=(2146129589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(285217261/625000000 : ℝ)|^4423 ≤ (9007276925219/25000000000000 : ℝ)^3399
        have hw : |(285217261/625000000 : ℝ)|=(285217261/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(807115607/2000000000 : ℝ)|^4423 ≤ (479732278297/1562500000000 : ℝ)^3399
        have hw : |(807115607/2000000000 : ℝ)|=(807115607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1463_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (149/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (317/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (5271/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (157/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (149/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (317/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (149/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (317/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (149/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (317/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (149/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (317/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (149/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (317/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (149/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (317/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (317/4000 : ℝ) ^ (2211/512 : ℝ) ≤ (1759880501460197/100000000000000000000 : ℝ) := by
    have hpowers : (317/4000 : ℝ)^2211 ≤ (1759880501460197/100000000000000000000 : ℝ)^512 := by
      have hnat : (317 : ℕ)^2211*100000000000000000000^512 ≤ 1759880501460197^512*4000^2211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        317 4000 1759880501460197 100000000000000000000 2211 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (317/4000 : ℝ)) (X := (1759880501460197/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hpowhi : (149/800 : ℝ) ^ (2211/512 : ℝ) ≤ (70471486756349687/100000000000000000000 : ℝ) := by
    have hpowers : (149/800 : ℝ)^2211 ≤ (70471486756349687/100000000000000000000 : ℝ)^512 := by
      have hnat : (149 : ℕ)^2211*100000000000000000000^512 ≤ 70471486756349687^512*800^2211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        149 800 70471486756349687 100000000000000000000 2211 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (149/800 : ℝ)) (X := (70471486756349687/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001759880501460197/50000000000000000000 : ℝ) ≤ (10000081505801137/10000000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (50001759880501460197/50000000000000000000 : ℝ)^512 ≤ (10000081505801137/10000000000000000 : ℝ)^2211 := by
      have hnat : (50001759880501460197 : ℕ)^512*10000000000000000^2211 ≤ 10000081505801137^2211*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001759880501460197 50000000000000000000 10000081505801137 10000000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000081505801137/10000000000000000 : ℝ)) (X := (50001759880501460197/50000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25018057841814452471/25000000000000000000 : ℝ) ≤ (1250209024202201/1250000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (25018057841814452471/25000000000000000000 : ℝ)^512 ≤ (1250209024202201/1250000000000000 : ℝ)^2211 := by
      have hnat : (25018057841814452471 : ℕ)^512*1250000000000000^2211 ≤ 1250209024202201^2211*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018057841814452471 25000000000000000000 1250209024202201 1250000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250209024202201/1250000000000000 : ℝ)) (X := (25018057841814452471/25000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50070471486756349687/50000000000000000000 : ℝ) ≤ (10003262881434079/10000000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (50070471486756349687/50000000000000000000 : ℝ)^512 ≤ (10003262881434079/10000000000000000 : ℝ)^2211 := by
      have hnat : (50070471486756349687 : ℕ)^512*10000000000000000^2211 ≤ 10003262881434079^2211*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50070471486756349687 50000000000000000000 10003262881434079 10000000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003262881434079/10000000000000000 : ℝ)) (X := (50070471486756349687/50000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1759880501460197/100000000000000000000 : ℝ) ≤ ((2139513194203622011/2140000000000000000 : ℝ)+2*(1590687816471/1070000000000000 : ℝ)*(317/4000 : ℝ))^(2211/512 : ℝ) := by
    rw [show (2139513194203622011/2140000000000000000 : ℝ)+2*(1590687816471/1070000000000000 : ℝ)*(317/4000 : ℝ)=(10000081505801137/10000000000000000 : ℝ) by norm_num, show 1+2*(1759880501460197/100000000000000000000 : ℝ)=(50001759880501460197/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(70471486756349687/100000000000000000000 : ℝ)+(1759880501460197/100000000000000000000 : ℝ) ≤ ((2139513194203622011/2140000000000000000 : ℝ)+(1590687816471/1070000000000000 : ℝ)*((149/800 : ℝ)+(317/4000 : ℝ)))^(2211/512 : ℝ) := by
    rw [show (2139513194203622011/2140000000000000000 : ℝ)+(1590687816471/1070000000000000 : ℝ)*((149/800 : ℝ)+(317/4000 : ℝ))=(1250209024202201/1250000000000000 : ℝ) by norm_num, show 1+(70471486756349687/100000000000000000000 : ℝ)+(1759880501460197/100000000000000000000 : ℝ)=(25018057841814452471/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(70471486756349687/100000000000000000000 : ℝ) ≤ ((2139513194203622011/2140000000000000000 : ℝ)+2*(1590687816471/1070000000000000 : ℝ)*(149/800 : ℝ))^(2211/512 : ℝ) := by
    rw [show (2139513194203622011/2140000000000000000 : ℝ)+2*(1590687816471/1070000000000000 : ℝ)*(149/800 : ℝ)=(10003262881434079/10000000000000000 : ℝ) by norm_num, show 1+2*(70471486756349687/100000000000000000000 : ℝ)=(50070471486756349687/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2139513194203622011/2140000000000000000 : ℝ)*(X 1 0+X 2 0)+(1590687816471/1070000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (317/4000 : ℝ)) (hi := (149/800 : ℝ)) (c := (2139513194203622011/2140000000000000000 : ℝ)) (alpha := (1590687816471/1070000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2139513194203622011/2140000000000000000 : ℝ)*(X 0 1+X 2 1)+(1590687816471/1070000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (317/4000 : ℝ)) (hi := (149/800 : ℝ)) (c := (2139513194203622011/2140000000000000000 : ℝ)) (alpha := (1590687816471/1070000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2139513194203622011/2140000000000000000 : ℝ)*(X 0 2+X 1 2)+(1590687816471/1070000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (317/4000 : ℝ)) (hi := (149/800 : ℝ)) (c := (2139513194203622011/2140000000000000000 : ℝ)) (alpha := (1590687816471/1070000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-193796251/1000000000 : ℝ)*X 0 0+(5450840137/10000000000 : ℝ)*X 0 1+(260356059/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5358028069/10000000000 : ℝ)*X 1 0+(-2063177957/10000000000 : ℝ)*X 1 1+(5207117997/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2679013061/5000000000 : ℝ)*X 2 0+(5207119583/10000000000 : ℝ)*X 2 1+(-257897307/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1073043441/2500000000 : ℝ)*X 0 0+(2016300293/5000000000 : ℝ)*X 0 1+(2283214307/5000000000 : ℝ)*X 0 2+(1073043441/2500000000 : ℝ)*X 1 0+(2016300293/5000000000 : ℝ)*X 1 1+(2283214307/5000000000 : ℝ)*X 1 2+(1073043441/2500000000 : ℝ)*X 2 0+(2016300293/5000000000 : ℝ)*X 2 1+(2283214307/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-38760051/200000000 : ℝ)*X 0 0+(5208467783/10000000000 : ℝ)*X 0 1+(5449482539/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661806789/1250000000 : ℝ)*X 1 0+(-1820813297/10000000000 : ℝ)*X 1 1+(5449482793/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((26472271/50000000 : ℝ)*X 2 0+(681185353/1250000000 : ℝ)*X 2 1+(-56900419/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2146129589/5000000000 : ℝ)*X 0 0+(285217261/625000000 : ℝ)*X 0 1+(807115607/2000000000 : ℝ)*X 0 2+(2146129589/5000000000 : ℝ)*X 1 0+(285217261/625000000 : ℝ)*X 1 1+(807115607/2000000000 : ℝ)*X 1 2+(2146129589/5000000000 : ℝ)*X 2 0+(285217261/625000000 : ℝ)*X 2 1+(807115607/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (222648646116966768825537/26750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (298083479/100000000000000 : ℝ)*(base19) + (34211287/50000000000000 : ℝ)*(upper2) + (596726733/100000000000000 : ℝ)*(lower4) + (233391797/50000000000000 : ℝ)*(upper5) + (1494095946095351/50000000000000 : ℝ)*(major0) + (1494095946095351/50000000000000 : ℝ)*(major1) + (1494095946095351/50000000000000 : ℝ)*(major2) + (512886550996199/12500000000000 : ℝ)*(sp0) + (205152205916399/5000000000000 : ℝ)*(sp1) + (2051520163279461/50000000000000 : ℝ)*(sp2) + (234160333166781/12500000000000 : ℝ)*(sp3) + (11997889533/25000000000000 : ℝ)*(sp5) + (5208141067/10000000000000 : ℝ)*(sp6) + (2108408437/25000000000000 : ℝ)*(sp7) + (468322774741999/25000000000000 : ℝ)*(f.failure) + (512886550996199/12500000000000 : ℝ)*(f.sum) + (1202916435291679/26750000000000000000000000000 : ℝ)*base66 + (724029380061012861/107000000000000000000000000000000 : ℝ)*base67 + (1076693407662987139/107000000000000000000000000000000 : ℝ)*base70 + (413561032681012861/107000000000000000000000000000000 : ℝ)*base71 + (76588863430321/26750000000000000000000000000 : ℝ)*base73 + (916270466494987139/107000000000000000000000000000000 : ℝ)*base76 + (8403275206078987139/107000000000000000000000000000000 : ℝ)*base78 + (418460117347012861/107000000000000000000000000000000 : ℝ)*base79 + (111957425921321/26750000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (14217619/2500000000000000000000 : ℝ)*base90 + (14217619/2500000000000000000000 : ℝ)*base92 + (14217619/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (331747104605299267786268997/107000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83923437/100000000000000 : ℝ)*(base19) + (33128373/25000000000000 : ℝ)*(base23) + (15058449/25000000000000 : ℝ)*(upper3) + (33377537/50000000000000 : ℝ)*(lower4) + (302171298064391/10000000000000 : ℝ)*(major0) + (302171298064391/10000000000000 : ℝ)*(major1) + (3021712980643911/100000000000000 : ℝ)*(major2) + (859689309/25000000000000 : ℝ)*(sp1) + (4294714689/100000000000000 : ℝ)*(sp2) + (259056077/100000000000000 : ℝ)*(sp3) + (2074560230197529/50000000000000 : ℝ)*(sp4) + (2074558468857193/50000000000000 : ℝ)*(sp5) + (2074558016583439/50000000000000 : ℝ)*(sp6) + (473576284622167/25000000000000 : ℝ)*(sp7) + (378861079508949/20000000000000 : ℝ)*(f.failure) + (2074560230197529/50000000000000 : ℝ)*(f.sum) + (567067753524309/107000000000000000000000000000 : ℝ)*base66 + (123867613591073499/21400000000000000000000000000000 : ℝ)*base68 + (233820018035945021/214000000000000000000000000000000 : ℝ)*base69 + (460846936752673499/21400000000000000000000000000000 : ℝ)*base72 + (31079755527691/107000000000000000000000000000 : ℝ)*base73 + (2259919774643945021/214000000000000000000000000000000 : ℝ)*base75 + (191099298674767699/21400000000000000000000000000000 : ℝ)*base78 + (326007904497367699/21400000000000000000000000000000 : ℝ)*base80 + (13401973146661/5350000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (15774431/2000000000000000000000 : ℝ)*base89 + (15774431/2000000000000000000000 : ℝ)*base91 + (4225569/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1463_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (149/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (317/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5271/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (157/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1463_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1463_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5271/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (157/1000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1463_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1463_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1463_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5271/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (157/1000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1463_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
