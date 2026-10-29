-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1457_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:07:38.403387+00:00
-- url     : https://prove2.me/submissions/4ef99c41-9a6a-4fbc-9a74-282ada003760

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
theorem support_rectangle_w1457_box_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-894989709/5000000000 : ℝ)*x 0 + (2692525363/5000000000 : ℝ)*x 1 + (1077009959/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (894989709/5000000000 : ℝ)^4417 ≤ (10650235337529/100000000000000 : ℝ)^3393 := by
    have hnat : (894989709 : ℕ)^4417*100000000000000^3393 ≤ 10650235337529^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894989709 5000000000 10650235337529 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692525363/5000000000 : ℝ)^4417 ≤ (22337443675749/50000000000000 : ℝ)^3393 := by
    have hnat : (2692525363 : ℕ)^4417*50000000000000^3393 ≤ 22337443675749^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692525363 5000000000 22337443675749 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077009959/2000000000 : ℝ)^4417 ≤ (893497545937/2000000000000 : ℝ)^3393 := by
    have hnat : (1077009959 : ℕ)^4417*2000000000000^3393 ≤ 893497545937^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077009959 2000000000 893497545937 2000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-894989709/5000000000 : ℝ), (2692525363/5000000000 : ℝ), (1077009959/2000000000 : ℝ)] ![(10650235337529/100000000000000 : ℝ), (22337443675749/50000000000000 : ℝ), (893497545937/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-894989709/5000000000 : ℝ)|^4417 ≤ (10650235337529/100000000000000 : ℝ)^3393
        have hw : |(-894989709/5000000000 : ℝ)|=(894989709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692525363/5000000000 : ℝ)|^4417 ≤ (22337443675749/50000000000000 : ℝ)^3393
        have hw : |(2692525363/5000000000 : ℝ)|=(2692525363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077009959/2000000000 : ℝ)|^4417 ≤ (893497545937/2000000000000 : ℝ)^3393
        have hw : |(1077009959/2000000000 : ℝ)|=(1077009959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_box_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286239257/10000000000 : ℝ)*x 0 + (-376141/1953125 : ℝ)*x 1 + (1346262401/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286239257/10000000000 : ℝ)^4417 ≤ (43610707095727/100000000000000 : ℝ)^3393 := by
    have hnat : (5286239257 : ℕ)^4417*100000000000000^3393 ≤ 43610707095727^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286239257 10000000000 43610707095727 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (376141/1953125 : ℝ)^4417 ≤ (5857208827563/50000000000000 : ℝ)^3393 := by
    have hnat : (376141 : ℕ)^4417*50000000000000^3393 ≤ 5857208827563^3393*1953125^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376141 1953125 5857208827563 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346262401/2500000000 : ℝ)^4417 ≤ (44674875234081/100000000000000 : ℝ)^3393 := by
    have hnat : (1346262401 : ℕ)^4417*100000000000000^3393 ≤ 44674875234081^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346262401 2500000000 44674875234081 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286239257/10000000000 : ℝ), (-376141/1953125 : ℝ), (1346262401/2500000000 : ℝ)] ![(43610707095727/100000000000000 : ℝ), (5857208827563/50000000000000 : ℝ), (44674875234081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286239257/10000000000 : ℝ)|^4417 ≤ (43610707095727/100000000000000 : ℝ)^3393
        have hw : |(5286239257/10000000000 : ℝ)|=(5286239257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-376141/1953125 : ℝ)|^4417 ≤ (5857208827563/50000000000000 : ℝ)^3393
        have hw : |(-376141/1953125 : ℝ)|=(376141/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346262401/2500000000 : ℝ)|^4417 ≤ (44674875234081/100000000000000 : ℝ)^3393
        have hw : |(1346262401/2500000000 : ℝ)|=(1346262401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_box_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057247843/2000000000 : ℝ)*x 0 + (5385050499/10000000000 : ℝ)*x 1 + (-481460189/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057247843/2000000000 : ℝ)^4417 ≤ (21805353322331/50000000000000 : ℝ)^3393 := by
    have hnat : (1057247843 : ℕ)^4417*50000000000000^3393 ≤ 21805353322331^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057247843 2000000000 21805353322331 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385050499/10000000000 : ℝ)^4417 ≤ (8934976979987/20000000000000 : ℝ)^3393 := by
    have hnat : (5385050499 : ℕ)^4417*20000000000000^3393 ≤ 8934976979987^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385050499 10000000000 8934976979987 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (481460189/2500000000 : ℝ)^4417 ≤ (11714408437979/100000000000000 : ℝ)^3393 := by
    have hnat : (481460189 : ℕ)^4417*100000000000000^3393 ≤ 11714408437979^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481460189 2500000000 11714408437979 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057247843/2000000000 : ℝ), (5385050499/10000000000 : ℝ), (-481460189/2500000000 : ℝ)] ![(21805353322331/50000000000000 : ℝ), (8934976979987/20000000000000 : ℝ), (11714408437979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057247843/2000000000 : ℝ)|^4417 ≤ (21805353322331/50000000000000 : ℝ)^3393
        have hw : |(1057247843/2000000000 : ℝ)|=(1057247843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385050499/10000000000 : ℝ)|^4417 ≤ (8934976979987/20000000000000 : ℝ)^3393
        have hw : |(5385050499/10000000000 : ℝ)|=(5385050499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-481460189/2500000000 : ℝ)|^4417 ≤ (11714408437979/100000000000000 : ℝ)^3393
        have hw : |(-481460189/2500000000 : ℝ)|=(481460189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_box_3 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2221583539/5000000000 : ℝ)*x 0 + (4228205273/10000000000 : ℝ)*x 1 + (4228205783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2221583539/5000000000 : ℝ)^4417 ≤ (8695750324187/25000000000000 : ℝ)^3393 := by
    have hnat : (2221583539 : ℕ)^4417*25000000000000^3393 ≤ 8695750324187^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221583539 5000000000 8695750324187 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4228205273/10000000000 : ℝ)^4417 ≤ (4076062098221/12500000000000 : ℝ)^3393 := by
    have hnat : (4228205273 : ℕ)^4417*12500000000000^3393 ≤ 4076062098221^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228205273 10000000000 4076062098221 12500000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228205783/10000000000 : ℝ)^4417 ≤ (16304250952993/50000000000000 : ℝ)^3393 := by
    have hnat : (4228205783 : ℕ)^4417*50000000000000^3393 ≤ 16304250952993^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228205783 10000000000 16304250952993 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2221583539/5000000000 : ℝ), (4228205273/10000000000 : ℝ), (4228205783/10000000000 : ℝ)] ![(8695750324187/25000000000000 : ℝ), (4076062098221/12500000000000 : ℝ), (16304250952993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2221583539/5000000000 : ℝ)|^4417 ≤ (8695750324187/25000000000000 : ℝ)^3393
        have hw : |(2221583539/5000000000 : ℝ)|=(2221583539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4228205273/10000000000 : ℝ)|^4417 ≤ (4076062098221/12500000000000 : ℝ)^3393
        have hw : |(4228205273/10000000000 : ℝ)|=(4228205273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228205783/10000000000 : ℝ)|^4417 ≤ (16304250952993/50000000000000 : ℝ)^3393
        have hw : |(4228205783/10000000000 : ℝ)|=(4228205783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_box_4 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1055013603/5000000000 : ℝ)*x 0 + (526691231/1000000000 : ℝ)*x 1 + (263345599/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055013603/5000000000 : ℝ)^4417 ≤ (824593070793/6250000000000 : ℝ)^3393 := by
    have hnat : (1055013603 : ℕ)^4417*6250000000000^3393 ≤ 824593070793^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055013603 5000000000 824593070793 6250000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526691231/1000000000 : ℝ)^4417 ≤ (21701628596003/50000000000000 : ℝ)^3393 := by
    have hnat : (526691231 : ℕ)^4417*50000000000000^3393 ≤ 21701628596003^3393*1000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526691231 1000000000 21701628596003 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263345599/500000000 : ℝ)^4417 ≤ (43403253651839/100000000000000 : ℝ)^3393 := by
    have hnat : (263345599 : ℕ)^4417*100000000000000^3393 ≤ 43403253651839^3393*500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263345599 500000000 43403253651839 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1055013603/5000000000 : ℝ), (526691231/1000000000 : ℝ), (263345599/500000000 : ℝ)] ![(824593070793/6250000000000 : ℝ), (21701628596003/50000000000000 : ℝ), (43403253651839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1055013603/5000000000 : ℝ)|^4417 ≤ (824593070793/6250000000000 : ℝ)^3393
        have hw : |(-1055013603/5000000000 : ℝ)|=(1055013603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526691231/1000000000 : ℝ)|^4417 ≤ (21701628596003/50000000000000 : ℝ)^3393
        have hw : |(526691231/1000000000 : ℝ)|=(526691231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263345599/500000000 : ℝ)|^4417 ≤ (43403253651839/100000000000000 : ℝ)^3393
        have hw : |(263345599/500000000 : ℝ)|=(263345599/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_box_5 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268441203/500000000 : ℝ)*x 0 + (-24674737/125000000 : ℝ)*x 1 + (5266912331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268441203/500000000 : ℝ)^4417 ≤ (44499721741239/100000000000000 : ℝ)^3393 := by
    have hnat : (268441203 : ℕ)^4417*100000000000000^3393 ≤ 44499721741239^3393*500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268441203 500000000 44499721741239 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24674737/125000000 : ℝ)^4417 ≤ (12097020831691/100000000000000 : ℝ)^3393 := by
    have hnat : (24674737 : ℕ)^4417*100000000000000^3393 ≤ 12097020831691^3393*125000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24674737 125000000 12097020831691 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266912331/10000000000 : ℝ)^4417 ≤ (43403257417289/100000000000000 : ℝ)^3393 := by
    have hnat : (5266912331 : ℕ)^4417*100000000000000^3393 ≤ 43403257417289^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266912331 10000000000 43403257417289 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268441203/500000000 : ℝ), (-24674737/125000000 : ℝ), (5266912331/10000000000 : ℝ)] ![(44499721741239/100000000000000 : ℝ), (12097020831691/100000000000000 : ℝ), (43403257417289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268441203/500000000 : ℝ)|^4417 ≤ (44499721741239/100000000000000 : ℝ)^3393
        have hw : |(268441203/500000000 : ℝ)|=(268441203/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-24674737/125000000 : ℝ)|^4417 ≤ (12097020831691/100000000000000 : ℝ)^3393
        have hw : |(-24674737/125000000 : ℝ)|=(24674737/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266912331/10000000000 : ℝ)|^4417 ≤ (43403257417289/100000000000000 : ℝ)^3393
        have hw : |(5266912331/10000000000 : ℝ)|=(5266912331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_box_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684411931/5000000000 : ℝ)*x 0 + (329182009/625000000 : ℝ)*x 1 + (-1973979479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684411931/5000000000 : ℝ)^4417 ≤ (22249859802409/50000000000000 : ℝ)^3393 := by
    have hnat : (2684411931 : ℕ)^4417*50000000000000^3393 ≤ 22249859802409^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684411931 5000000000 22249859802409 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329182009/625000000 : ℝ)^4417 ≤ (8680651082239/20000000000000 : ℝ)^3393 := by
    have hnat : (329182009 : ℕ)^4417*20000000000000^3393 ≤ 8680651082239^3393*625000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329182009 625000000 8680651082239 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1973979479/10000000000 : ℝ)^4417 ≤ (2419404994427/20000000000000 : ℝ)^3393 := by
    have hnat : (1973979479 : ℕ)^4417*20000000000000^3393 ≤ 2419404994427^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973979479 10000000000 2419404994427 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684411931/5000000000 : ℝ), (329182009/625000000 : ℝ), (-1973979479/10000000000 : ℝ)] ![(22249859802409/50000000000000 : ℝ), (8680651082239/20000000000000 : ℝ), (2419404994427/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684411931/5000000000 : ℝ)|^4417 ≤ (22249859802409/50000000000000 : ℝ)^3393
        have hw : |(2684411931/5000000000 : ℝ)|=(2684411931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329182009/625000000 : ℝ)|^4417 ≤ (8680651082239/20000000000000 : ℝ)^3393
        have hw : |(329182009/625000000 : ℝ)|=(329182009/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1973979479/10000000000 : ℝ)|^4417 ≤ (2419404994427/20000000000000 : ℝ)^3393
        have hw : |(-1973979479/10000000000 : ℝ)|=(1973979479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_box_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (129706023/312500000 : ℝ)*x 0 + (4374442611/10000000000 : ℝ)*x 1 + (4374442583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129706023/312500000 : ℝ)^4417 ≤ (31831462243151/100000000000000 : ℝ)^3393 := by
    have hnat : (129706023 : ℕ)^4417*100000000000000^3393 ≤ 31831462243151^3393*312500000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129706023 312500000 31831462243151 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4374442611/10000000000 : ℝ)^4417 ≤ (852106725337/2500000000000 : ℝ)^3393 := by
    have hnat : (4374442611 : ℕ)^4417*2500000000000^3393 ≤ 852106725337^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374442611 10000000000 852106725337 2500000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4374442583/10000000000 : ℝ)^4417 ≤ (3408426872947/10000000000000 : ℝ)^3393 := by
    have hnat : (4374442583 : ℕ)^4417*10000000000000^3393 ≤ 3408426872947^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374442583 10000000000 3408426872947 10000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129706023/312500000 : ℝ), (4374442611/10000000000 : ℝ), (4374442583/10000000000 : ℝ)] ![(31831462243151/100000000000000 : ℝ), (852106725337/2500000000000 : ℝ), (3408426872947/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129706023/312500000 : ℝ)|^4417 ≤ (31831462243151/100000000000000 : ℝ)^3393
        have hw : |(129706023/312500000 : ℝ)|=(129706023/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4374442611/10000000000 : ℝ)|^4417 ≤ (852106725337/2500000000000 : ℝ)^3393
        have hw : |(4374442611/10000000000 : ℝ)|=(4374442611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4374442583/10000000000 : ℝ)|^4417 ≤ (3408426872947/10000000000000 : ℝ)^3393
        have hw : |(4374442583/10000000000 : ℝ)|=(4374442583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_box_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2042556551/10000000000 : ℝ)*x 0 + (5185074151/10000000000 : ℝ)*x 1 + (5399005793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2042556551/10000000000 : ℝ)^4417 ≤ (6323479841507/50000000000000 : ℝ)^3393 := by
    have hnat : (2042556551 : ℕ)^4417*50000000000000^3393 ≤ 6323479841507^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042556551 10000000000 6323479841507 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185074151/10000000000 : ℝ)^4417 ≤ (42527381593939/100000000000000 : ℝ)^3393 := by
    have hnat : (5185074151 : ℕ)^4417*100000000000000^3393 ≤ 42527381593939^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185074151 10000000000 42527381593939 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399005793/10000000000 : ℝ)^4417 ≤ (11206414675663/25000000000000 : ℝ)^3393 := by
    have hnat : (5399005793 : ℕ)^4417*25000000000000^3393 ≤ 11206414675663^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399005793 10000000000 11206414675663 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2042556551/10000000000 : ℝ), (5185074151/10000000000 : ℝ), (5399005793/10000000000 : ℝ)] ![(6323479841507/50000000000000 : ℝ), (42527381593939/100000000000000 : ℝ), (11206414675663/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2042556551/10000000000 : ℝ)|^4417 ≤ (6323479841507/50000000000000 : ℝ)^3393
        have hw : |(-2042556551/10000000000 : ℝ)|=(2042556551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185074151/10000000000 : ℝ)|^4417 ≤ (42527381593939/100000000000000 : ℝ)^3393
        have hw : |(5185074151/10000000000 : ℝ)|=(5185074151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399005793/10000000000 : ℝ)|^4417 ≤ (11206414675663/25000000000000 : ℝ)^3393
        have hw : |(5399005793/10000000000 : ℝ)|=(5399005793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_box_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276479591/10000000000 : ℝ)*x 0 + (-1920030367/10000000000 : ℝ)*x 1 + (2699502921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276479591/10000000000 : ℝ)^4417 ≤ (21752960489489/50000000000000 : ℝ)^3393 := by
    have hnat : (5276479591 : ℕ)^4417*50000000000000^3393 ≤ 21752960489489^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276479591 10000000000 21752960489489 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1920030367/10000000000 : ℝ)^4417 ≤ (11668419769953/100000000000000 : ℝ)^3393 := by
    have hnat : (1920030367 : ℕ)^4417*100000000000000^3393 ≤ 11668419769953^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920030367 10000000000 11668419769953 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699502921/5000000000 : ℝ)^4417 ≤ (22412829616129/50000000000000 : ℝ)^3393 := by
    have hnat : (2699502921 : ℕ)^4417*50000000000000^3393 ≤ 22412829616129^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699502921 5000000000 22412829616129 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276479591/10000000000 : ℝ), (-1920030367/10000000000 : ℝ), (2699502921/5000000000 : ℝ)] ![(21752960489489/50000000000000 : ℝ), (11668419769953/100000000000000 : ℝ), (22412829616129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276479591/10000000000 : ℝ)|^4417 ≤ (21752960489489/50000000000000 : ℝ)^3393
        have hw : |(5276479591/10000000000 : ℝ)|=(5276479591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1920030367/10000000000 : ℝ)|^4417 ≤ (11668419769953/100000000000000 : ℝ)^3393
        have hw : |(-1920030367/10000000000 : ℝ)|=(1920030367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699502921/5000000000 : ℝ)|^4417 ≤ (22412829616129/50000000000000 : ℝ)^3393
        have hw : |(2699502921/5000000000 : ℝ)|=(2699502921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_box_10 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329779971/625000000 : ℝ)*x 0 + (2699503017/5000000000 : ℝ)*x 1 + (-96001509/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329779971/625000000 : ℝ)^4417 ≤ (43505920388627/100000000000000 : ℝ)^3393 := by
    have hnat : (329779971 : ℕ)^4417*100000000000000^3393 ≤ 43505920388627^3393*625000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329779971 625000000 43505920388627 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699503017/5000000000 : ℝ)^4417 ≤ (44825661307447/100000000000000 : ℝ)^3393 := by
    have hnat : (2699503017 : ℕ)^4417*100000000000000^3393 ≤ 44825661307447^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699503017 5000000000 44825661307447 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96001509/500000000 : ℝ)^4417 ≤ (11668418290541/100000000000000 : ℝ)^3393 := by
    have hnat : (96001509 : ℕ)^4417*100000000000000^3393 ≤ 11668418290541^3393*500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96001509 500000000 11668418290541 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329779971/625000000 : ℝ), (2699503017/5000000000 : ℝ), (-96001509/500000000 : ℝ)] ![(43505920388627/100000000000000 : ℝ), (44825661307447/100000000000000 : ℝ), (11668418290541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329779971/625000000 : ℝ)|^4417 ≤ (43505920388627/100000000000000 : ℝ)^3393
        have hw : |(329779971/625000000 : ℝ)|=(329779971/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699503017/5000000000 : ℝ)|^4417 ≤ (44825661307447/100000000000000 : ℝ)^3393
        have hw : |(2699503017/5000000000 : ℝ)|=(2699503017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-96001509/500000000 : ℝ)|^4417 ≤ (11668418290541/100000000000000 : ℝ)^3393
        have hw : |(-96001509/500000000 : ℝ)|=(96001509/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_box_11 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1119292971/2500000000 : ℝ)*x 0 + (842183277/2000000000 : ℝ)*x 1 + (4210915969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1119292971/2500000000 : ℝ)^4417 ≤ (17564972346371/50000000000000 : ℝ)^3393 := by
    have hnat : (1119292971 : ℕ)^4417*50000000000000^3393 ≤ 17564972346371^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119292971 2500000000 17564972346371 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (842183277/2000000000 : ℝ)^4417 ≤ (32435029728763/100000000000000 : ℝ)^3393 := by
    have hnat : (842183277 : ℕ)^4417*100000000000000^3393 ≤ 32435029728763^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842183277 2000000000 32435029728763 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4210915969/10000000000 : ℝ)^4417 ≤ (32435025557433/100000000000000 : ℝ)^3393 := by
    have hnat : (4210915969 : ℕ)^4417*100000000000000^3393 ≤ 32435025557433^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4210915969 10000000000 32435025557433 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1119292971/2500000000 : ℝ), (842183277/2000000000 : ℝ), (4210915969/10000000000 : ℝ)] ![(17564972346371/50000000000000 : ℝ), (32435029728763/100000000000000 : ℝ), (32435025557433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1119292971/2500000000 : ℝ)|^4417 ≤ (17564972346371/50000000000000 : ℝ)^3393
        have hw : |(1119292971/2500000000 : ℝ)|=(1119292971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(842183277/2000000000 : ℝ)|^4417 ≤ (32435029728763/100000000000000 : ℝ)^3393
        have hw : |(842183277/2000000000 : ℝ)|=(842183277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4210915969/10000000000 : ℝ)|^4417 ≤ (32435025557433/100000000000000 : ℝ)^3393
        have hw : |(4210915969/10000000000 : ℝ)|=(4210915969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_box_12 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-928792007/5000000000 : ℝ)*x 0 + (2732458883/5000000000 : ℝ)*x 1 + (5255774021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (928792007/5000000000 : ℝ)^4417 ≤ (2794207890739/25000000000000 : ℝ)^3393 := by
    have hnat : (928792007 : ℕ)^4417*25000000000000^3393 ≤ 2794207890739^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928792007 5000000000 2794207890739 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732458883/5000000000 : ℝ)^4417 ≤ (11384840540541/25000000000000 : ℝ)^3393 := by
    have hnat : (2732458883 : ℕ)^4417*25000000000000^3393 ≤ 11384840540541^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732458883 5000000000 11384840540541 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255774021/10000000000 : ℝ)^4417 ≤ (8656761250187/20000000000000 : ℝ)^3393 := by
    have hnat : (5255774021 : ℕ)^4417*20000000000000^3393 ≤ 8656761250187^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255774021 10000000000 8656761250187 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-928792007/5000000000 : ℝ), (2732458883/5000000000 : ℝ), (5255774021/10000000000 : ℝ)] ![(2794207890739/25000000000000 : ℝ), (11384840540541/25000000000000 : ℝ), (8656761250187/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-928792007/5000000000 : ℝ)|^4417 ≤ (2794207890739/25000000000000 : ℝ)^3393
        have hw : |(-928792007/5000000000 : ℝ)|=(928792007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732458883/5000000000 : ℝ)|^4417 ≤ (11384840540541/25000000000000 : ℝ)^3393
        have hw : |(2732458883/5000000000 : ℝ)|=(2732458883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255774021/10000000000 : ℝ)|^4417 ≤ (8656761250187/20000000000000 : ℝ)^3393
        have hw : |(5255774021/10000000000 : ℝ)|=(5255774021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_box_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344152249/2500000000 : ℝ)*x 0 + (-1978418927/10000000000 : ℝ)*x 1 + (2627887029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344152249/2500000000 : ℝ)^4417 ≤ (5572967452049/12500000000000 : ℝ)^3393 := by
    have hnat : (1344152249 : ℕ)^4417*12500000000000^3393 ≤ 5572967452049^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344152249 2500000000 5572967452049 12500000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1978418927/10000000000 : ℝ)^4417 ≤ (1516556714359/12500000000000 : ℝ)^3393 := by
    have hnat : (1978418927 : ℕ)^4417*12500000000000^3393 ≤ 1516556714359^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978418927 10000000000 1516556714359 12500000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627887029/5000000000 : ℝ)^4417 ≤ (43283806647609/100000000000000 : ℝ)^3393 := by
    have hnat : (2627887029 : ℕ)^4417*100000000000000^3393 ≤ 43283806647609^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627887029 5000000000 43283806647609 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344152249/2500000000 : ℝ), (-1978418927/10000000000 : ℝ), (2627887029/5000000000 : ℝ)] ![(5572967452049/12500000000000 : ℝ), (1516556714359/12500000000000 : ℝ), (43283806647609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344152249/2500000000 : ℝ)|^4417 ≤ (5572967452049/12500000000000 : ℝ)^3393
        have hw : |(1344152249/2500000000 : ℝ)|=(1344152249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1978418927/10000000000 : ℝ)|^4417 ≤ (1516556714359/12500000000000 : ℝ)^3393
        have hw : |(-1978418927/10000000000 : ℝ)|=(1978418927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627887029/5000000000 : ℝ)|^4417 ≤ (43283806647609/100000000000000 : ℝ)^3393
        have hw : |(2627887029/5000000000 : ℝ)|=(2627887029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_box_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688304473/5000000000 : ℝ)*x 0 + (1313943517/2500000000 : ℝ)*x 1 + (-1978418981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688304473/5000000000 : ℝ)^4417 ≤ (8916747815331/20000000000000 : ℝ)^3393 := by
    have hnat : (2688304473 : ℕ)^4417*20000000000000^3393 ≤ 8916747815331^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688304473 5000000000 8916747815331 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313943517/2500000000 : ℝ)^4417 ≤ (21641903377409/50000000000000 : ℝ)^3393 := by
    have hnat : (1313943517 : ℕ)^4417*50000000000000^3393 ≤ 21641903377409^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313943517 2500000000 21641903377409 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1978418981/10000000000 : ℝ)^4417 ≤ (6066227072981/50000000000000 : ℝ)^3393 := by
    have hnat : (1978418981 : ℕ)^4417*50000000000000^3393 ≤ 6066227072981^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978418981 10000000000 6066227072981 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688304473/5000000000 : ℝ), (1313943517/2500000000 : ℝ), (-1978418981/10000000000 : ℝ)] ![(8916747815331/20000000000000 : ℝ), (21641903377409/50000000000000 : ℝ), (6066227072981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688304473/5000000000 : ℝ)|^4417 ≤ (8916747815331/20000000000000 : ℝ)^3393
        have hw : |(2688304473/5000000000 : ℝ)|=(2688304473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313943517/2500000000 : ℝ)|^4417 ≤ (21641903377409/50000000000000 : ℝ)^3393
        have hw : |(1313943517/2500000000 : ℝ)|=(1313943517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1978418981/10000000000 : ℝ)|^4417 ≤ (6066227072981/50000000000000 : ℝ)^3393
        have hw : |(-1978418981/10000000000 : ℝ)|=(1978418981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_box_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2061279039/5000000000 : ℝ)*x 0 + (4388218839/10000000000 : ℝ)*x 1 + (1097054709/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2061279039/5000000000 : ℝ)^4417 ≤ (985995603893/3125000000000 : ℝ)^3393 := by
    have hnat : (2061279039 : ℕ)^4417*3125000000000^3393 ≤ 985995603893^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061279039 5000000000 985995603893 3125000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4388218839/10000000000 : ℝ)^4417 ≤ (273792562759/800000000000 : ℝ)^3393 := by
    have hnat : (4388218839 : ℕ)^4417*800000000000^3393 ≤ 273792562759^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4388218839 10000000000 273792562759 800000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097054709/2500000000 : ℝ)^4417 ≤ (2139004394651/6250000000000 : ℝ)^3393 := by
    have hnat : (1097054709 : ℕ)^4417*6250000000000^3393 ≤ 2139004394651^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097054709 2500000000 2139004394651 6250000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2061279039/5000000000 : ℝ), (4388218839/10000000000 : ℝ), (1097054709/2500000000 : ℝ)] ![(985995603893/3125000000000 : ℝ), (273792562759/800000000000 : ℝ), (2139004394651/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2061279039/5000000000 : ℝ)|^4417 ≤ (985995603893/3125000000000 : ℝ)^3393
        have hw : |(2061279039/5000000000 : ℝ)|=(2061279039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4388218839/10000000000 : ℝ)|^4417 ≤ (273792562759/800000000000 : ℝ)^3393
        have hw : |(4388218839/10000000000 : ℝ)|=(4388218839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1097054709/2500000000 : ℝ)|^4417 ≤ (2139004394651/6250000000000 : ℝ)^3393
        have hw : |(1097054709/2500000000 : ℝ)|=(1097054709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1457_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31459/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5917/10000 : ℝ) ∧ (40301/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84789/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11397/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11397/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11397/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11397/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11397/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11397/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11397/100000 : ℝ) ^ (69/16 : ℝ) ≤ (8558728293632531/100000000000000000000 : ℝ) := by
    have hpowers : (11397/100000 : ℝ)^69 ≤ (8558728293632531/100000000000000000000 : ℝ)^16 := by
      have hnat : (11397 : ℕ)^69*100000000000000000000^16 ≤ 8558728293632531^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11397 100000 8558728293632531 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11397/100000 : ℝ)) (X := (8558728293632531/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hpowhi : (1477/10000 : ℝ) ^ (69/16 : ℝ) ≤ (26179020068418349/100000000000000000000 : ℝ) := by
    have hpowers : (1477/10000 : ℝ)^69 ≤ (26179020068418349/100000000000000000000 : ℝ)^16 := by
      have hnat : (1477 : ℕ)^69*100000000000000000000^16 ≤ 26179020068418349^16*10000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1477 10000 26179020068418349 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1477/10000 : ℝ)) (X := (26179020068418349/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008558728293632531/50000000000000000000 : ℝ) ≤ (10000396900437863/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (50008558728293632531/50000000000000000000 : ℝ)^16 ≤ (10000396900437863/10000000000000000 : ℝ)^69 := by
      have hnat : (50008558728293632531 : ℕ)^16*10000000000000000^69 ≤ 10000396900437863^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008558728293632531 50000000000000000000 10000396900437863 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000396900437863/10000000000000000 : ℝ)) (X := (50008558728293632531/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (312608555463631409/312500000000000000 : ℝ) ≤ (5000402702780757/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (312608555463631409/312500000000000000 : ℝ)^16 ≤ (5000402702780757/5000000000000000 : ℝ)^69 := by
      have hnat : (312608555463631409 : ℕ)^16*5000000000000000^69 ≤ 5000402702780757^69*312500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312608555463631409 312500000000000000 5000402702780757 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000402702780757/5000000000000000 : ℝ)) (X := (312608555463631409/312500000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026179020068418349/50000000000000000000 : ℝ) ≤ (2000242782137033/2000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (50026179020068418349/50000000000000000000 : ℝ)^16 ≤ (2000242782137033/2000000000000000 : ℝ)^69 := by
      have hnat : (50026179020068418349 : ℕ)^16*2000000000000000^69 ≤ 2000242782137033^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026179020068418349 50000000000000000000 2000242782137033 2000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000242782137033/2000000000000000 : ℝ)) (X := (50026179020068418349/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8558728293632531/100000000000000000000 : ℝ) ≤ ((6744405455877682201/6746000000000000000 : ℝ)+2*(408505123651/337300000000000 : ℝ)*(11397/100000 : ℝ))^(69/16 : ℝ) := by
    rw [show (6744405455877682201/6746000000000000000 : ℝ)+2*(408505123651/337300000000000 : ℝ)*(11397/100000 : ℝ)=(10000396900437863/10000000000000000 : ℝ) by norm_num, show 1+2*(8558728293632531/100000000000000000000 : ℝ)=(50008558728293632531/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26179020068418349/100000000000000000000 : ℝ)+(8558728293632531/100000000000000000000 : ℝ) ≤ ((6744405455877682201/6746000000000000000 : ℝ)+(408505123651/337300000000000 : ℝ)*((1477/10000 : ℝ)+(11397/100000 : ℝ)))^(69/16 : ℝ) := by
    rw [show (6744405455877682201/6746000000000000000 : ℝ)+(408505123651/337300000000000 : ℝ)*((1477/10000 : ℝ)+(11397/100000 : ℝ))=(5000402702780757/5000000000000000 : ℝ) by norm_num, show 1+(26179020068418349/100000000000000000000 : ℝ)+(8558728293632531/100000000000000000000 : ℝ)=(312608555463631409/312500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26179020068418349/100000000000000000000 : ℝ) ≤ ((6744405455877682201/6746000000000000000 : ℝ)+2*(408505123651/337300000000000 : ℝ)*(1477/10000 : ℝ))^(69/16 : ℝ) := by
    rw [show (6744405455877682201/6746000000000000000 : ℝ)+2*(408505123651/337300000000000 : ℝ)*(1477/10000 : ℝ)=(2000242782137033/2000000000000000 : ℝ) by norm_num, show 1+2*(26179020068418349/100000000000000000000 : ℝ)=(50026179020068418349/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6744405455877682201/6746000000000000000 : ℝ)*(X 1 0+X 2 0)+(408505123651/337300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (11397/100000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (6744405455877682201/6746000000000000000 : ℝ)) (alpha := (408505123651/337300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6744405455877682201/6746000000000000000 : ℝ)*(X 0 1+X 2 1)+(408505123651/337300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (11397/100000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (6744405455877682201/6746000000000000000 : ℝ)) (alpha := (408505123651/337300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6744405455877682201/6746000000000000000 : ℝ)*(X 0 2+X 1 2)+(408505123651/337300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (11397/100000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (6744405455877682201/6746000000000000000 : ℝ)) (alpha := (408505123651/337300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-894989709/5000000000 : ℝ)*X 0 0+(2692525363/5000000000 : ℝ)*X 0 1+(1077009959/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5286239257/10000000000 : ℝ)*X 1 0+(-376141/1953125 : ℝ)*X 1 1+(1346262401/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1057247843/2000000000 : ℝ)*X 2 0+(5385050499/10000000000 : ℝ)*X 2 1+(-481460189/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2221583539/5000000000 : ℝ)*X 0 0+(4228205273/10000000000 : ℝ)*X 0 1+(4228205783/10000000000 : ℝ)*X 0 2+(2221583539/5000000000 : ℝ)*X 1 0+(4228205273/10000000000 : ℝ)*X 1 1+(4228205783/10000000000 : ℝ)*X 1 2+(2221583539/5000000000 : ℝ)*X 2 0+(4228205273/10000000000 : ℝ)*X 2 1+(4228205783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1055013603/5000000000 : ℝ)*X 0 0+(526691231/1000000000 : ℝ)*X 0 1+(263345599/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((268441203/500000000 : ℝ)*X 1 0+(-24674737/125000000 : ℝ)*X 1 1+(5266912331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2684411931/5000000000 : ℝ)*X 2 0+(329182009/625000000 : ℝ)*X 2 1+(-1973979479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((129706023/312500000 : ℝ)*X 0 0+(4374442611/10000000000 : ℝ)*X 0 1+(4374442583/10000000000 : ℝ)*X 0 2+(129706023/312500000 : ℝ)*X 1 0+(4374442611/10000000000 : ℝ)*X 1 1+(4374442583/10000000000 : ℝ)*X 1 2+(129706023/312500000 : ℝ)*X 2 0+(4374442611/10000000000 : ℝ)*X 2 1+(4374442583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2042556551/10000000000 : ℝ)*X 0 0+(5185074151/10000000000 : ℝ)*X 0 1+(5399005793/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276479591/10000000000 : ℝ)*X 1 0+(-1920030367/10000000000 : ℝ)*X 1 1+(2699502921/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((329779971/625000000 : ℝ)*X 2 0+(2699503017/5000000000 : ℝ)*X 2 1+(-96001509/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1119292971/2500000000 : ℝ)*X 0 0+(842183277/2000000000 : ℝ)*X 0 1+(4210915969/10000000000 : ℝ)*X 0 2+(1119292971/2500000000 : ℝ)*X 1 0+(842183277/2000000000 : ℝ)*X 1 1+(4210915969/10000000000 : ℝ)*X 1 2+(1119292971/2500000000 : ℝ)*X 2 0+(842183277/2000000000 : ℝ)*X 2 1+(4210915969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-928792007/5000000000 : ℝ)*X 0 0+(2732458883/5000000000 : ℝ)*X 0 1+(5255774021/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1344152249/2500000000 : ℝ)*X 1 0+(-1978418927/10000000000 : ℝ)*X 1 1+(2627887029/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2688304473/5000000000 : ℝ)*X 2 0+(1313943517/2500000000 : ℝ)*X 2 1+(-1978418981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2061279039/5000000000 : ℝ)*X 0 0+(4388218839/10000000000 : ℝ)*X 0 1+(1097054709/2500000000 : ℝ)*X 0 2+(2061279039/5000000000 : ℝ)*X 1 0+(4388218839/10000000000 : ℝ)*X 1 1+(1097054709/2500000000 : ℝ)*X 1 2+(2061279039/5000000000 : ℝ)*X 2 0+(4388218839/10000000000 : ℝ)*X 2 1+(1097054709/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31459/50000 : ℝ) ≤ (-2652655215625210980907544820123/4216250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53304409/100000000000000 : ℝ)*(upper1) + (115509939/100000000000000 : ℝ)*(upper2) + (130679097/100000000000000 : ℝ)*(upper3) + (17084137/20000000000000 : ℝ)*(lower4) + (14263637/50000000000000 : ℝ)*(upper5) + (38091445703591/1250000000000 : ℝ)*(major0) + (38091445703591/1250000000000 : ℝ)*(major1) + (38091445703591/1250000000000 : ℝ)*(major2) + (8319647349/100000000000000 : ℝ)*(sp2) + (1050597449583147/25000000000000 : ℝ)*(sp4) + (2101163417988109/50000000000000 : ℝ)*(sp5) + (4202381478685239/100000000000000 : ℝ)*(sp6) + (239151649123733/12500000000000 : ℝ)*(sp7) + (6296235637/10000000000000 : ℝ)*(sp13) + (239151649123733/12500000000000 : ℝ)*(f.failure) + (1050597449583147/25000000000000 : ℝ)*(f.sum) + (2611604737449/421625000000000000000000000 : ℝ)*base66 + (97920160883223791/8432500000000000000000000000000 : ℝ)*base67 + (61533672364563791/8432500000000000000000000000000 : ℝ)*base69 + (30282367354823791/8432500000000000000000000000000 : ℝ)*base71 + (6874496207687/1686500000000000000000000000 : ℝ)*base73 + (151322776065421209/8432500000000000000000000000000 : ℝ)*base76 + (17773222820098709/8432500000000000000000000000000 : ℝ)*base78 + (51813263830596291/8432500000000000000000000000000 : ℝ)*base79 + (16798696737899/674600000000000000000000000 : ℝ)*base82 + (317779/125000000000000000000 : ℝ)*base90 + (317779/125000000000000000000 : ℝ)*base92 + (317779/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (5917/10000 : ℝ) ≤ (49897009926403456180324733800023/84325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32198619/10000000000000 : ℝ)*(lower1) + (94918003/50000000000000 : ℝ)*(lower2) + (127882459/50000000000000 : ℝ)*(upper4) + (1559940895386859/50000000000000 : ℝ)*(major0) + (1559940895386859/50000000000000 : ℝ)*(major1) + (1559940895386859/50000000000000 : ℝ)*(major2) + (106531251203927/2500000000000 : ℝ)*(sp0) + (2130480509495173/50000000000000 : ℝ)*(sp1) + (170449868030299/4000000000000 : ℝ)*(sp2) + (979383699000663/50000000000000 : ℝ)*(sp3) + (4999830913/25000000000000 : ℝ)*(sp6) + (5396133659/100000000000000 : ℝ)*(sp7) + (8325962023/50000000000000 : ℝ)*(sp8) + (305681090781/100000000000000 : ℝ)*(sp9) + (391754558826997/20000000000000 : ℝ)*(f.failure) + (4261266700081127/100000000000000 : ℝ)*(f.sum) + (2116832068521/527031250000000000000000000 : ℝ)*base66 + (2553480914194876659/337300000000000000000000000000000 : ℝ)*base67 + (2300318422616876659/337300000000000000000000000000000 : ℝ)*base69 + (2246871250250723341/337300000000000000000000000000000 : ℝ)*base72 + (17080332269459/8432500000000000000000000000 : ℝ)*base73 + (1616723134868476659/337300000000000000000000000000000 : ℝ)*base75 + (730137653880476659/337300000000000000000000000000000 : ℝ)*base77 + (871708211809776659/337300000000000000000000000000000 : ℝ)*base79 + (48651134146763/16865000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (715789/200000000000000000000 : ℝ)*base89 + (715789/200000000000000000000 : ℝ)*base91 + (715789/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40301/50000 : ℝ) ≤ (27187728170936066656910200459053/33730000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (141105851/100000000000000 : ℝ)*(lower3) + (104065611/100000000000000 : ℝ)*(upper4) + (110213161/50000000000000 : ℝ)*(lower5) + (342616429495283/10000000000000 : ℝ)*(major0) + (342616429495283/10000000000000 : ℝ)*(major1) + (342616429495283/10000000000000 : ℝ)*(major2) + (1635949607/100000000000000 : ℝ)*(sp0) + (5957676631/5000000000000 : ℝ)*(sp1) + (25212370099/10000000000000 : ℝ)*(sp2) + (48514181653/100000000000000 : ℝ)*(sp3) + (4674391107134467/100000000000000 : ℝ)*(sp8) + (2337136794775727/50000000000000 : ℝ)*(sp9) + (934828123876617/20000000000000 : ℝ)*(sp10) + (268877416707111/12500000000000 : ℝ)*(sp11) + (2151067847838541/100000000000000 : ℝ)*(f.failure) + (2337196371542037/50000000000000 : ℝ)*(f.sum) + (19330221146107/3373000000000000000000000000 : ℝ)*base65 + (455576333811137883/67460000000000000000000000000000 : ℝ)*base67 + (849940861211397883/67460000000000000000000000000000 : ℝ)*base69 + (549811057240417883/67460000000000000000000000000000 : ℝ)*base71 + (5448615198603/3373000000000000000000000000 : ℝ)*base73 + (575444174855477883/67460000000000000000000000000000 : ℝ)*base75 + (329221393520657883/67460000000000000000000000000000 : ℝ)*base77 + (199147267061677883/67460000000000000000000000000000 : ℝ)*base79 + (24260652801903/3373000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (488283/1000000000000000000000 : ℝ)*base90 + (488283/1000000000000000000000 : ℝ)*base92 + (488283/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-84789/100000 : ℝ) ≤ (-1787406111083950802416464675903/2108125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22996581/100000000000000 : ℝ)*(lower0) + (2314711/25000000000000 : ℝ)*(lower1) + (1495901/20000000000000 : ℝ)*(upper3) + (8280439/25000000000000 : ℝ)*(lower4) + (43299648666899/1250000000000 : ℝ)*(major0) + (43299648666899/1250000000000 : ℝ)*(major1) + (43299648666899/1250000000000 : ℝ)*(major2) + (2959104269/25000000000000 : ℝ)*(sp6) + (5244898937/100000000000000 : ℝ)*(sp7) + (8315533/12500000000000 : ℝ)*(sp8) + (597675136840819/12500000000000 : ℝ)*(sp12) + (956280232250163/20000000000000 : ℝ)*(sp13) + (4781389324833739/100000000000000 : ℝ)*(sp14) + (13592497240093/625000000000 : ℝ)*(sp15) + (2174804803313817/100000000000000 : ℝ)*(f.failure) + (956280232250163/20000000000000 : ℝ)*(f.sum) + (3096674008143/421625000000000000000000000 : ℝ)*base65 + (18728114522552801/8432500000000000000000000000000 : ℝ)*base68 + (295819468951942801/8432500000000000000000000000000 : ℝ)*base70 + (4155089011045301/8432500000000000000000000000000 : ℝ)*base72 + (4039154748439/1686500000000000000000000000 : ℝ)*base73 + (45723846624062199/8432500000000000000000000000000 : ℝ)*base75 + (10410021243590301/8432500000000000000000000000000 : ℝ)*base78 + (4086161848802801/8432500000000000000000000000000 : ℝ)*base80 + (1120980261067/168650000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (5642129/1000000000000000000000 : ℝ)*base89 + (5642129/1000000000000000000000 : ℝ)*base91 + (5642129/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1457_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31459/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(5917/10000 : ℝ) else (40301/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84789/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1457_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1457_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31459/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(5917/10000 : ℝ) else (40301/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84789/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1457_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31459/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(5917/10000 : ℝ) else (40301/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84789/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1457_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
