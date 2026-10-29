-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1313_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:41:03.261773+00:00
-- url     : https://prove2.me/submissions/bcfa0fd1-9b44-4671-a904-d8cc2b562f82

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
theorem support_rectangle_w1313_s6_0 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-517321077/2500000000 : ℝ)*x 0 + (5414229987/10000000000 : ℝ)*x 1 + (2621825327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517321077/2500000000 : ℝ)^4273 ≤ (157432557457/1250000000000 : ℝ)^3249 := by
    have hnat : (517321077 : ℕ)^4273*1250000000000^3249 ≤ 157432557457^3249*2500000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517321077 2500000000 157432557457 1250000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414229987/10000000000 : ℝ)^4273 ≤ (22311276933537/50000000000000 : ℝ)^3249 := by
    have hnat : (5414229987 : ℕ)^4273*50000000000000^3249 ≤ 22311276933537^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414229987 10000000000 22311276933537 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621825327/5000000000 : ℝ)^4273 ≤ (342262732133/800000000000 : ℝ)^3249 := by
    have hnat : (2621825327 : ℕ)^4273*800000000000^3249 ≤ 342262732133^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621825327 5000000000 342262732133 800000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-517321077/2500000000 : ℝ), (5414229987/10000000000 : ℝ), (2621825327/5000000000 : ℝ)] ![(157432557457/1250000000000 : ℝ), (22311276933537/50000000000000 : ℝ), (342262732133/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-517321077/2500000000 : ℝ)|^4273 ≤ (157432557457/1250000000000 : ℝ)^3249
        have hw : |(-517321077/2500000000 : ℝ)|=(517321077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414229987/10000000000 : ℝ)|^4273 ≤ (22311276933537/50000000000000 : ℝ)^3249
        have hw : |(5414229987/10000000000 : ℝ)|=(5414229987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621825327/5000000000 : ℝ)|^4273 ≤ (342262732133/800000000000 : ℝ)^3249
        have hw : |(2621825327/5000000000 : ℝ)|=(2621825327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s6_1 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674742809/5000000000 : ℝ)*x 0 + (-1078110103/5000000000 : ℝ)*x 1 + (2621825017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674742809/5000000000 : ℝ)^4273 ≤ (43922096871641/100000000000000 : ℝ)^3249 := by
    have hnat : (2674742809 : ℕ)^4273*100000000000000^3249 ≤ 43922096871641^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674742809 5000000000 43922096871641 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078110103/5000000000 : ℝ)^4273 ≤ (13295068249243/100000000000000 : ℝ)^3249 := by
    have hnat : (1078110103 : ℕ)^4273*100000000000000^3249 ≤ 13295068249243^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078110103 5000000000 13295068249243 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621825017/5000000000 : ℝ)^4273 ≤ (42782834863729/100000000000000 : ℝ)^3249 := by
    have hnat : (2621825017 : ℕ)^4273*100000000000000^3249 ≤ 42782834863729^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621825017 5000000000 42782834863729 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674742809/5000000000 : ℝ), (-1078110103/5000000000 : ℝ), (2621825017/5000000000 : ℝ)] ![(43922096871641/100000000000000 : ℝ), (13295068249243/100000000000000 : ℝ), (42782834863729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674742809/5000000000 : ℝ)|^4273 ≤ (43922096871641/100000000000000 : ℝ)^3249
        have hw : |(2674742809/5000000000 : ℝ)|=(2674742809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1078110103/5000000000 : ℝ)|^4273 ≤ (13295068249243/100000000000000 : ℝ)^3249
        have hw : |(-1078110103/5000000000 : ℝ)|=(1078110103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621825017/5000000000 : ℝ)|^4273 ≤ (42782834863729/100000000000000 : ℝ)^3249
        have hw : |(2621825017/5000000000 : ℝ)|=(2621825017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s6_2 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334342801/625000000 : ℝ)*x 0 + (655456311/1250000000 : ℝ)*x 1 + (-8422737/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334342801/625000000 : ℝ)^4273 ≤ (10980522052857/25000000000000 : ℝ)^3249 := by
    have hnat : (334342801 : ℕ)^4273*25000000000000^3249 ≤ 10980522052857^3249*625000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334342801 625000000 10980522052857 25000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655456311/1250000000 : ℝ)^4273 ≤ (21391419867683/50000000000000 : ℝ)^3249 := by
    have hnat : (655456311 : ℕ)^4273*50000000000000^3249 ≤ 21391419867683^3249*1250000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655456311 1250000000 21391419867683 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8422737/39062500 : ℝ)^4273 ≤ (13295072028153/100000000000000 : ℝ)^3249 := by
    have hnat : (8422737 : ℕ)^4273*100000000000000^3249 ≤ 13295072028153^3249*39062500^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8422737 39062500 13295072028153 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334342801/625000000 : ℝ), (655456311/1250000000 : ℝ), (-8422737/39062500 : ℝ)] ![(10980522052857/25000000000000 : ℝ), (21391419867683/50000000000000 : ℝ), (13295072028153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334342801/625000000 : ℝ)|^4273 ≤ (10980522052857/25000000000000 : ℝ)^3249
        have hw : |(334342801/625000000 : ℝ)|=(334342801/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655456311/1250000000 : ℝ)|^4273 ≤ (21391419867683/50000000000000 : ℝ)^3249
        have hw : |(655456311/1250000000 : ℝ)|=(655456311/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8422737/39062500 : ℝ)|^4273 ≤ (13295072028153/100000000000000 : ℝ)^3249
        have hw : |(-8422737/39062500 : ℝ)|=(8422737/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s6_3 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2167128171/5000000000 : ℝ)*x 0 + (2080484159/5000000000 : ℝ)*x 1 + (902873171/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167128171/5000000000 : ℝ)^4273 ≤ (33302708025153/100000000000000 : ℝ)^3249 := by
    have hnat : (2167128171 : ℕ)^4273*100000000000000^3249 ≤ 33302708025153^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167128171 5000000000 33302708025153 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080484159/5000000000 : ℝ)^4273 ≤ (31562720241259/100000000000000 : ℝ)^3249 := by
    have hnat : (2080484159 : ℕ)^4273*100000000000000^3249 ≤ 31562720241259^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080484159 5000000000 31562720241259 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902873171/2000000000 : ℝ)^4273 ≤ (35134571716297/100000000000000 : ℝ)^3249 := by
    have hnat : (902873171 : ℕ)^4273*100000000000000^3249 ≤ 35134571716297^3249*2000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902873171 2000000000 35134571716297 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2167128171/5000000000 : ℝ), (2080484159/5000000000 : ℝ), (902873171/2000000000 : ℝ)] ![(33302708025153/100000000000000 : ℝ), (31562720241259/100000000000000 : ℝ), (35134571716297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2167128171/5000000000 : ℝ)|^4273 ≤ (33302708025153/100000000000000 : ℝ)^3249
        have hw : |(2167128171/5000000000 : ℝ)|=(2167128171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2080484159/5000000000 : ℝ)|^4273 ≤ (31562720241259/100000000000000 : ℝ)^3249
        have hw : |(2080484159/5000000000 : ℝ)|=(2080484159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(902873171/2000000000 : ℝ)|^4273 ≤ (35134571716297/100000000000000 : ℝ)^3249
        have hw : |(902873171/2000000000 : ℝ)|=(902873171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s6_4 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1034648623/5000000000 : ℝ)*x 0 + (5244259849/10000000000 : ℝ)*x 1 + (1353404333/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034648623/5000000000 : ℝ)^4273 ≤ (2518941632413/20000000000000 : ℝ)^3249 := by
    have hnat : (1034648623 : ℕ)^4273*20000000000000^3249 ≤ 2518941632413^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034648623 5000000000 2518941632413 20000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244259849/10000000000 : ℝ)^4273 ≤ (10697344647419/25000000000000 : ℝ)^3249 := by
    have hnat : (5244259849 : ℕ)^4273*25000000000000^3249 ≤ 10697344647419^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244259849 10000000000 10697344647419 25000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353404333/2500000000 : ℝ)^4273 ≤ (11153978309809/25000000000000 : ℝ)^3249 := by
    have hnat : (1353404333 : ℕ)^4273*25000000000000^3249 ≤ 11153978309809^3249*2500000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353404333 2500000000 11153978309809 25000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1034648623/5000000000 : ℝ), (5244259849/10000000000 : ℝ), (1353404333/2500000000 : ℝ)] ![(2518941632413/20000000000000 : ℝ), (10697344647419/25000000000000 : ℝ), (11153978309809/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1034648623/5000000000 : ℝ)|^4273 ≤ (2518941632413/20000000000000 : ℝ)^3249
        have hw : |(-1034648623/5000000000 : ℝ)|=(1034648623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244259849/10000000000 : ℝ)|^4273 ≤ (10697344647419/25000000000000 : ℝ)^3249
        have hw : |(5244259849/10000000000 : ℝ)|=(5244259849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353404333/2500000000 : ℝ)|^4273 ≤ (11153978309809/25000000000000 : ℝ)^3249
        have hw : |(1353404333/2500000000 : ℝ)|=(1353404333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s6_5 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305698353/10000000000 : ℝ)*x 0 + (-248281731/1250000000 : ℝ)*x 1 + (676702131/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305698353/10000000000 : ℝ)^4273 ≤ (43449881160519/100000000000000 : ℝ)^3249 := by
    have hnat : (5305698353 : ℕ)^4273*100000000000000^3249 ≤ 43449881160519^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305698353 10000000000 43449881160519 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (248281731/1250000000 : ℝ)^4273 ≤ (11934208658573/100000000000000 : ℝ)^3249 := by
    have hnat : (248281731 : ℕ)^4273*100000000000000^3249 ≤ 11934208658573^3249*1250000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248281731 1250000000 11934208658573 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676702131/1250000000 : ℝ)^4273 ≤ (44615910160987/100000000000000 : ℝ)^3249 := by
    have hnat : (676702131 : ℕ)^4273*100000000000000^3249 ≤ 44615910160987^3249*1250000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676702131 1250000000 44615910160987 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305698353/10000000000 : ℝ), (-248281731/1250000000 : ℝ), (676702131/1250000000 : ℝ)] ![(43449881160519/100000000000000 : ℝ), (11934208658573/100000000000000 : ℝ), (44615910160987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305698353/10000000000 : ℝ)|^4273 ≤ (43449881160519/100000000000000 : ℝ)^3249
        have hw : |(5305698353/10000000000 : ℝ)|=(5305698353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-248281731/1250000000 : ℝ)|^4273 ≤ (11934208658573/100000000000000 : ℝ)^3249
        have hw : |(-248281731/1250000000 : ℝ)|=(248281731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676702131/1250000000 : ℝ)|^4273 ≤ (44615910160987/100000000000000 : ℝ)^3249
        have hw : |(676702131/1250000000 : ℝ)|=(676702131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s6_6 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305697863/10000000000 : ℝ)*x 0 + (5413617623/10000000000 : ℝ)*x 1 + (-1986253727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305697863/10000000000 : ℝ)^4273 ≤ (8689975176611/20000000000000 : ℝ)^3249 := by
    have hnat : (5305697863 : ℕ)^4273*20000000000000^3249 ≤ 8689975176611^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305697863 10000000000 8689975176611 20000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413617623/10000000000 : ℝ)^4273 ≤ (44615916393357/100000000000000 : ℝ)^3249 := by
    have hnat : (5413617623 : ℕ)^4273*100000000000000^3249 ≤ 44615916393357^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413617623 10000000000 44615916393357 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1986253727/10000000000 : ℝ)^4273 ≤ (596710385121/5000000000000 : ℝ)^3249 := by
    have hnat : (1986253727 : ℕ)^4273*5000000000000^3249 ≤ 596710385121^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986253727 10000000000 596710385121 5000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305697863/10000000000 : ℝ), (5413617623/10000000000 : ℝ), (-1986253727/10000000000 : ℝ)] ![(8689975176611/20000000000000 : ℝ), (44615916393357/100000000000000 : ℝ), (596710385121/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305697863/10000000000 : ℝ)|^4273 ≤ (8689975176611/20000000000000 : ℝ)^3249
        have hw : |(5305697863/10000000000 : ℝ)|=(5305697863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413617623/10000000000 : ℝ)|^4273 ≤ (44615916393357/100000000000000 : ℝ)^3249
        have hw : |(5413617623/10000000000 : ℝ)|=(5413617623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1986253727/10000000000 : ℝ)|^4273 ≤ (596710385121/5000000000000 : ℝ)^3249
        have hw : |(-1986253727/10000000000 : ℝ)|=(1986253727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s6_7 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (270892633/625000000 : ℝ)*x 0 + (4513103143/10000000000 : ℝ)*x 1 + (2081118827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270892633/625000000 : ℝ)^4273 ≤ (33302968600019/100000000000000 : ℝ)^3249 := by
    have hnat : (270892633 : ℕ)^4273*100000000000000^3249 ≤ 33302968600019^3249*625000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270892633 625000000 33302968600019 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4513103143/10000000000 : ℝ)^4273 ≤ (35121647439341/100000000000000 : ℝ)^3249 := by
    have hnat : (4513103143 : ℕ)^4273*100000000000000^3249 ≤ 35121647439341^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513103143 10000000000 35121647439341 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081118827/5000000000 : ℝ)^4273 ≤ (31575383942951/100000000000000 : ℝ)^3249 := by
    have hnat : (2081118827 : ℕ)^4273*100000000000000^3249 ≤ 31575383942951^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081118827 5000000000 31575383942951 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270892633/625000000 : ℝ), (4513103143/10000000000 : ℝ), (2081118827/5000000000 : ℝ)] ![(33302968600019/100000000000000 : ℝ), (35121647439341/100000000000000 : ℝ), (31575383942951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270892633/625000000 : ℝ)|^4273 ≤ (33302968600019/100000000000000 : ℝ)^3249
        have hw : |(270892633/625000000 : ℝ)|=(270892633/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4513103143/10000000000 : ℝ)|^4273 ≤ (35121647439341/100000000000000 : ℝ)^3249
        have hw : |(4513103143/10000000000 : ℝ)|=(4513103143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2081118827/5000000000 : ℝ)|^4273 ≤ (31575383942951/100000000000000 : ℝ)^3249
        have hw : |(2081118827/5000000000 : ℝ)|=(2081118827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1313_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7679353/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11069/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5539/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14689/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14699/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11069/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14699/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11069/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14699/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11069/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14699/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11069/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14699/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11069/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14699/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11069/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11069/100000 : ℝ) ^ (267/64 : ℝ) ≤ (10283469844730199/100000000000000000000 : ℝ) := by
    have hpowers : (11069/100000 : ℝ)^267 ≤ (10283469844730199/100000000000000000000 : ℝ)^64 := by
      have hnat : (11069 : ℕ)^267*100000000000000000000^64 ≤ 10283469844730199^64*100000^267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11069 100000 10283469844730199 100000000000000000000 267 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11069/100000 : ℝ)) (X := (10283469844730199/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14699/100000 : ℝ) ^ (267/64 : ℝ) ≤ (16787991970787269/50000000000000000000 : ℝ) := by
    have hpowers : (14699/100000 : ℝ)^267 ≤ (16787991970787269/50000000000000000000 : ℝ)^64 := by
      have hnat : (14699 : ℕ)^267*50000000000000000000^64 ≤ 16787991970787269^64*100000^267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14699 100000 16787991970787269 50000000000000000000 267 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14699/100000 : ℝ)) (X := (16787991970787269/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010283469844730199/50000000000000000000 : ℝ) ≤ (10000492951774767/10000000000000000 : ℝ) ^ (267/64 : ℝ) := by
    have hpowers : (50010283469844730199/50000000000000000000 : ℝ)^64 ≤ (10000492951774767/10000000000000000 : ℝ)^267 := by
      have hnat : (50010283469844730199 : ℕ)^64*10000000000000000^267 ≤ 10000492951774767^267*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010283469844730199 50000000000000000000 10000492951774767 10000000000000000 64 267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000492951774767/10000000000000000 : ℝ)) (X := (50010283469844730199/50000000000000000000 : ℝ)) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043859453786304737/100000000000000000000 : ℝ) ≤ (10001051137507941/10000000000000000 : ℝ) ^ (267/64 : ℝ) := by
    have hpowers : (100043859453786304737/100000000000000000000 : ℝ)^64 ≤ (10001051137507941/10000000000000000 : ℝ)^267 := by
      have hnat : (100043859453786304737 : ℕ)^64*10000000000000000^267 ≤ 10001051137507941^267*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043859453786304737 100000000000000000000 10001051137507941 10000000000000000 64 267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001051137507941/10000000000000000 : ℝ)) (X := (100043859453786304737/100000000000000000000 : ℝ)) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016787991970787269/25000000000000000000 : ℝ) ≤ (2000321864648223/2000000000000000 : ℝ) ^ (267/64 : ℝ) := by
    have hpowers : (25016787991970787269/25000000000000000000 : ℝ)^64 ≤ (2000321864648223/2000000000000000 : ℝ)^267 := by
      have hnat : (25016787991970787269 : ℕ)^64*2000000000000000^267 ≤ 2000321864648223^267*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016787991970787269 25000000000000000000 2000321864648223 2000000000000000 64 267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000321864648223/2000000000000000 : ℝ)) (X := (25016787991970787269/25000000000000000000 : ℝ)) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10283469844730199/100000000000000000000 : ℝ) ≤ ((6048238716530233033/6050000000000000000 : ℝ)+2*(93030955529/60500000000000 : ℝ)*(11069/100000 : ℝ))^(267/64 : ℝ) := by
    rw [show (6048238716530233033/6050000000000000000 : ℝ)+2*(93030955529/60500000000000 : ℝ)*(11069/100000 : ℝ)=(10000492951774767/10000000000000000 : ℝ) by norm_num, show 1+2*(10283469844730199/100000000000000000000 : ℝ)=(50010283469844730199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16787991970787269/50000000000000000000 : ℝ)+(10283469844730199/100000000000000000000 : ℝ) ≤ ((6048238716530233033/6050000000000000000 : ℝ)+(93030955529/60500000000000 : ℝ)*((14699/100000 : ℝ)+(11069/100000 : ℝ)))^(267/64 : ℝ) := by
    rw [show (6048238716530233033/6050000000000000000 : ℝ)+(93030955529/60500000000000 : ℝ)*((14699/100000 : ℝ)+(11069/100000 : ℝ))=(10001051137507941/10000000000000000 : ℝ) by norm_num, show 1+(16787991970787269/50000000000000000000 : ℝ)+(10283469844730199/100000000000000000000 : ℝ)=(100043859453786304737/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16787991970787269/50000000000000000000 : ℝ) ≤ ((6048238716530233033/6050000000000000000 : ℝ)+2*(93030955529/60500000000000 : ℝ)*(14699/100000 : ℝ))^(267/64 : ℝ) := by
    rw [show (6048238716530233033/6050000000000000000 : ℝ)+2*(93030955529/60500000000000 : ℝ)*(14699/100000 : ℝ)=(2000321864648223/2000000000000000 : ℝ) by norm_num, show 1+2*(16787991970787269/50000000000000000000 : ℝ)=(25016787991970787269/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6048238716530233033/6050000000000000000 : ℝ)*(X 1 0+X 2 0)+(93030955529/60500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (267/64 : ℝ)) (lo := (11069/100000 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (6048238716530233033/6050000000000000000 : ℝ)) (alpha := (93030955529/60500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6048238716530233033/6050000000000000000 : ℝ)*(X 0 1+X 2 1)+(93030955529/60500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (267/64 : ℝ)) (lo := (11069/100000 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (6048238716530233033/6050000000000000000 : ℝ)) (alpha := (93030955529/60500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6048238716530233033/6050000000000000000 : ℝ)*(X 0 2+X 1 2)+(93030955529/60500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (267/64 : ℝ)) (lo := (11069/100000 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (6048238716530233033/6050000000000000000 : ℝ)) (alpha := (93030955529/60500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-517321077/2500000000 : ℝ)*X 0 0+(5414229987/10000000000 : ℝ)*X 0 1+(2621825327/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674742809/5000000000 : ℝ)*X 1 0+(-1078110103/5000000000 : ℝ)*X 1 1+(2621825017/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334342801/625000000 : ℝ)*X 2 0+(655456311/1250000000 : ℝ)*X 2 1+(-8422737/39062500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2167128171/5000000000 : ℝ)*X 0 0+(2080484159/5000000000 : ℝ)*X 0 1+(902873171/2000000000 : ℝ)*X 0 2+(2167128171/5000000000 : ℝ)*X 1 0+(2080484159/5000000000 : ℝ)*X 1 1+(902873171/2000000000 : ℝ)*X 1 2+(2167128171/5000000000 : ℝ)*X 2 0+(2080484159/5000000000 : ℝ)*X 2 1+(902873171/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1034648623/5000000000 : ℝ)*X 0 0+(5244259849/10000000000 : ℝ)*X 0 1+(1353404333/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305698353/10000000000 : ℝ)*X 1 0+(-248281731/1250000000 : ℝ)*X 1 1+(676702131/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305697863/10000000000 : ℝ)*X 2 0+(5413617623/10000000000 : ℝ)*X 2 1+(-1986253727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((270892633/625000000 : ℝ)*X 0 0+(4513103143/10000000000 : ℝ)*X 0 1+(2081118827/5000000000 : ℝ)*X 0 2+(270892633/625000000 : ℝ)*X 1 0+(4513103143/10000000000 : ℝ)*X 1 1+(2081118827/5000000000 : ℝ)*X 1 2+(270892633/625000000 : ℝ)*X 2 0+(4513103143/10000000000 : ℝ)*X 2 1+(2081118827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (143317452680449682033294211/13750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2145392971/100000000000000 : ℝ)*(base19) + (407910491/25000000000000 : ℝ)*(base23) + (5688671/5000000000000 : ℝ)*(upper3) + (58201949/25000000000000 : ℝ)*(lower4) + (2173044804935807/50000000000000 : ℝ)*(major0) + (2173044804935807/50000000000000 : ℝ)*(major1) + (2173044804935807/50000000000000 : ℝ)*(major2) + (1465605775447231/25000000000000 : ℝ)*(sp0) + (732806614290929/12500000000000 : ℝ)*(sp1) + (2931222435436677/50000000000000 : ℝ)*(sp2) + (88428151270961/3125000000000 : ℝ)*(sp3) + (31957931479/100000000000000 : ℝ)*(sp4) + (4278602543/50000000000000 : ℝ)*(sp6) + (5742978953/25000000000000 : ℝ)*(sp7) + (707430953146641/25000000000000 : ℝ)*(f.failure) + (5862455059720403/100000000000000 : ℝ)*(f.sum) + (38410319719/17187500000000000000000000 : ℝ)*base66 + (174806514584428421/27500000000000000000000000000000 : ℝ)*base67 + (466358065506928421/27500000000000000000000000000000 : ℝ)*base69 + (530683816996928421/27500000000000000000000000000000 : ℝ)*base71 + (66437551923/137500000000000000000000000 : ℝ)*base73 + (510122050496928421/27500000000000000000000000000000 : ℝ)*base75 + (467487411581928421/27500000000000000000000000000000 : ℝ)*base77 + (207669656131928421/27500000000000000000000000000000 : ℝ)*base79 + (85119551763/34375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (496727/125000000000000000000 : ℝ)*base90 + (496727/125000000000000000000 : ℝ)*base92 + (496727/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (517971727038997515959796723/60500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (262927729/20000000000000 : ℝ)*(base19) + (486473269/50000000000000 : ℝ)*(base23) + (69084993/100000000000000 : ℝ)*(upper2) + (10150653/5000000000000 : ℝ)*(upper3) + (2203913/4000000000000 : ℝ)*(upper5) + (875475447223977/20000000000000 : ℝ)*(major0) + (875475447223977/20000000000000 : ℝ)*(major1) + (875475447223977/20000000000000 : ℝ)*(major2) + (13663724717/100000000000000 : ℝ)*(sp1) + (5639890281/25000000000000 : ℝ)*(sp2) + (236186364390307/4000000000000 : ℝ)*(sp4) + (5904644131394313/100000000000000 : ℝ)*(sp5) + (2952317788625007/50000000000000 : ℝ)*(sp6) + (2850095077098217/100000000000000 : ℝ)*(sp7) + (2850095077098217/100000000000000 : ℝ)*(f.failure) + (236186364390307/4000000000000 : ℝ)*(f.sum) + (2200253369603/605000000000000000000000000 : ℝ)*base65 + (13383155187667759/121000000000000000000000000000000 : ℝ)*base68 + (873257423539667759/121000000000000000000000000000000 : ℝ)*base70 + (404760747747332241/121000000000000000000000000000000 : ℝ)*base71 + (670322946577/151250000000000000000000000 : ℝ)*base73 + (91026024918332241/121000000000000000000000000000000 : ℝ)*base75 + (221792579443667759/121000000000000000000000000000000 : ℝ)*base78 + (2611704988426667759/121000000000000000000000000000000 : ℝ)*base80 + (457791244573/605000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (986399/500000000000000000000 : ℝ)*base90 + (986399/500000000000000000000 : ℝ)*base92 + (986399/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1313_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7679353/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11069/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5539/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1313_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1313_s7_0 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1034647789/5000000000 : ℝ)*x 0 + (1082829287/2000000000 : ℝ)*x 1 + (2621863323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034647789/5000000000 : ℝ)^4273 ≤ (3148673702531/25000000000000 : ℝ)^3249 := by
    have hnat : (1034647789 : ℕ)^4273*25000000000000^3249 ≤ 3148673702531^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034647789 5000000000 3148673702531 25000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082829287/2000000000 : ℝ)^4273 ≤ (5577706028097/12500000000000 : ℝ)^3249 := by
    have hnat : (1082829287 : ℕ)^4273*12500000000000^3249 ≤ 5577706028097^3249*2000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082829287 2000000000 5577706028097 12500000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621863323/5000000000 : ℝ)^4273 ≤ (855673138979/2000000000000 : ℝ)^3249 := by
    have hnat : (2621863323 : ℕ)^4273*2000000000000^3249 ≤ 855673138979^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621863323 5000000000 855673138979 2000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1034647789/5000000000 : ℝ), (1082829287/2000000000 : ℝ), (2621863323/5000000000 : ℝ)] ![(3148673702531/25000000000000 : ℝ), (5577706028097/12500000000000 : ℝ), (855673138979/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1034647789/5000000000 : ℝ)|^4273 ≤ (3148673702531/25000000000000 : ℝ)^3249
        have hw : |(-1034647789/5000000000 : ℝ)|=(1034647789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082829287/2000000000 : ℝ)|^4273 ≤ (5577706028097/12500000000000 : ℝ)^3249
        have hw : |(1082829287/2000000000 : ℝ)|=(1082829287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621863323/5000000000 : ℝ)|^4273 ≤ (855673138979/2000000000000 : ℝ)^3249
        have hw : |(2621863323/5000000000 : ℝ)|=(2621863323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s7_1 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349463037/10000000000 : ℝ)*x 0 + (-1078074331/5000000000 : ℝ)*x 1 + (209749073/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349463037/10000000000 : ℝ)^4273 ≤ (21960926518023/50000000000000 : ℝ)^3249 := by
    have hnat : (5349463037 : ℕ)^4273*50000000000000^3249 ≤ 21960926518023^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349463037 10000000000 21960926518023 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078074331/5000000000 : ℝ)^4273 ≤ (13294488084159/100000000000000 : ℝ)^3249 := by
    have hnat : (1078074331 : ℕ)^4273*100000000000000^3249 ≤ 13294488084159^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078074331 5000000000 13294488084159 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209749073/400000000 : ℝ)^4273 ≤ (21391829434857/50000000000000 : ℝ)^3249 := by
    have hnat : (209749073 : ℕ)^4273*50000000000000^3249 ≤ 21391829434857^3249*400000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209749073 400000000 21391829434857 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349463037/10000000000 : ℝ), (-1078074331/5000000000 : ℝ), (209749073/400000000 : ℝ)] ![(21960926518023/50000000000000 : ℝ), (13294488084159/100000000000000 : ℝ), (21391829434857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349463037/10000000000 : ℝ)|^4273 ≤ (21960926518023/50000000000000 : ℝ)^3249
        have hw : |(5349463037/10000000000 : ℝ)|=(5349463037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1078074331/5000000000 : ℝ)|^4273 ≤ (13294488084159/100000000000000 : ℝ)^3249
        have hw : |(-1078074331/5000000000 : ℝ)|=(1078074331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209749073/400000000 : ℝ)|^4273 ≤ (21391829434857/50000000000000 : ℝ)^3249
        have hw : |(209749073/400000000 : ℝ)|=(209749073/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s7_2 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674731667/5000000000 : ℝ)*x 0 + (524372669/1000000000 : ℝ)*x 1 + (-539037111/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674731667/5000000000 : ℝ)^4273 ≤ (5490232030391/12500000000000 : ℝ)^3249 := by
    have hnat : (2674731667 : ℕ)^4273*12500000000000^3249 ≤ 5490232030391^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674731667 5000000000 5490232030391 12500000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524372669/1000000000 : ℝ)^4273 ≤ (42783657421093/100000000000000 : ℝ)^3249 := by
    have hnat : (524372669 : ℕ)^4273*100000000000000^3249 ≤ 42783657421093^3249*1000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524372669 1000000000 42783657421093 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539037111/2500000000 : ℝ)^4273 ≤ (13294486316361/100000000000000 : ℝ)^3249 := by
    have hnat : (539037111 : ℕ)^4273*100000000000000^3249 ≤ 13294486316361^3249*2500000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539037111 2500000000 13294486316361 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674731667/5000000000 : ℝ), (524372669/1000000000 : ℝ), (-539037111/2500000000 : ℝ)] ![(5490232030391/12500000000000 : ℝ), (42783657421093/100000000000000 : ℝ), (13294486316361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674731667/5000000000 : ℝ)|^4273 ≤ (5490232030391/12500000000000 : ℝ)^3249
        have hw : |(2674731667/5000000000 : ℝ)|=(2674731667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524372669/1000000000 : ℝ)|^4273 ≤ (42783657421093/100000000000000 : ℝ)^3249
        have hw : |(524372669/1000000000 : ℝ)|=(524372669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-539037111/2500000000 : ℝ)|^4273 ≤ (13294486316361/100000000000000 : ℝ)^3249
        have hw : |(-539037111/2500000000 : ℝ)|=(539037111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s7_3 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083565577/2500000000 : ℝ)*x 0 + (2080566881/5000000000 : ℝ)*x 1 + (1128549679/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083565577/2500000000 : ℝ)^4273 ≤ (33302768313237/100000000000000 : ℝ)^3249 := by
    have hnat : (1083565577 : ℕ)^4273*100000000000000^3249 ≤ 33302768313237^3249*2500000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083565577 2500000000 33302768313237 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080566881/5000000000 : ℝ)^4273 ≤ (31564370746627/100000000000000 : ℝ)^3249 := by
    have hnat : (2080566881 : ℕ)^4273*100000000000000^3249 ≤ 31564370746627^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080566881 5000000000 31564370746627 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1128549679/2500000000 : ℝ)^4273 ≤ (17566430463827/50000000000000 : ℝ)^3249 := by
    have hnat : (1128549679 : ℕ)^4273*50000000000000^3249 ≤ 17566430463827^3249*2500000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128549679 2500000000 17566430463827 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083565577/2500000000 : ℝ), (2080566881/5000000000 : ℝ), (1128549679/2500000000 : ℝ)] ![(33302768313237/100000000000000 : ℝ), (31564370746627/100000000000000 : ℝ), (17566430463827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083565577/2500000000 : ℝ)|^4273 ≤ (33302768313237/100000000000000 : ℝ)^3249
        have hw : |(1083565577/2500000000 : ℝ)|=(1083565577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2080566881/5000000000 : ℝ)|^4273 ≤ (31564370746627/100000000000000 : ℝ)^3249
        have hw : |(2080566881/5000000000 : ℝ)|=(2080566881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1128549679/2500000000 : ℝ)|^4273 ≤ (17566430463827/50000000000000 : ℝ)^3249
        have hw : |(1128549679/2500000000 : ℝ)|=(1128549679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s7_4 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-258663499/1250000000 : ℝ)*x 0 + (5244335089/10000000000 : ℝ)*x 1 + (1082706981/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258663499/1250000000 : ℝ)^4273 ≤ (2518958836261/20000000000000 : ℝ)^3249 := by
    have hnat : (258663499 : ℕ)^4273*20000000000000^3249 ≤ 2518958836261^3249*1250000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258663499 1250000000 2518958836261 20000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244335089/10000000000 : ℝ)^4273 ≤ (21395092991103/50000000000000 : ℝ)^3249 := by
    have hnat : (5244335089 : ℕ)^4273*50000000000000^3249 ≤ 21395092991103^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244335089 10000000000 21395092991103 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082706981/2000000000 : ℝ)^4273 ≤ (11153754955737/25000000000000 : ℝ)^3249 := by
    have hnat : (1082706981 : ℕ)^4273*25000000000000^3249 ≤ 11153754955737^3249*2000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082706981 2000000000 11153754955737 25000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-258663499/1250000000 : ℝ), (5244335089/10000000000 : ℝ), (1082706981/2000000000 : ℝ)] ![(2518958836261/20000000000000 : ℝ), (21395092991103/50000000000000 : ℝ), (11153754955737/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-258663499/1250000000 : ℝ)|^4273 ≤ (2518958836261/20000000000000 : ℝ)^3249
        have hw : |(-258663499/1250000000 : ℝ)|=(258663499/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244335089/10000000000 : ℝ)|^4273 ≤ (21395092991103/50000000000000 : ℝ)^3249
        have hw : |(5244335089/10000000000 : ℝ)|=(5244335089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082706981/2000000000 : ℝ)|^4273 ≤ (11153754955737/25000000000000 : ℝ)^3249
        have hw : |(1082706981/2000000000 : ℝ)|=(1082706981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s7_5 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652858817/5000000000 : ℝ)*x 0 + (-397268047/2000000000 : ℝ)*x 1 + (5413534909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652858817/5000000000 : ℝ)^4273 ≤ (43450088823471/100000000000000 : ℝ)^3249 := by
    have hnat : (2652858817 : ℕ)^4273*100000000000000^3249 ≤ 43450088823471^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652858817 5000000000 43450088823471 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397268047/2000000000 : ℝ)^4273 ≤ (5967445650617/50000000000000 : ℝ)^3249 := by
    have hnat : (397268047 : ℕ)^4273*50000000000000^3249 ≤ 5967445650617^3249*2000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397268047 2000000000 5967445650617 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413534909/10000000000 : ℝ)^4273 ≤ (44615019866303/100000000000000 : ℝ)^3249 := by
    have hnat : (5413534909 : ℕ)^4273*100000000000000^3249 ≤ 44615019866303^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413534909 10000000000 44615019866303 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652858817/5000000000 : ℝ), (-397268047/2000000000 : ℝ), (5413534909/10000000000 : ℝ)] ![(43450088823471/100000000000000 : ℝ), (5967445650617/50000000000000 : ℝ), (44615019866303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652858817/5000000000 : ℝ)|^4273 ≤ (43450088823471/100000000000000 : ℝ)^3249
        have hw : |(2652858817/5000000000 : ℝ)|=(2652858817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-397268047/2000000000 : ℝ)|^4273 ≤ (5967445650617/50000000000000 : ℝ)^3249
        have hw : |(-397268047/2000000000 : ℝ)|=(397268047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413534909/10000000000 : ℝ)|^4273 ≤ (44615019866303/100000000000000 : ℝ)^3249
        have hw : |(5413534909/10000000000 : ℝ)|=(5413534909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s7_6 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305717639/10000000000 : ℝ)*x 0 + (2706767451/5000000000 : ℝ)*x 1 + (-1986340237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305717639/10000000000 : ℝ)^4273 ≤ (43450088877323/100000000000000 : ℝ)^3249 := by
    have hnat : (5305717639 : ℕ)^4273*100000000000000^3249 ≤ 43450088877323^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305717639 10000000000 43450088877323 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706767451/5000000000 : ℝ)^4273 ≤ (44615019790431/100000000000000 : ℝ)^3249 := by
    have hnat : (2706767451 : ℕ)^4273*100000000000000^3249 ≤ 44615019790431^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706767451 5000000000 44615019790431 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1986340237/10000000000 : ℝ)^4273 ≤ (5967445658519/50000000000000 : ℝ)^3249 := by
    have hnat : (1986340237 : ℕ)^4273*50000000000000^3249 ≤ 5967445658519^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986340237 10000000000 5967445658519 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305717639/10000000000 : ℝ), (2706767451/5000000000 : ℝ), (-1986340237/10000000000 : ℝ)] ![(43450088877323/100000000000000 : ℝ), (44615019790431/100000000000000 : ℝ), (5967445658519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305717639/10000000000 : ℝ)|^4273 ≤ (43450088877323/100000000000000 : ℝ)^3249
        have hw : |(5305717639/10000000000 : ℝ)|=(5305717639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706767451/5000000000 : ℝ)|^4273 ≤ (44615019790431/100000000000000 : ℝ)^3249
        have hw : |(2706767451/5000000000 : ℝ)|=(2706767451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1986340237/10000000000 : ℝ)|^4273 ≤ (5967445658519/50000000000000 : ℝ)^3249
        have hw : |(-1986340237/10000000000 : ℝ)|=(1986340237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_s7_7 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (108357203/250000000 : ℝ)*x 0 + (4512938591/10000000000 : ℝ)*x 1 + (2081200193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108357203/250000000 : ℝ)^4273 ≤ (16651514575477/50000000000000 : ℝ)^3249 := by
    have hnat : (108357203 : ℕ)^4273*50000000000000^3249 ≤ 16651514575477^3249*250000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108357203 250000000 16651514575477 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4512938591/10000000000 : ℝ)^4273 ≤ (7023992655773/20000000000000 : ℝ)^3249 := by
    have hnat : (4512938591 : ℕ)^4273*20000000000000^3249 ≤ 7023992655773^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512938591 10000000000 7023992655773 20000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081200193/5000000000 : ℝ)^4273 ≤ (394712594359/1250000000000 : ℝ)^3249 := by
    have hnat : (2081200193 : ℕ)^4273*1250000000000^3249 ≤ 394712594359^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081200193 5000000000 394712594359 1250000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108357203/250000000 : ℝ), (4512938591/10000000000 : ℝ), (2081200193/5000000000 : ℝ)] ![(16651514575477/50000000000000 : ℝ), (7023992655773/20000000000000 : ℝ), (394712594359/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108357203/250000000 : ℝ)|^4273 ≤ (16651514575477/50000000000000 : ℝ)^3249
        have hw : |(108357203/250000000 : ℝ)|=(108357203/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4512938591/10000000000 : ℝ)|^4273 ≤ (7023992655773/20000000000000 : ℝ)^3249
        have hw : |(4512938591/10000000000 : ℝ)|=(4512938591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2081200193/5000000000 : ℝ)|^4273 ≤ (394712594359/1250000000000 : ℝ)^3249
        have hw : |(2081200193/5000000000 : ℝ)|=(2081200193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1313_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7679353/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5539/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (277/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14687/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14689/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5539/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14689/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5539/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14689/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5539/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14689/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5539/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14689/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5539/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14689/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5539/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5539/50000 : ℝ) ^ (267/64 : ℝ) ≤ (2063679429968239/20000000000000000000 : ℝ) := by
    have hpowers : (5539/50000 : ℝ)^267 ≤ (2063679429968239/20000000000000000000 : ℝ)^64 := by
      have hnat : (5539 : ℕ)^267*20000000000000000000^64 ≤ 2063679429968239^64*50000^267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5539 50000 2063679429968239 20000000000000000000 267 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5539/50000 : ℝ)) (X := (2063679429968239/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14689/100000 : ℝ) ^ (267/64 : ℝ) ≤ (33480791241546127/100000000000000000000 : ℝ) := by
    have hpowers : (14689/100000 : ℝ)^267 ≤ (33480791241546127/100000000000000000000 : ℝ)^64 := by
      have hnat : (14689 : ℕ)^267*100000000000000000000^64 ≤ 33480791241546127^64*100000^267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14689 100000 33480791241546127 100000000000000000000 267 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14689/100000 : ℝ)) (X := (33480791241546127/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002063679429968239/10000000000000000000 : ℝ) ≤ (2500123656482541/2500000000000000 : ℝ) ^ (267/64 : ℝ) := by
    have hpowers : (10002063679429968239/10000000000000000000 : ℝ)^64 ≤ (2500123656482541/2500000000000000 : ℝ)^267 := by
      have hnat : (10002063679429968239 : ℕ)^64*2500000000000000^267 ≤ 2500123656482541^267*10000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002063679429968239 10000000000000000000 2500123656482541 2500000000000000 64 267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500123656482541/2500000000000000 : ℝ)) (X := (10002063679429968239/10000000000000000000 : ℝ)) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021899594195693661/50000000000000000000 : ℝ) ≤ (125013121167817/125000000000000 : ℝ) ^ (267/64 : ℝ) := by
    have hpowers : (50021899594195693661/50000000000000000000 : ℝ)^64 ≤ (125013121167817/125000000000000 : ℝ)^267 := by
      have hnat : (50021899594195693661 : ℕ)^64*125000000000000^267 ≤ 125013121167817^267*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021899594195693661 50000000000000000000 125013121167817 125000000000000 64 267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125013121167817/125000000000000 : ℝ)) (X := (50021899594195693661/50000000000000000000 : ℝ)) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033480791241546127/50000000000000000000 : ℝ) ≤ (2500401190230139/2500000000000000 : ℝ) ^ (267/64 : ℝ) := by
    have hpowers : (50033480791241546127/50000000000000000000 : ℝ)^64 ≤ (2500401190230139/2500000000000000 : ℝ)^267 := by
      have hnat : (50033480791241546127 : ℕ)^64*2500000000000000^267 ≤ 2500401190230139^267*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033480791241546127 50000000000000000000 2500401190230139 2500000000000000 64 267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500401190230139/2500000000000000 : ℝ)) (X := (50033480791241546127/50000000000000000000 : ℝ)) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2063679429968239/20000000000000000000 : ℝ) ≤ ((9024872004702564907/9027500000000000000 : ℝ)+2*(138766873799/90275000000000 : ℝ)*(5539/50000 : ℝ))^(267/64 : ℝ) := by
    rw [show (9024872004702564907/9027500000000000000 : ℝ)+2*(138766873799/90275000000000 : ℝ)*(5539/50000 : ℝ)=(2500123656482541/2500000000000000 : ℝ) by norm_num, show 1+2*(2063679429968239/20000000000000000000 : ℝ)=(10002063679429968239/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33480791241546127/100000000000000000000 : ℝ)+(2063679429968239/20000000000000000000 : ℝ) ≤ ((9024872004702564907/9027500000000000000 : ℝ)+(138766873799/90275000000000 : ℝ)*((14689/100000 : ℝ)+(5539/50000 : ℝ)))^(267/64 : ℝ) := by
    rw [show (9024872004702564907/9027500000000000000 : ℝ)+(138766873799/90275000000000 : ℝ)*((14689/100000 : ℝ)+(5539/50000 : ℝ))=(125013121167817/125000000000000 : ℝ) by norm_num, show 1+(33480791241546127/100000000000000000000 : ℝ)+(2063679429968239/20000000000000000000 : ℝ)=(50021899594195693661/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33480791241546127/100000000000000000000 : ℝ) ≤ ((9024872004702564907/9027500000000000000 : ℝ)+2*(138766873799/90275000000000 : ℝ)*(14689/100000 : ℝ))^(267/64 : ℝ) := by
    rw [show (9024872004702564907/9027500000000000000 : ℝ)+2*(138766873799/90275000000000 : ℝ)*(14689/100000 : ℝ)=(2500401190230139/2500000000000000 : ℝ) by norm_num, show 1+2*(33480791241546127/100000000000000000000 : ℝ)=(50033480791241546127/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9024872004702564907/9027500000000000000 : ℝ)*(X 1 0+X 2 0)+(138766873799/90275000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (267/64 : ℝ)) (lo := (5539/50000 : ℝ)) (hi := (14689/100000 : ℝ)) (c := (9024872004702564907/9027500000000000000 : ℝ)) (alpha := (138766873799/90275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9024872004702564907/9027500000000000000 : ℝ)*(X 0 1+X 2 1)+(138766873799/90275000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (267/64 : ℝ)) (lo := (5539/50000 : ℝ)) (hi := (14689/100000 : ℝ)) (c := (9024872004702564907/9027500000000000000 : ℝ)) (alpha := (138766873799/90275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9024872004702564907/9027500000000000000 : ℝ)*(X 0 2+X 1 2)+(138766873799/90275000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (267/64 : ℝ)) (lo := (5539/50000 : ℝ)) (hi := (14689/100000 : ℝ)) (c := (9024872004702564907/9027500000000000000 : ℝ)) (alpha := (138766873799/90275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1034647789/5000000000 : ℝ)*X 0 0+(1082829287/2000000000 : ℝ)*X 0 1+(2621863323/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349463037/10000000000 : ℝ)*X 1 0+(-1078074331/5000000000 : ℝ)*X 1 1+(209749073/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674731667/5000000000 : ℝ)*X 2 0+(524372669/1000000000 : ℝ)*X 2 1+(-539037111/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1083565577/2500000000 : ℝ)*X 0 0+(2080566881/5000000000 : ℝ)*X 0 1+(1128549679/2500000000 : ℝ)*X 0 2+(1083565577/2500000000 : ℝ)*X 1 0+(2080566881/5000000000 : ℝ)*X 1 1+(1128549679/2500000000 : ℝ)*X 1 2+(1083565577/2500000000 : ℝ)*X 2 0+(2080566881/5000000000 : ℝ)*X 2 1+(1128549679/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-258663499/1250000000 : ℝ)*X 0 0+(5244335089/10000000000 : ℝ)*X 0 1+(1082706981/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652858817/5000000000 : ℝ)*X 1 0+(-397268047/2000000000 : ℝ)*X 1 1+(5413534909/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305717639/10000000000 : ℝ)*X 2 0+(2706767451/5000000000 : ℝ)*X 2 1+(-1986340237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((108357203/250000000 : ℝ)*X 0 0+(4512938591/10000000000 : ℝ)*X 0 1+(2081200193/5000000000 : ℝ)*X 0 2+(108357203/250000000 : ℝ)*X 1 0+(4512938591/10000000000 : ℝ)*X 1 1+(2081200193/5000000000 : ℝ)*X 1 2+(108357203/250000000 : ℝ)*X 2 0+(4512938591/10000000000 : ℝ)*X 2 1+(2081200193/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1713072715714348683048027831/225687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (186798799/20000000000000 : ℝ)*(base19) + (1209338317/100000000000000 : ℝ)*(base23) + (26982471/100000000000000 : ℝ)*(lower2) + (31760963/100000000000000 : ℝ)*(upper3) + (15772759/5000000000000 : ℝ)*(upper5) + (2175066862052089/50000000000000 : ℝ)*(major0) + (2175066862052089/50000000000000 : ℝ)*(major1) + (2175066862052089/50000000000000 : ℝ)*(major2) + (5867879797908249/100000000000000 : ℝ)*(sp0) + (733488667489561/12500000000000 : ℝ)*(sp1) + (2933954532286083/50000000000000 : ℝ)*(sp2) + (2832349812062693/100000000000000 : ℝ)*(sp3) + (6095200447/20000000000000 : ℝ)*(sp4) + (7109219723/100000000000000 : ℝ)*(sp7) + (177022307580151/6250000000000 : ℝ)*(f.failure) + (5867910273910483/100000000000000 : ℝ)*(f.sum) + (24340864925511/9027500000000000000000000000 : ℝ)*base66 + (1954939978613665723/451375000000000000000000000000000 : ℝ)*base67 + (1903170332755415723/451375000000000000000000000000000 : ℝ)*base69 + (4884416687991040723/451375000000000000000000000000000 : ℝ)*base71 + (17344589701777/18055000000000000000000000000 : ℝ)*base74 + (1261137714917209277/451375000000000000000000000000000 : ℝ)*base76 + (735780590732540723/451375000000000000000000000000000 : ℝ)*base77 + (2582256384312584277/451375000000000000000000000000000 : ℝ)*base80 + (10879277196511/9027500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (302697/31250000000000000000 : ℝ)*base90 + (302697/31250000000000000000 : ℝ)*base92 + (302697/31250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46859045779494604069041/9027500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2203939/250000000000 : ℝ)*(base19) + (966494151/100000000000000 : ℝ)*(base23) + (304483877/100000000000000 : ℝ)*(lower1) + (102211747/100000000000000 : ℝ)*(upper3) + (36912923/100000000000000 : ℝ)*(lower4) + (4376127/4000000000000 : ℝ)*(upper5) + (1095362590163573/25000000000000 : ℝ)*(major0) + (1095362590163573/25000000000000 : ℝ)*(major1) + (1095362590163573/25000000000000 : ℝ)*(major2) + (1185805149/100000000000000 : ℝ)*(sp2) + (5910153473984641/100000000000000 : ℝ)*(sp4) + (5910152592409041/100000000000000 : ℝ)*(sp5) + (5910151321685341/100000000000000 : ℝ)*(sp6) + (285274707430059/10000000000000 : ℝ)*(sp7) + (285274707430059/10000000000000 : ℝ)*(f.failure) + (5910153473984641/100000000000000 : ℝ)*(f.sum) + (8747004860149/2256875000000000000000000000 : ℝ)*base65 + (244693976120829789/225687500000000000000000000000000 : ℝ)*base68 + (42745439731204789/225687500000000000000000000000000 : ℝ)*base70 + (3447286523153857711/225687500000000000000000000000000 : ℝ)*base71 + (62942458568207/18055000000000000000000000000 : ℝ)*base73 + (19987498682868954789/225687500000000000000000000000000 : ℝ)*base76 + (1321173129405045211/225687500000000000000000000000000 : ℝ)*base77 + (1905514263343357711/225687500000000000000000000000000 : ℝ)*base79 + (10905787168047/18055000000000000000000000000 : ℝ)*base81 + (128173/50000000000000000000 : ℝ)*base90 + (128173/50000000000000000000 : ℝ)*base92 + (128173/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1313_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7679353/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5539/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (277/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1313_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1313_box_0 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-37993863/200000000 : ℝ)*x 0 + (5391147839/10000000000 : ℝ)*x 1 + (673893489/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37993863/200000000 : ℝ)^4273 ≤ (11254943233597/100000000000000 : ℝ)^3249 := by
    have hnat : (37993863 : ℕ)^4273*100000000000000^3249 ≤ 11254943233597^3249*200000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37993863 200000000 11254943233597 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391147839/10000000000 : ℝ)^4273 ≤ (22186263991847/50000000000000 : ℝ)^3249 := by
    have hnat : (5391147839 : ℕ)^4273*50000000000000^3249 ≤ 22186263991847^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391147839 10000000000 22186263991847 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673893489/1250000000 : ℝ)^4273 ≤ (44372528773897/100000000000000 : ℝ)^3249 := by
    have hnat : (673893489 : ℕ)^4273*100000000000000^3249 ≤ 44372528773897^3249*1250000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673893489 1250000000 44372528773897 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37993863/200000000 : ℝ), (5391147839/10000000000 : ℝ), (673893489/1250000000 : ℝ)] ![(11254943233597/100000000000000 : ℝ), (22186263991847/50000000000000 : ℝ), (44372528773897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37993863/200000000 : ℝ)|^4273 ≤ (11254943233597/100000000000000 : ℝ)^3249
        have hw : |(-37993863/200000000 : ℝ)|=(37993863/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391147839/10000000000 : ℝ)|^4273 ≤ (22186263991847/50000000000000 : ℝ)^3249
        have hw : |(5391147839/10000000000 : ℝ)|=(5391147839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673893489/1250000000 : ℝ)|^4273 ≤ (44372528773897/100000000000000 : ℝ)^3249
        have hw : |(673893489/1250000000 : ℝ)|=(673893489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_box_1 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5284728341/10000000000 : ℝ)*x 0 + (-102267071/500000000 : ℝ)*x 1 + (269557419/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284728341/10000000000 : ℝ)^4273 ≤ (43224167900503/100000000000000 : ℝ)^3249 := by
    have hnat : (5284728341 : ℕ)^4273*100000000000000^3249 ≤ 43224167900503^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284728341 10000000000 43224167900503 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102267071/500000000 : ℝ)^4273 ≤ (12403298250299/100000000000000 : ℝ)^3249 := by
    have hnat : (102267071 : ℕ)^4273*100000000000000^3249 ≤ 12403298250299^3249*500000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102267071 500000000 12403298250299 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269557419/500000000 : ℝ)^4273 ≤ (2218626691993/5000000000000 : ℝ)^3249 := by
    have hnat : (269557419 : ℕ)^4273*5000000000000^3249 ≤ 2218626691993^3249*500000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269557419 500000000 2218626691993 5000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284728341/10000000000 : ℝ), (-102267071/500000000 : ℝ), (269557419/500000000 : ℝ)] ![(43224167900503/100000000000000 : ℝ), (12403298250299/100000000000000 : ℝ), (2218626691993/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284728341/10000000000 : ℝ)|^4273 ≤ (43224167900503/100000000000000 : ℝ)^3249
        have hw : |(5284728341/10000000000 : ℝ)|=(5284728341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-102267071/500000000 : ℝ)|^4273 ≤ (12403298250299/100000000000000 : ℝ)^3249
        have hw : |(-102267071/500000000 : ℝ)|=(102267071/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269557419/500000000 : ℝ)|^4273 ≤ (2218626691993/5000000000000 : ℝ)^3249
        have hw : |(269557419/500000000 : ℝ)|=(269557419/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_box_2 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1056945767/2000000000 : ℝ)*x 0 + (5391147891/10000000000 : ℝ)*x 1 + (-2045341417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056945767/2000000000 : ℝ)^4273 ≤ (10806043303603/25000000000000 : ℝ)^3249 := by
    have hnat : (1056945767 : ℕ)^4273*25000000000000^3249 ≤ 10806043303603^3249*2000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056945767 2000000000 10806043303603 25000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391147891/10000000000 : ℝ)^4273 ≤ (22186264273289/50000000000000 : ℝ)^3249 := by
    have hnat : (5391147891 : ℕ)^4273*50000000000000^3249 ≤ 22186264273289^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391147891 10000000000 22186264273289 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2045341417/10000000000 : ℝ)^4273 ≤ (12403298226373/100000000000000 : ℝ)^3249 := by
    have hnat : (2045341417 : ℕ)^4273*100000000000000^3249 ≤ 12403298226373^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045341417 10000000000 12403298226373 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056945767/2000000000 : ℝ), (5391147891/10000000000 : ℝ), (-2045341417/10000000000 : ℝ)] ![(10806043303603/25000000000000 : ℝ), (22186264273289/50000000000000 : ℝ), (12403298226373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056945767/2000000000 : ℝ)|^4273 ≤ (10806043303603/25000000000000 : ℝ)^3249
        have hw : |(1056945767/2000000000 : ℝ)|=(1056945767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391147891/10000000000 : ℝ)|^4273 ≤ (22186264273289/50000000000000 : ℝ)^3249
        have hw : |(5391147891/10000000000 : ℝ)|=(5391147891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2045341417/10000000000 : ℝ)|^4273 ≤ (12403298226373/100000000000000 : ℝ)^3249
        have hw : |(-2045341417/10000000000 : ℝ)|=(2045341417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_box_3 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (140098677/312500000 : ℝ)*x 0 + (4263770461/10000000000 : ℝ)*x 1 + (852754051/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (140098677/312500000 : ℝ)^4273 ≤ (17407739990733/50000000000000 : ℝ)^3249 := by
    have hnat : (140098677 : ℕ)^4273*50000000000000^3249 ≤ 17407739990733^3249*312500000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140098677 312500000 17407739990733 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4263770461/10000000000 : ℝ)^4273 ≤ (6518452207069/20000000000000 : ℝ)^3249 := by
    have hnat : (4263770461 : ℕ)^4273*20000000000000^3249 ≤ 6518452207069^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4263770461 10000000000 6518452207069 20000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (852754051/2000000000 : ℝ)^4273 ≤ (8148064741097/25000000000000 : ℝ)^3249 := by
    have hnat : (852754051 : ℕ)^4273*25000000000000^3249 ≤ 8148064741097^3249*2000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852754051 2000000000 8148064741097 25000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(140098677/312500000 : ℝ), (4263770461/10000000000 : ℝ), (852754051/2000000000 : ℝ)] ![(17407739990733/50000000000000 : ℝ), (6518452207069/20000000000000 : ℝ), (8148064741097/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(140098677/312500000 : ℝ)|^4273 ≤ (17407739990733/50000000000000 : ℝ)^3249
        have hw : |(140098677/312500000 : ℝ)|=(140098677/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4263770461/10000000000 : ℝ)|^4273 ≤ (6518452207069/20000000000000 : ℝ)^3249
        have hw : |(4263770461/10000000000 : ℝ)|=(4263770461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(852754051/2000000000 : ℝ)|^4273 ≤ (8148064741097/25000000000000 : ℝ)^3249
        have hw : |(852754051/2000000000 : ℝ)|=(852754051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_box_4 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2241655551/10000000000 : ℝ)*x 0 + (5264240109/10000000000 : ℝ)*x 1 + (5264240313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2241655551/10000000000 : ℝ)^4273 ≤ (6996086109659/50000000000000 : ℝ)^3249 := by
    have hnat : (2241655551 : ℕ)^4273*50000000000000^3249 ≤ 6996086109659^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241655551 10000000000 6996086109659 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264240109/10000000000 : ℝ)^4273 ≤ (2150195639543/5000000000000 : ℝ)^3249 := by
    have hnat : (5264240109 : ℕ)^4273*5000000000000^3249 ≤ 2150195639543^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264240109 10000000000 2150195639543 5000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264240313/10000000000 : ℝ)^4273 ≤ (43003914982583/100000000000000 : ℝ)^3249 := by
    have hnat : (5264240313 : ℕ)^4273*100000000000000^3249 ≤ 43003914982583^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264240313 10000000000 43003914982583 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2241655551/10000000000 : ℝ), (5264240109/10000000000 : ℝ), (5264240313/10000000000 : ℝ)] ![(6996086109659/50000000000000 : ℝ), (2150195639543/5000000000000 : ℝ), (43003914982583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2241655551/10000000000 : ℝ)|^4273 ≤ (6996086109659/50000000000000 : ℝ)^3249
        have hw : |(-2241655551/10000000000 : ℝ)|=(2241655551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264240109/10000000000 : ℝ)|^4273 ≤ (2150195639543/5000000000000 : ℝ)^3249
        have hw : |(5264240109/10000000000 : ℝ)|=(5264240109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264240313/10000000000 : ℝ)|^4273 ≤ (43003914982583/100000000000000 : ℝ)^3249
        have hw : |(5264240313/10000000000 : ℝ)|=(5264240313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_box_5 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671747033/1250000000 : ℝ)*x 0 + (-524013989/2500000000 : ℝ)*x 1 + (5264240353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671747033/1250000000 : ℝ)^4273 ≤ (690417876537/1562500000000 : ℝ)^3249 := by
    have hnat : (671747033 : ℕ)^4273*1562500000000^3249 ≤ 690417876537^3249*1250000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671747033 1250000000 690417876537 1562500000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524013989/2500000000 : ℝ)^4273 ≤ (12809340470737/100000000000000 : ℝ)^3249 := by
    have hnat : (524013989 : ℕ)^4273*100000000000000^3249 ≤ 12809340470737^3249*2500000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524013989 2500000000 12809340470737 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264240353/10000000000 : ℝ)^4273 ≤ (43003915412333/100000000000000 : ℝ)^3249 := by
    have hnat : (5264240353 : ℕ)^4273*100000000000000^3249 ≤ 43003915412333^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264240353 10000000000 43003915412333 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671747033/1250000000 : ℝ), (-524013989/2500000000 : ℝ), (5264240353/10000000000 : ℝ)] ![(690417876537/1562500000000 : ℝ), (12809340470737/100000000000000 : ℝ), (43003915412333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671747033/1250000000 : ℝ)|^4273 ≤ (690417876537/1562500000000 : ℝ)^3249
        have hw : |(671747033/1250000000 : ℝ)|=(671747033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-524013989/2500000000 : ℝ)|^4273 ≤ (12809340470737/100000000000000 : ℝ)^3249
        have hw : |(-524013989/2500000000 : ℝ)|=(524013989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264240353/10000000000 : ℝ)|^4273 ≤ (43003915412333/100000000000000 : ℝ)^3249
        have hw : |(5264240353/10000000000 : ℝ)|=(5264240353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_box_6 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074795219/2000000000 : ℝ)*x 0 + (16450751/31250000 : ℝ)*x 1 + (-2096056229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074795219/2000000000 : ℝ)^4273 ≤ (44186742270831/100000000000000 : ℝ)^3249 := by
    have hnat : (1074795219 : ℕ)^4273*100000000000000^3249 ≤ 44186742270831^3249*2000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074795219 2000000000 44186742270831 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16450751/31250000 : ℝ)^4273 ≤ (43003915057789/100000000000000 : ℝ)^3249 := by
    have hnat : (16450751 : ℕ)^4273*100000000000000^3249 ≤ 43003915057789^3249*31250000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16450751 31250000 43003915057789 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2096056229/10000000000 : ℝ)^4273 ≤ (1601167833113/12500000000000 : ℝ)^3249 := by
    have hnat : (2096056229 : ℕ)^4273*12500000000000^3249 ≤ 1601167833113^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096056229 10000000000 1601167833113 12500000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074795219/2000000000 : ℝ), (16450751/31250000 : ℝ), (-2096056229/10000000000 : ℝ)] ![(44186742270831/100000000000000 : ℝ), (43003915057789/100000000000000 : ℝ), (1601167833113/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074795219/2000000000 : ℝ)|^4273 ≤ (44186742270831/100000000000000 : ℝ)^3249
        have hw : |(1074795219/2000000000 : ℝ)|=(1074795219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16450751/31250000 : ℝ)|^4273 ≤ (43003915057789/100000000000000 : ℝ)^3249
        have hw : |(16450751/31250000 : ℝ)|=(16450751/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2096056229/10000000000 : ℝ)|^4273 ≤ (1601167833113/12500000000000 : ℝ)^3249
        have hw : |(-2096056229/10000000000 : ℝ)|=(2096056229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_box_7 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (418448467/1000000000 : ℝ)*x 0 + (2206526033/5000000000 : ℝ)*x 1 + (2206526217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418448467/1000000000 : ℝ)^4273 ≤ (15898765846979/50000000000000 : ℝ)^3249 := by
    have hnat : (418448467 : ℕ)^4273*50000000000000^3249 ≤ 15898765846979^3249*1000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418448467 1000000000 15898765846979 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2206526033/5000000000 : ℝ)^4273 ≤ (17050616134901/50000000000000 : ℝ)^3249 := by
    have hnat : (2206526033 : ℕ)^4273*50000000000000^3249 ≤ 17050616134901^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206526033 5000000000 17050616134901 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2206526217/5000000000 : ℝ)^4273 ≤ (34101236009719/100000000000000 : ℝ)^3249 := by
    have hnat : (2206526217 : ℕ)^4273*100000000000000^3249 ≤ 34101236009719^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206526217 5000000000 34101236009719 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(418448467/1000000000 : ℝ), (2206526033/5000000000 : ℝ), (2206526217/5000000000 : ℝ)] ![(15898765846979/50000000000000 : ℝ), (17050616134901/50000000000000 : ℝ), (34101236009719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(418448467/1000000000 : ℝ)|^4273 ≤ (15898765846979/50000000000000 : ℝ)^3249
        have hw : |(418448467/1000000000 : ℝ)|=(418448467/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2206526033/5000000000 : ℝ)|^4273 ≤ (17050616134901/50000000000000 : ℝ)^3249
        have hw : |(2206526033/5000000000 : ℝ)|=(2206526033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2206526217/5000000000 : ℝ)|^4273 ≤ (34101236009719/100000000000000 : ℝ)^3249
        have hw : |(2206526217/5000000000 : ℝ)|=(2206526217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_box_8 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1084961393/5000000000 : ℝ)*x 0 + (2588506291/5000000000 : ℝ)*x 1 + (270258997/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084961393/5000000000 : ℝ)^4273 ≤ (1675787125191/12500000000000 : ℝ)^3249 := by
    have hnat : (1084961393 : ℕ)^4273*12500000000000^3249 ≤ 1675787125191^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084961393 5000000000 1675787125191 12500000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588506291/5000000000 : ℝ)^4273 ≤ (42069219370747/100000000000000 : ℝ)^3249 := by
    have hnat : (2588506291 : ℕ)^4273*100000000000000^3249 ≤ 42069219370747^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588506291 5000000000 42069219370747 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270258997/500000000 : ℝ)^4273 ≤ (5565560452149/12500000000000 : ℝ)^3249 := by
    have hnat : (270258997 : ℕ)^4273*12500000000000^3249 ≤ 5565560452149^3249*500000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270258997 500000000 5565560452149 12500000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1084961393/5000000000 : ℝ), (2588506291/5000000000 : ℝ), (270258997/500000000 : ℝ)] ![(1675787125191/12500000000000 : ℝ), (42069219370747/100000000000000 : ℝ), (5565560452149/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1084961393/5000000000 : ℝ)|^4273 ≤ (1675787125191/12500000000000 : ℝ)^3249
        have hw : |(-1084961393/5000000000 : ℝ)|=(1084961393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588506291/5000000000 : ℝ)|^4273 ≤ (42069219370747/100000000000000 : ℝ)^3249
        have hw : |(2588506291/5000000000 : ℝ)|=(2588506291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270258997/500000000 : ℝ)|^4273 ≤ (5565560452149/12500000000000 : ℝ)^3249
        have hw : |(270258997/500000000 : ℝ)|=(270258997/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_box_9 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637427791/5000000000 : ℝ)*x 0 + (-2039599549/10000000000 : ℝ)*x 1 + (5405179283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637427791/5000000000 : ℝ)^4273 ≤ (2694874930743/6250000000000 : ℝ)^3249 := by
    have hnat : (2637427791 : ℕ)^4273*6250000000000^3249 ≤ 2694874930743^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637427791 5000000000 2694874930743 6250000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2039599549/10000000000 : ℝ)^4273 ≤ (772345286549/6250000000000 : ℝ)^3249 := by
    have hnat : (2039599549 : ℕ)^4273*6250000000000^3249 ≤ 772345286549^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039599549 10000000000 772345286549 6250000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405179283/10000000000 : ℝ)^4273 ≤ (44524476499531/100000000000000 : ℝ)^3249 := by
    have hnat : (5405179283 : ℕ)^4273*100000000000000^3249 ≤ 44524476499531^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405179283 10000000000 44524476499531 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637427791/5000000000 : ℝ), (-2039599549/10000000000 : ℝ), (5405179283/10000000000 : ℝ)] ![(2694874930743/6250000000000 : ℝ), (772345286549/6250000000000 : ℝ), (44524476499531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637427791/5000000000 : ℝ)|^4273 ≤ (2694874930743/6250000000000 : ℝ)^3249
        have hw : |(2637427791/5000000000 : ℝ)|=(2637427791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2039599549/10000000000 : ℝ)|^4273 ≤ (772345286549/6250000000000 : ℝ)^3249
        have hw : |(-2039599549/10000000000 : ℝ)|=(2039599549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405179283/10000000000 : ℝ)|^4273 ≤ (44524476499531/100000000000000 : ℝ)^3249
        have hw : |(5405179283/10000000000 : ℝ)|=(5405179283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_box_10 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054970973/2000000000 : ℝ)*x 0 + (2702589899/5000000000 : ℝ)*x 1 + (-2039599817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054970973/2000000000 : ℝ)^4273 ≤ (21558995591867/50000000000000 : ℝ)^3249 := by
    have hnat : (1054970973 : ℕ)^4273*50000000000000^3249 ≤ 21558995591867^3249*2000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054970973 2000000000 21558995591867 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702589899/5000000000 : ℝ)^4273 ≤ (5565560259853/12500000000000 : ℝ)^3249 := by
    have hnat : (2702589899 : ℕ)^4273*12500000000000^3249 ≤ 5565560259853^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702589899 5000000000 5565560259853 12500000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2039599817/10000000000 : ℝ)^4273 ≤ (12357526720309/100000000000000 : ℝ)^3249 := by
    have hnat : (2039599817 : ℕ)^4273*100000000000000^3249 ≤ 12357526720309^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039599817 10000000000 12357526720309 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054970973/2000000000 : ℝ), (2702589899/5000000000 : ℝ), (-2039599817/10000000000 : ℝ)] ![(21558995591867/50000000000000 : ℝ), (5565560259853/12500000000000 : ℝ), (12357526720309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054970973/2000000000 : ℝ)|^4273 ≤ (21558995591867/50000000000000 : ℝ)^3249
        have hw : |(1054970973/2000000000 : ℝ)|=(1054970973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702589899/5000000000 : ℝ)|^4273 ≤ (5565560259853/12500000000000 : ℝ)^3249
        have hw : |(2702589899/5000000000 : ℝ)|=(2702589899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2039599817/10000000000 : ℝ)|^4273 ≤ (12357526720309/100000000000000 : ℝ)^3249
        have hw : |(-2039599817/10000000000 : ℝ)|=(2039599817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_box_11 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (564452623/1250000000 : ℝ)*x 0 + (2123625471/5000000000 : ℝ)*x 1 + (2123625627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (564452623/1250000000 : ℝ)^4273 ≤ (35147419507903/100000000000000 : ℝ)^3249 := by
    have hnat : (564452623 : ℕ)^4273*100000000000000^3249 ≤ 35147419507903^3249*1250000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564452623 1250000000 35147419507903 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123625471/5000000000 : ℝ)^4273 ≤ (8106572168143/25000000000000 : ℝ)^3249 := by
    have hnat : (2123625471 : ℕ)^4273*25000000000000^3249 ≤ 8106572168143^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123625471 5000000000 8106572168143 25000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123625627/5000000000 : ℝ)^4273 ≤ (8106572951333/25000000000000 : ℝ)^3249 := by
    have hnat : (2123625627 : ℕ)^4273*25000000000000^3249 ≤ 8106572951333^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123625627 5000000000 8106572951333 25000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(564452623/1250000000 : ℝ), (2123625471/5000000000 : ℝ), (2123625627/5000000000 : ℝ)] ![(35147419507903/100000000000000 : ℝ), (8106572168143/25000000000000 : ℝ), (8106572951333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(564452623/1250000000 : ℝ)|^4273 ≤ (35147419507903/100000000000000 : ℝ)^3249
        have hw : |(564452623/1250000000 : ℝ)|=(564452623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2123625471/5000000000 : ℝ)|^4273 ≤ (8106572168143/25000000000000 : ℝ)^3249
        have hw : |(2123625471/5000000000 : ℝ)|=(2123625471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123625627/5000000000 : ℝ)|^4273 ≤ (8106572951333/25000000000000 : ℝ)^3249
        have hw : |(2123625627/5000000000 : ℝ)|=(2123625627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_box_12 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-985910057/5000000000 : ℝ)*x 0 + (2738051527/5000000000 : ℝ)*x 1 + (2626598067/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (985910057/5000000000 : ℝ)^4273 ≤ (2955070700261/25000000000000 : ℝ)^3249 := by
    have hnat : (985910057 : ℕ)^4273*25000000000000^3249 ≤ 2955070700261^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985910057 5000000000 2955070700261 25000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738051527/5000000000 : ℝ)^4273 ≤ (45294418733/100000000000 : ℝ)^3249 := by
    have hnat : (2738051527 : ℕ)^4273*100000000000^3249 ≤ 45294418733^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738051527 5000000000 45294418733 100000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626598067/5000000000 : ℝ)^4273 ≤ (4288529844823/10000000000000 : ℝ)^3249 := by
    have hnat : (2626598067 : ℕ)^4273*10000000000000^3249 ≤ 4288529844823^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626598067 5000000000 4288529844823 10000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-985910057/5000000000 : ℝ), (2738051527/5000000000 : ℝ), (2626598067/5000000000 : ℝ)] ![(2955070700261/25000000000000 : ℝ), (45294418733/100000000000 : ℝ), (4288529844823/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-985910057/5000000000 : ℝ)|^4273 ≤ (2955070700261/25000000000000 : ℝ)^3249
        have hw : |(-985910057/5000000000 : ℝ)|=(985910057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738051527/5000000000 : ℝ)|^4273 ≤ (45294418733/100000000000 : ℝ)^3249
        have hw : |(2738051527/5000000000 : ℝ)|=(2738051527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626598067/5000000000 : ℝ)|^4273 ≤ (4288529844823/10000000000000 : ℝ)^3249
        have hw : |(2626598067/5000000000 : ℝ)|=(2626598067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_box_13 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53817401/100000000 : ℝ)*x 0 + (-420072869/2000000000 : ℝ)*x 1 + (1313299087/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53817401/100000000 : ℝ)^4273 ≤ (22135359994941/50000000000000 : ℝ)^3249 := by
    have hnat : (53817401 : ℕ)^4273*50000000000000^3249 ≤ 22135359994941^3249*100000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53817401 100000000 22135359994941 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (420072869/2000000000 : ℝ)^4273 ≤ (802748703099/6250000000000 : ℝ)^3249 := by
    have hnat : (420072869 : ℕ)^4273*6250000000000^3249 ≤ 802748703099^3249*2000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420072869 2000000000 802748703099 6250000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313299087/2500000000 : ℝ)^4273 ≤ (42885300745869/100000000000000 : ℝ)^3249 := by
    have hnat : (1313299087 : ℕ)^4273*100000000000000^3249 ≤ 42885300745869^3249*2500000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313299087 2500000000 42885300745869 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53817401/100000000 : ℝ), (-420072869/2000000000 : ℝ), (1313299087/2500000000 : ℝ)] ![(22135359994941/50000000000000 : ℝ), (802748703099/6250000000000 : ℝ), (42885300745869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53817401/100000000 : ℝ)|^4273 ≤ (22135359994941/50000000000000 : ℝ)^3249
        have hw : |(53817401/100000000 : ℝ)|=(53817401/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-420072869/2000000000 : ℝ)|^4273 ≤ (802748703099/6250000000000 : ℝ)^3249
        have hw : |(-420072869/2000000000 : ℝ)|=(420072869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313299087/2500000000 : ℝ)|^4273 ≤ (42885300745869/100000000000000 : ℝ)^3249
        have hw : |(1313299087/2500000000 : ℝ)|=(1313299087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_box_14 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690869959/5000000000 : ℝ)*x 0 + (5253196811/10000000000 : ℝ)*x 1 + (-2100363971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690869959/5000000000 : ℝ)^4273 ≤ (4427071802087/10000000000000 : ℝ)^3249 := by
    have hnat : (2690869959 : ℕ)^4273*10000000000000^3249 ≤ 4427071802087^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690869959 5000000000 4427071802087 10000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253196811/10000000000 : ℝ)^4273 ≤ (42885305716929/100000000000000 : ℝ)^3249 := by
    have hnat : (5253196811 : ℕ)^4273*100000000000000^3249 ≤ 42885305716929^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253196811 10000000000 42885305716929 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2100363971/10000000000 : ℝ)^4273 ≤ (1284397624171/10000000000000 : ℝ)^3249 := by
    have hnat : (2100363971 : ℕ)^4273*10000000000000^3249 ≤ 1284397624171^3249*10000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100363971 10000000000 1284397624171 10000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690869959/5000000000 : ℝ), (5253196811/10000000000 : ℝ), (-2100363971/10000000000 : ℝ)] ![(4427071802087/10000000000000 : ℝ), (42885305716929/100000000000000 : ℝ), (1284397624171/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690869959/5000000000 : ℝ)|^4273 ≤ (4427071802087/10000000000000 : ℝ)^3249
        have hw : |(2690869959/5000000000 : ℝ)|=(2690869959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253196811/10000000000 : ℝ)|^4273 ≤ (42885305716929/100000000000000 : ℝ)^3249
        have hw : |(5253196811/10000000000 : ℝ)|=(5253196811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2100363971/10000000000 : ℝ)|^4273 ≤ (1284397624171/10000000000000 : ℝ)^3249
        have hw : |(-2100363971/10000000000 : ℝ)|=(2100363971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1313_box_15 (p : ℝ) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (103951131/250000000 : ℝ)*x 0 + (2213016947/5000000000 : ℝ)*x 1 + (1106508151/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103951131/250000000 : ℝ)^4273 ≤ (15766781195079/50000000000000 : ℝ)^3249 := by
    have hnat : (103951131 : ℕ)^4273*50000000000000^3249 ≤ 15766781195079^3249*250000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103951131 250000000 15766781195079 50000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2213016947/5000000000 : ℝ)^4273 ≤ (26744707313/78125000000 : ℝ)^3249 := by
    have hnat : (2213016947 : ℕ)^4273*78125000000^3249 ≤ 26744707313^3249*5000000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213016947 5000000000 26744707313 78125000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1106508151/2500000000 : ℝ)^4273 ≤ (34233212238461/100000000000000 : ℝ)^3249 := by
    have hnat : (1106508151 : ℕ)^4273*100000000000000^3249 ≤ 34233212238461^3249*2500000000^4273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106508151 2500000000 34233212238461 100000000000000 4273 3249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4273/1024 : ℝ)) 4273 3249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103951131/250000000 : ℝ), (2213016947/5000000000 : ℝ), (1106508151/2500000000 : ℝ)] ![(15766781195079/50000000000000 : ℝ), (26744707313/78125000000 : ℝ), (34233212238461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103951131/250000000 : ℝ)|^4273 ≤ (15766781195079/50000000000000 : ℝ)^3249
        have hw : |(103951131/250000000 : ℝ)|=(103951131/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2213016947/5000000000 : ℝ)|^4273 ≤ (26744707313/78125000000 : ℝ)^3249
        have hw : |(2213016947/5000000000 : ℝ)|=(2213016947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1106508151/2500000000 : ℝ)|^4273 ≤ (34233212238461/100000000000000 : ℝ)^3249
        have hw : |(1106508151/2500000000 : ℝ)|=(1106508151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1313_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7679353/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (277/2500 : ℝ)*pair X i i ≤ pair X i h) :
    -(12569/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11777/20000 : ℝ) ∧ (79783/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42119/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14687/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (277/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14687/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (277/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14687/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (277/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14687/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (277/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14687/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (277/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14687/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (277/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (277/2500 : ℝ) ^ (267/64 : ℝ) ≤ (2581542751535099/25000000000000000000 : ℝ) := by
    have hpowers : (277/2500 : ℝ)^267 ≤ (2581542751535099/25000000000000000000 : ℝ)^64 := by
      have hnat : (277 : ℕ)^267*25000000000000000000^64 ≤ 2581542751535099^64*2500^267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        277 2500 2581542751535099 25000000000000000000 267 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (277/2500 : ℝ)) (X := (2581542751535099/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14687/100000 : ℝ) ^ (267/64 : ℝ) ≤ (33461777351209169/100000000000000000000 : ℝ) := by
    have hpowers : (14687/100000 : ℝ)^267 ≤ (33461777351209169/100000000000000000000 : ℝ)^64 := by
      have hnat : (14687 : ℕ)^267*100000000000000000000^64 ≤ 33461777351209169^64*100000^267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14687 100000 33461777351209169 100000000000000000000 267 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14687/100000 : ℝ)) (X := (33461777351209169/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502581542751535099/12500000000000000000 : ℝ) ≤ (2500123749637733/2500000000000000 : ℝ) ^ (267/64 : ℝ) := by
    have hpowers : (12502581542751535099/12500000000000000000 : ℝ)^64 ≤ (2500123749637733/2500000000000000 : ℝ)^267 := by
      have hnat : (12502581542751535099 : ℕ)^64*2500000000000000^267 ≤ 2500123749637733^267*12500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502581542751535099 12500000000000000000 2500123749637733 2500000000000000 64 267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500123749637733/2500000000000000 : ℝ)) (X := (12502581542751535099/12500000000000000000 : ℝ)) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008757589671469913/20000000000000000000 : ℝ) ≤ (10001049424090997/10000000000000000 : ℝ) ^ (267/64 : ℝ) := by
    have hpowers : (20008757589671469913/20000000000000000000 : ℝ)^64 ≤ (10001049424090997/10000000000000000 : ℝ)^267 := by
      have hnat : (20008757589671469913 : ℕ)^64*10000000000000000^267 ≤ 10001049424090997^267*20000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008757589671469913 20000000000000000000 10001049424090997 10000000000000000 64 267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001049424090997/10000000000000000 : ℝ)) (X := (20008757589671469913/20000000000000000000 : ℝ)) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033461777351209169/50000000000000000000 : ℝ) ≤ (5000801924815531/5000000000000000 : ℝ) ^ (267/64 : ℝ) := by
    have hpowers : (50033461777351209169/50000000000000000000 : ℝ)^64 ≤ (5000801924815531/5000000000000000 : ℝ)^267 := by
      have hnat : (50033461777351209169 : ℕ)^64*5000000000000000^267 ≤ 5000801924815531^267*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033461777351209169 50000000000000000000 5000801924815531 5000000000000000 64 267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000801924815531/5000000000000000 : ℝ)) (X := (50033461777351209169/50000000000000000000 : ℝ)) (by norm_num) 267 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2581542751535099/25000000000000000000 : ℝ) ≤ ((9014874847451342831/9017500000000000000 : ℝ)+2*(110885108013/72140000000000 : ℝ)*(277/2500 : ℝ))^(267/64 : ℝ) := by
    rw [show (9014874847451342831/9017500000000000000 : ℝ)+2*(110885108013/72140000000000 : ℝ)*(277/2500 : ℝ)=(2500123749637733/2500000000000000 : ℝ) by norm_num, show 1+2*(2581542751535099/25000000000000000000 : ℝ)=(12502581542751535099/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33461777351209169/100000000000000000000 : ℝ)+(2581542751535099/25000000000000000000 : ℝ) ≤ ((9014874847451342831/9017500000000000000 : ℝ)+(110885108013/72140000000000 : ℝ)*((14687/100000 : ℝ)+(277/2500 : ℝ)))^(267/64 : ℝ) := by
    rw [show (9014874847451342831/9017500000000000000 : ℝ)+(110885108013/72140000000000 : ℝ)*((14687/100000 : ℝ)+(277/2500 : ℝ))=(10001049424090997/10000000000000000 : ℝ) by norm_num, show 1+(33461777351209169/100000000000000000000 : ℝ)+(2581542751535099/25000000000000000000 : ℝ)=(20008757589671469913/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33461777351209169/100000000000000000000 : ℝ) ≤ ((9014874847451342831/9017500000000000000 : ℝ)+2*(110885108013/72140000000000 : ℝ)*(14687/100000 : ℝ))^(267/64 : ℝ) := by
    rw [show (9014874847451342831/9017500000000000000 : ℝ)+2*(110885108013/72140000000000 : ℝ)*(14687/100000 : ℝ)=(5000801924815531/5000000000000000 : ℝ) by norm_num, show 1+2*(33461777351209169/100000000000000000000 : ℝ)=(50033461777351209169/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9014874847451342831/9017500000000000000 : ℝ)*(X 1 0+X 2 0)+(110885108013/72140000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (267/64 : ℝ)) (lo := (277/2500 : ℝ)) (hi := (14687/100000 : ℝ)) (c := (9014874847451342831/9017500000000000000 : ℝ)) (alpha := (110885108013/72140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9014874847451342831/9017500000000000000 : ℝ)*(X 0 1+X 2 1)+(110885108013/72140000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (267/64 : ℝ)) (lo := (277/2500 : ℝ)) (hi := (14687/100000 : ℝ)) (c := (9014874847451342831/9017500000000000000 : ℝ)) (alpha := (110885108013/72140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9014874847451342831/9017500000000000000 : ℝ)*(X 0 2+X 1 2)+(110885108013/72140000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (267/64 : ℝ)) (lo := (277/2500 : ℝ)) (hi := (14687/100000 : ℝ)) (c := (9014874847451342831/9017500000000000000 : ℝ)) (alpha := (110885108013/72140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-37993863/200000000 : ℝ)*X 0 0+(5391147839/10000000000 : ℝ)*X 0 1+(673893489/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5284728341/10000000000 : ℝ)*X 1 0+(-102267071/500000000 : ℝ)*X 1 1+(269557419/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1056945767/2000000000 : ℝ)*X 2 0+(5391147891/10000000000 : ℝ)*X 2 1+(-2045341417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((140098677/312500000 : ℝ)*X 0 0+(4263770461/10000000000 : ℝ)*X 0 1+(852754051/2000000000 : ℝ)*X 0 2+(140098677/312500000 : ℝ)*X 1 0+(4263770461/10000000000 : ℝ)*X 1 1+(852754051/2000000000 : ℝ)*X 1 2+(140098677/312500000 : ℝ)*X 2 0+(4263770461/10000000000 : ℝ)*X 2 1+(852754051/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2241655551/10000000000 : ℝ)*X 0 0+(5264240109/10000000000 : ℝ)*X 0 1+(5264240313/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((671747033/1250000000 : ℝ)*X 1 0+(-524013989/2500000000 : ℝ)*X 1 1+(5264240353/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1074795219/2000000000 : ℝ)*X 2 0+(16450751/31250000 : ℝ)*X 2 1+(-2096056229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((418448467/1000000000 : ℝ)*X 0 0+(2206526033/5000000000 : ℝ)*X 0 1+(2206526217/5000000000 : ℝ)*X 0 2+(418448467/1000000000 : ℝ)*X 1 0+(2206526033/5000000000 : ℝ)*X 1 1+(2206526217/5000000000 : ℝ)*X 1 2+(418448467/1000000000 : ℝ)*X 2 0+(2206526033/5000000000 : ℝ)*X 2 1+(2206526217/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1084961393/5000000000 : ℝ)*X 0 0+(2588506291/5000000000 : ℝ)*X 0 1+(270258997/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2637427791/5000000000 : ℝ)*X 1 0+(-2039599549/10000000000 : ℝ)*X 1 1+(5405179283/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1054970973/2000000000 : ℝ)*X 2 0+(2702589899/5000000000 : ℝ)*X 2 1+(-2039599817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((564452623/1250000000 : ℝ)*X 0 0+(2123625471/5000000000 : ℝ)*X 0 1+(2123625627/5000000000 : ℝ)*X 0 2+(564452623/1250000000 : ℝ)*X 1 0+(2123625471/5000000000 : ℝ)*X 1 1+(2123625627/5000000000 : ℝ)*X 1 2+(564452623/1250000000 : ℝ)*X 2 0+(2123625471/5000000000 : ℝ)*X 2 1+(2123625627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-985910057/5000000000 : ℝ)*X 0 0+(2738051527/5000000000 : ℝ)*X 0 1+(2626598067/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((53817401/100000000 : ℝ)*X 1 0+(-420072869/2000000000 : ℝ)*X 1 1+(1313299087/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2690869959/5000000000 : ℝ)*X 2 0+(5253196811/10000000000 : ℝ)*X 2 1+(-2100363971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((103951131/250000000 : ℝ)*X 0 0+(2213016947/5000000000 : ℝ)*X 0 1+(1106508151/2500000000 : ℝ)*X 0 2+(103951131/250000000 : ℝ)*X 1 0+(2213016947/5000000000 : ℝ)*X 1 1+(1106508151/2500000000 : ℝ)*X 1 2+(103951131/250000000 : ℝ)*X 2 0+(2213016947/5000000000 : ℝ)*X 2 1+(1106508151/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1313_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12569/20000 : ℝ) ≤ (-283341794459762626250425647704157/450875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46760287/50000000000000 : ℝ)*(upper1) + (191588879/100000000000000 : ℝ)*(lower4) + (31505441/25000000000000 : ℝ)*(upper5) + (2887875884181317/100000000000000 : ℝ)*(major0) + (2887875884181317/100000000000000 : ℝ)*(major1) + (2887875884181317/100000000000000 : ℝ)*(major2) + (5349901429/100000000000000 : ℝ)*(sp2) + (6016657827/100000000000000 : ℝ)*(sp3) + (391641222820037/10000000000000 : ℝ)*(sp4) + (1958156681739583/50000000000000 : ℝ)*(sp5) + (122387751097657/3125000000000 : ℝ)*(sp6) + (470069979100689/25000000000000 : ℝ)*(sp7) + (1156826083/100000000000000 : ℝ)*(sp12) + (100021547287/100000000000000 : ℝ)*(sp13) + (1880285933060583/100000000000000 : ℝ)*(f.failure) + (979103346256613/25000000000000 : ℝ)*(f.sum) + (15131204739691/3607000000000000000000000000 : ℝ)*base66 + (2267453532549036573/901750000000000000000000000000000 : ℝ)*base68 + (793617972139536573/901750000000000000000000000000000 : ℝ)*base70 + (7447530452478786573/901750000000000000000000000000000 : ℝ)*base72 + (9504458294103/3607000000000000000000000000 : ℝ)*base74 + (2045440435388036573/901750000000000000000000000000000 : ℝ)*base76 + (2505653669828036573/901750000000000000000000000000000 : ℝ)*base78 + (1263991639536286573/901750000000000000000000000000000 : ℝ)*base80 + (8613368640921/3607000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2242799/500000000000000000000 : ℝ)*base89 + (2242799/500000000000000000000 : ℝ)*base91 + (2242799/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (11777/20000 : ℝ) ≤ (132754784646915630939776867526099/225437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (111227/2500000000000 : ℝ)*(upper0) + (1915363/25000000000000 : ℝ)*(lower1) + (106998377/100000000000000 : ℝ)*(upper4) + (1477800636946343/50000000000000 : ℝ)*(major0) + (1477800636946343/50000000000000 : ℝ)*(major1) + (1477800636946343/50000000000000 : ℝ)*(major2) + (991797621199987/25000000000000 : ℝ)*(sp0) + (3967177743458133/100000000000000 : ℝ)*(sp1) + (247949232094289/6250000000000 : ℝ)*(sp2) + (1924380056771589/100000000000000 : ℝ)*(sp3) + (13898235151/100000000000000 : ℝ)*(sp5) + (196409233/5000000000000 : ℝ)*(sp6) + (820860453/50000000000000 : ℝ)*(sp7) + (144611667/12500000000000 : ℝ)*(sp8) + (962190849246247/50000000000000 : ℝ)*(f.failure) + (991797910423321/25000000000000 : ℝ)*(f.sum) + (13959710960411/1803500000000000000000000000 : ℝ)*base66 + (625743923565782967/450875000000000000000000000000000 : ℝ)*base68 + (496137424238967033/450875000000000000000000000000000 : ℝ)*base69 + (608805489439282967/450875000000000000000000000000000 : ℝ)*base72 + (29977042324449/721400000000000000000000000 : ℝ)*base74 + (2584797148034657967/450875000000000000000000000000000 : ℝ)*base76 + (255444099253092033/450875000000000000000000000000000 : ℝ)*base77 + (20263125385668282967/450875000000000000000000000000000 : ℝ)*base80 + (33567025292039/3607000000000000000000000000 : ℝ)*base82 + (361809/250000000000000000000 : ℝ)*base90 + (361809/250000000000000000000 : ℝ)*base92 + (361809/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (79783/100000 : ℝ) ≤ (89933054841602454213541392356373/112718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28604253/50000000000000 : ℝ)*(upper1) + (271925269/100000000000000 : ℝ)*(upper2) + (18441761/100000000000000 : ℝ)*(lower5) + (1634428975095661/50000000000000 : ℝ)*(major0) + (1634428975095661/50000000000000 : ℝ)*(major1) + (1634428975095661/50000000000000 : ℝ)*(major2) + (50423073813/25000000000000 : ℝ)*(sp1) + (244527692161/100000000000000 : ℝ)*(sp2) + (34567776983/25000000000000 : ℝ)*(sp3) + (36450540761/100000000000000 : ℝ)*(sp4) + (2191371150893881/50000000000000 : ℝ)*(sp8) + (438257706003327/10000000000000 : ℝ)*(sp9) + (4382534224636361/100000000000000 : ℝ)*(sp10) + (2128203758612099/100000000000000 : ℝ)*(sp11) + (66510688428751/3125000000000 : ℝ)*(f.failure) + (2191389376164261/50000000000000 : ℝ)*(f.sum) + (10056389631561/3607000000000000000000000000 : ℝ)*base66 + (617683646569443709/450875000000000000000000000000000 : ℝ)*base68 + (1000760093088443709/450875000000000000000000000000000 : ℝ)*base70 + (972602524163318709/450875000000000000000000000000000 : ℝ)*base72 + (1713891718347/1803500000000000000000000000 : ℝ)*base74 + (2168726845848318709/450875000000000000000000000000000 : ℝ)*base76 + (56225520562818709/450875000000000000000000000000000 : ℝ)*base78 + (2320843173771556291/450875000000000000000000000000000 : ℝ)*base79 + (3815646690431/1803500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (215603/15625000000000000000 : ℝ)*base89 + (215603/15625000000000000000 : ℝ)*base91 + (215603/15625000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-42119/50000 : ℝ) ≤ (-189899076453386869442127143664969/225437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (405992267/100000000000000 : ℝ)*(lower0) + (12229491/25000000000000 : ℝ)*(upper3) + (59960979/20000000000000 : ℝ)*(upper5) + (1652487290042933/50000000000000 : ℝ)*(major0) + (1652487290042933/50000000000000 : ℝ)*(major1) + (1652487290042933/50000000000000 : ℝ)*(major2) + (4199370763/100000000000000 : ℝ)*(sp0) + (105164894731/100000000000000 : ℝ)*(sp5) + (64092847353/100000000000000 : ℝ)*(sp7) + (1385663129/20000000000000 : ℝ)*(sp8) + (448615919002869/10000000000000 : ℝ)*(sp12) + (280379072051273/6250000000000 : ℝ)*(sp13) + (2243085158857549/50000000000000 : ℝ)*(sp14) + (2151793348844587/100000000000000 : ℝ)*(sp15) + (2151857441691941/100000000000000 : ℝ)*(f.failure) + (2243085158857549/50000000000000 : ℝ)*(f.sum) + (266737640159/112718750000000000000000000 : ℝ)*base65 + (3483312731635263323/450875000000000000000000000000000 : ℝ)*base67 + (2496577234262361677/450875000000000000000000000000000 : ℝ)*base70 + (4585473381805638323/450875000000000000000000000000000 : ℝ)*base71 + (92236947063851/1803500000000000000000000000 : ℝ)*base74 + (955162385483013323/450875000000000000000000000000000 : ℝ)*base75 + (7992798798148138323/450875000000000000000000000000000 : ℝ)*base77 + (11676843644901861677/450875000000000000000000000000000 : ℝ)*base80 + (4657041650043/1803500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2194173/500000000000000000000 : ℝ)*base89 + (2194173/500000000000000000000 : ℝ)*base91 + (2194173/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1313_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7679353/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (277/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12569/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(11777/20000 : ℝ) else (79783/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42119/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1313_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1313_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7679353/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11069/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12569/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(11777/20000 : ℝ) else (79783/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42119/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1313_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1313_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1313_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (267/64 : ℝ) ≤ p) (hpb : p ≤ (4273/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7679353/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11069/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12569/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(11777/20000 : ℝ) else (79783/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42119/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1313_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
