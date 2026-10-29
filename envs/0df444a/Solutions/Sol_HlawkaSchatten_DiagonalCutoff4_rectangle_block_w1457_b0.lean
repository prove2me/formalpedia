-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1457_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:07:01.310331+00:00
-- url     : https://prove2.me/submissions/9fa1c018-c038-4c36-80ef-21e0e0d724eb

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
theorem support_rectangle_w1457_s0_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1743069753/10000000000 : ℝ)*x 0 + (1189742261/2000000000 : ℝ)*x 1 + (967519507/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1743069753/10000000000 : ℝ)^4417 ≤ (5144168934401/50000000000000 : ℝ)^3393 := by
    have hnat : (1743069753 : ℕ)^4417*50000000000000^3393 ≤ 5144168934401^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1743069753 10000000000 5144168934401 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1189742261/2000000000 : ℝ)^4417 ≤ (50856236008969/100000000000000 : ℝ)^3393 := by
    have hnat : (1189742261 : ℕ)^4417*100000000000000^3393 ≤ 50856236008969^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1189742261 2000000000 50856236008969 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (967519507/2000000000 : ℝ)^4417 ≤ (7771085220051/20000000000000 : ℝ)^3393 := by
    have hnat : (967519507 : ℕ)^4417*20000000000000^3393 ≤ 7771085220051^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967519507 2000000000 7771085220051 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1743069753/10000000000 : ℝ), (1189742261/2000000000 : ℝ), (967519507/2000000000 : ℝ)] ![(5144168934401/50000000000000 : ℝ), (50856236008969/100000000000000 : ℝ), (7771085220051/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1743069753/10000000000 : ℝ)|^4417 ≤ (5144168934401/50000000000000 : ℝ)^3393
        have hw : |(-1743069753/10000000000 : ℝ)|=(1743069753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1189742261/2000000000 : ℝ)|^4417 ≤ (50856236008969/100000000000000 : ℝ)^3393
        have hw : |(1189742261/2000000000 : ℝ)|=(1189742261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(967519507/2000000000 : ℝ)|^4417 ≤ (7771085220051/20000000000000 : ℝ)^3393
        have hw : |(967519507/2000000000 : ℝ)|=(967519507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s0_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5488989887/10000000000 : ℝ)*x 0 + (-2369527139/10000000000 : ℝ)*x 1 + (4837597439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5488989887/10000000000 : ℝ)^4417 ≤ (45800668226083/100000000000000 : ℝ)^3393 := by
    have hnat : (5488989887 : ℕ)^4417*100000000000000^3393 ≤ 45800668226083^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488989887 10000000000 45800668226083 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2369527139/10000000000 : ℝ)^4417 ≤ (7671953334973/50000000000000 : ℝ)^3393 := by
    have hnat : (2369527139 : ℕ)^4417*50000000000000^3393 ≤ 7671953334973^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2369527139 10000000000 7671953334973 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4837597439/10000000000 : ℝ)^4417 ≤ (38855425096479/100000000000000 : ℝ)^3393 := by
    have hnat : (4837597439 : ℕ)^4417*100000000000000^3393 ≤ 38855425096479^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4837597439 10000000000 38855425096479 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5488989887/10000000000 : ℝ), (-2369527139/10000000000 : ℝ), (4837597439/10000000000 : ℝ)] ![(45800668226083/100000000000000 : ℝ), (7671953334973/50000000000000 : ℝ), (38855425096479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5488989887/10000000000 : ℝ)|^4417 ≤ (45800668226083/100000000000000 : ℝ)^3393
        have hw : |(5488989887/10000000000 : ℝ)|=(5488989887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2369527139/10000000000 : ℝ)|^4417 ≤ (7671953334973/50000000000000 : ℝ)^3393
        have hw : |(-2369527139/10000000000 : ℝ)|=(2369527139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4837597439/10000000000 : ℝ)|^4417 ≤ (38855425096479/100000000000000 : ℝ)^3393
        have hw : |(4837597439/10000000000 : ℝ)|=(4837597439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s0_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5488989903/10000000000 : ℝ)*x 0 + (1209399353/2500000000 : ℝ)*x 1 + (-2369527151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5488989903/10000000000 : ℝ)^4417 ≤ (1145016709997/2500000000000 : ℝ)^3393 := by
    have hnat : (5488989903 : ℕ)^4417*2500000000000^3393 ≤ 1145016709997^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488989903 10000000000 1145016709997 2500000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1209399353/2500000000 : ℝ)^4417 ≤ (38855424814167/100000000000000 : ℝ)^3393 := by
    have hnat : (1209399353 : ℕ)^4417*100000000000000^3393 ≤ 38855424814167^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209399353 2500000000 38855424814167 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2369527151/10000000000 : ℝ)^4417 ≤ (479497086597/3125000000000 : ℝ)^3393 := by
    have hnat : (2369527151 : ℕ)^4417*3125000000000^3393 ≤ 479497086597^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2369527151 10000000000 479497086597 3125000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5488989903/10000000000 : ℝ), (1209399353/2500000000 : ℝ), (-2369527151/10000000000 : ℝ)] ![(1145016709997/2500000000000 : ℝ), (38855424814167/100000000000000 : ℝ), (479497086597/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5488989903/10000000000 : ℝ)|^4417 ≤ (1145016709997/2500000000000 : ℝ)^3393
        have hw : |(5488989903/10000000000 : ℝ)|=(5488989903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1209399353/2500000000 : ℝ)|^4417 ≤ (38855424814167/100000000000000 : ℝ)^3393
        have hw : |(1209399353/2500000000 : ℝ)|=(1209399353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2369527151/10000000000 : ℝ)|^4417 ≤ (479497086597/3125000000000 : ℝ)^3393
        have hw : |(-2369527151/10000000000 : ℝ)|=(2369527151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s0_3 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4162010751/10000000000 : ℝ)*x 0 + (1551385483/5000000000 : ℝ)*x 1 + (345697679/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4162010751/10000000000 : ℝ)^4417 ≤ (15972751585901/50000000000000 : ℝ)^3393 := by
    have hnat : (4162010751 : ℕ)^4417*50000000000000^3393 ≤ 15972751585901^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162010751 10000000000 15972751585901 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1551385483/5000000000 : ℝ)^4417 ≤ (2179520170343/10000000000000 : ℝ)^3393 := by
    have hnat : (1551385483 : ℕ)^4417*10000000000000^3393 ≤ 2179520170343^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1551385483 5000000000 2179520170343 10000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345697679/625000000 : ℝ)^4417 ≤ (9251859022083/20000000000000 : ℝ)^3393 := by
    have hnat : (345697679 : ℕ)^4417*20000000000000^3393 ≤ 9251859022083^3393*625000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345697679 625000000 9251859022083 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4162010751/10000000000 : ℝ), (1551385483/5000000000 : ℝ), (345697679/625000000 : ℝ)] ![(15972751585901/50000000000000 : ℝ), (2179520170343/10000000000000 : ℝ), (9251859022083/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4162010751/10000000000 : ℝ)|^4417 ≤ (15972751585901/50000000000000 : ℝ)^3393
        have hw : |(4162010751/10000000000 : ℝ)|=(4162010751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1551385483/5000000000 : ℝ)|^4417 ≤ (2179520170343/10000000000000 : ℝ)^3393
        have hw : |(1551385483/5000000000 : ℝ)|=(1551385483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(345697679/625000000 : ℝ)|^4417 ≤ (9251859022083/20000000000000 : ℝ)^3393
        have hw : |(345697679/625000000 : ℝ)|=(345697679/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s0_4 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1746954329/10000000000 : ℝ)*x 0 + (2432981617/5000000000 : ℝ)*x 1 + (1183866633/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1746954329/10000000000 : ℝ)^4417 ≤ (10318196064663/100000000000000 : ℝ)^3393 := by
    have hnat : (1746954329 : ℕ)^4417*100000000000000^3393 ≤ 10318196064663^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1746954329 10000000000 10318196064663 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2432981617/5000000000 : ℝ)^4417 ≤ (39152279855211/100000000000000 : ℝ)^3393 := by
    have hnat : (2432981617 : ℕ)^4417*100000000000000^3393 ≤ 39152279855211^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2432981617 5000000000 39152279855211 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1183866633/2000000000 : ℝ)^4417 ≤ (50529524061897/100000000000000 : ℝ)^3393 := by
    have hnat : (1183866633 : ℕ)^4417*100000000000000^3393 ≤ 50529524061897^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183866633 2000000000 50529524061897 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1746954329/10000000000 : ℝ), (2432981617/5000000000 : ℝ), (1183866633/2000000000 : ℝ)] ![(10318196064663/100000000000000 : ℝ), (39152279855211/100000000000000 : ℝ), (50529524061897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1746954329/10000000000 : ℝ)|^4417 ≤ (10318196064663/100000000000000 : ℝ)^3393
        have hw : |(-1746954329/10000000000 : ℝ)|=(1746954329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2432981617/5000000000 : ℝ)|^4417 ≤ (39152279855211/100000000000000 : ℝ)^3393
        have hw : |(2432981617/5000000000 : ℝ)|=(2432981617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1183866633/2000000000 : ℝ)|^4417 ≤ (50529524061897/100000000000000 : ℝ)^3393
        have hw : |(1183866633/2000000000 : ℝ)|=(1183866633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s0_5 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5185604299/10000000000 : ℝ)*x 0 + (-321947827/2500000000 : ℝ)*x 1 + (1183866647/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5185604299/10000000000 : ℝ)^4417 ≤ (42533042175337/100000000000000 : ℝ)^3393 := by
    have hnat : (5185604299 : ℕ)^4417*100000000000000^3393 ≤ 42533042175337^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185604299 10000000000 42533042175337 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321947827/2500000000 : ℝ)^4417 ≤ (1734358241019/25000000000000 : ℝ)^3393 := by
    have hnat : (321947827 : ℕ)^4417*25000000000000^3393 ≤ 1734358241019^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321947827 2500000000 1734358241019 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1183866647/2000000000 : ℝ)^4417 ≤ (50529524839779/100000000000000 : ℝ)^3393 := by
    have hnat : (1183866647 : ℕ)^4417*100000000000000^3393 ≤ 50529524839779^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183866647 2000000000 50529524839779 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5185604299/10000000000 : ℝ), (-321947827/2500000000 : ℝ), (1183866647/2000000000 : ℝ)] ![(42533042175337/100000000000000 : ℝ), (1734358241019/25000000000000 : ℝ), (50529524839779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5185604299/10000000000 : ℝ)|^4417 ≤ (42533042175337/100000000000000 : ℝ)^3393
        have hw : |(5185604299/10000000000 : ℝ)|=(5185604299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-321947827/2500000000 : ℝ)|^4417 ≤ (1734358241019/25000000000000 : ℝ)^3393
        have hw : |(-321947827/2500000000 : ℝ)|=(321947827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1183866647/2000000000 : ℝ)|^4417 ≤ (50529524839779/100000000000000 : ℝ)^3393
        have hw : |(1183866647/2000000000 : ℝ)|=(1183866647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s0_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2592802167/5000000000 : ℝ)*x 0 + (1479833269/2500000000 : ℝ)*x 1 + (-1287791507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2592802167/5000000000 : ℝ)^4417 ≤ (42533042549051/100000000000000 : ℝ)^3393 := by
    have hnat : (2592802167 : ℕ)^4417*100000000000000^3393 ≤ 42533042549051^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592802167 5000000000 42533042549051 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1479833269/2500000000 : ℝ)^4417 ≤ (404236184583/800000000000 : ℝ)^3393 := by
    have hnat : (1479833269 : ℕ)^4417*800000000000^3393 ≤ 404236184583^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479833269 2500000000 404236184583 800000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1287791507/10000000000 : ℝ)^4417 ≤ (6937434359641/100000000000000 : ℝ)^3393 := by
    have hnat : (1287791507 : ℕ)^4417*100000000000000^3393 ≤ 6937434359641^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287791507 10000000000 6937434359641 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2592802167/5000000000 : ℝ), (1479833269/2500000000 : ℝ), (-1287791507/10000000000 : ℝ)] ![(42533042549051/100000000000000 : ℝ), (404236184583/800000000000 : ℝ), (6937434359641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2592802167/5000000000 : ℝ)|^4417 ≤ (42533042549051/100000000000000 : ℝ)^3393
        have hw : |(2592802167/5000000000 : ℝ)|=(2592802167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1479833269/2500000000 : ℝ)|^4417 ≤ (404236184583/800000000000 : ℝ)^3393
        have hw : |(1479833269/2500000000 : ℝ)|=(1479833269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1287791507/10000000000 : ℝ)|^4417 ≤ (6937434359641/100000000000000 : ℝ)^3393
        have hw : |(-1287791507/10000000000 : ℝ)|=(1287791507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s0_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41705009/100000000 : ℝ)*x 0 + (5469168037/10000000000 : ℝ)*x 1 + (1583489159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41705009/100000000 : ℝ)^4417 ≤ (32030362382517/100000000000000 : ℝ)^3393 := by
    have hnat : (41705009 : ℕ)^4417*100000000000000^3393 ≤ 32030362382517^3393*100000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41705009 100000000 32030362382517 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469168037/10000000000 : ℝ)^4417 ≤ (45585474212173/100000000000000 : ℝ)^3393 := by
    have hnat : (5469168037 : ℕ)^4417*100000000000000^3393 ≤ 45585474212173^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469168037 10000000000 45585474212173 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1583489159/5000000000 : ℝ)^4417 ≤ (559604084897/2500000000000 : ℝ)^3393 := by
    have hnat : (1583489159 : ℕ)^4417*2500000000000^3393 ≤ 559604084897^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583489159 5000000000 559604084897 2500000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41705009/100000000 : ℝ), (5469168037/10000000000 : ℝ), (1583489159/5000000000 : ℝ)] ![(32030362382517/100000000000000 : ℝ), (45585474212173/100000000000000 : ℝ), (559604084897/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41705009/100000000 : ℝ)|^4417 ≤ (32030362382517/100000000000000 : ℝ)^3393
        have hw : |(41705009/100000000 : ℝ)|=(41705009/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469168037/10000000000 : ℝ)|^4417 ≤ (45585474212173/100000000000000 : ℝ)^3393
        have hw : |(5469168037/10000000000 : ℝ)|=(5469168037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1583489159/5000000000 : ℝ)|^4417 ≤ (559604084897/2500000000000 : ℝ)^3393
        have hw : |(1583489159/5000000000 : ℝ)|=(1583489159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1457_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2243/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13033/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (69/16 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^69 ≤ (0 : ℝ)^16 := by
      have hnat : (0 : ℕ)^69*1^16 ≤ 0^16*1^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (69/16 : ℝ) ≤ (15020131778658159/781250000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^69 ≤ (15020131778658159/781250000000000000 : ℝ)^16 := by
      have hnat : (2 : ℕ)^69*781250000000000000^16 ≤ 15020131778658159^16*5^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 15020131778658159 781250000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (15020131778658159/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (1 : ℝ)^16 ≤ (1 : ℝ)^69 := by
      have hnat : (1 : ℕ)^16*1^69 ≤ 1^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (796270131778658159/781250000000000000 : ℝ) ≤ (2008851198480533/2000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (796270131778658159/781250000000000000 : ℝ)^16 ≤ (2008851198480533/2000000000000000 : ℝ)^69 := by
      have hnat : (796270131778658159 : ℕ)^16*2000000000000000^69 ≤ 2008851198480533^69*781250000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        796270131778658159 781250000000000000 2008851198480533 2000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2008851198480533/2000000000000000 : ℝ)) (X := (796270131778658159/781250000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (405645131778658159/390625000000000000 : ℝ) ≤ (1008851198480533/1000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (405645131778658159/390625000000000000 : ℝ)^16 ≤ (1008851198480533/1000000000000000 : ℝ)^69 := by
      have hnat : (405645131778658159 : ℕ)^16*1000000000000000^69 ≤ 1008851198480533^69*390625000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        405645131778658159 390625000000000000 1008851198480533 1000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1008851198480533/1000000000000000 : ℝ)) (X := (405645131778658159/390625000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(8851198480533/800000000000000 : ℝ)*(0 : ℝ))^(69/16 : ℝ) := by
    rw [show (1 : ℝ)+2*(8851198480533/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15020131778658159/781250000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(8851198480533/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(69/16 : ℝ) := by
    rw [show (1 : ℝ)+(8851198480533/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2008851198480533/2000000000000000 : ℝ) by norm_num, show 1+(15020131778658159/781250000000000000 : ℝ)+(0 : ℝ)=(796270131778658159/781250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15020131778658159/781250000000000000 : ℝ) ≤ ((1 : ℝ)+2*(8851198480533/800000000000000 : ℝ)*(2/5 : ℝ))^(69/16 : ℝ) := by
    rw [show (1 : ℝ)+2*(8851198480533/800000000000000 : ℝ)*(2/5 : ℝ)=(1008851198480533/1000000000000000 : ℝ) by norm_num, show 1+2*(15020131778658159/781250000000000000 : ℝ)=(405645131778658159/390625000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(8851198480533/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8851198480533/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(8851198480533/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8851198480533/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(8851198480533/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8851198480533/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1743069753/10000000000 : ℝ)*X 0 0+(1189742261/2000000000 : ℝ)*X 0 1+(967519507/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5488989887/10000000000 : ℝ)*X 1 0+(-2369527139/10000000000 : ℝ)*X 1 1+(4837597439/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5488989903/10000000000 : ℝ)*X 2 0+(1209399353/2500000000 : ℝ)*X 2 1+(-2369527151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4162010751/10000000000 : ℝ)*X 0 0+(1551385483/5000000000 : ℝ)*X 0 1+(345697679/625000000 : ℝ)*X 0 2+(4162010751/10000000000 : ℝ)*X 1 0+(1551385483/5000000000 : ℝ)*X 1 1+(345697679/625000000 : ℝ)*X 1 2+(4162010751/10000000000 : ℝ)*X 2 0+(1551385483/5000000000 : ℝ)*X 2 1+(345697679/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1746954329/10000000000 : ℝ)*X 0 0+(2432981617/5000000000 : ℝ)*X 0 1+(1183866633/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5185604299/10000000000 : ℝ)*X 1 0+(-321947827/2500000000 : ℝ)*X 1 1+(1183866647/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2592802167/5000000000 : ℝ)*X 2 0+(1479833269/2500000000 : ℝ)*X 2 1+(-1287791507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((41705009/100000000 : ℝ)*X 0 0+(5469168037/10000000000 : ℝ)*X 0 1+(1583489159/5000000000 : ℝ)*X 0 2+(41705009/100000000 : ℝ)*X 1 0+(5469168037/10000000000 : ℝ)*X 1 1+(1583489159/5000000000 : ℝ)*X 1 2+(41705009/100000000 : ℝ)*X 2 0+(5469168037/10000000000 : ℝ)*X 2 1+(1583489159/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (161808425750355230189757/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4958537/5000000000000 : ℝ)*(base1) + (1818594413/100000000000000 : ℝ)*(base19) + (182121787/10000000000000 : ℝ)*(base23) + (220163063/100000000000000 : ℝ)*(upper3) + (217606293/100000000000000 : ℝ)*(upper5) + (655905327120319/100000000000000 : ℝ)*(major0) + (655905327120319/100000000000000 : ℝ)*(major1) + (655905327120319/100000000000000 : ℝ)*(major2) + (450001830929187/50000000000000 : ℝ)*(sp0) + (900007864384157/100000000000000 : ℝ)*(sp1) + (900007861760701/100000000000000 : ℝ)*(sp2) + (51474724724207/12500000000000 : ℝ)*(sp3) + (6120290937/100000000000000 : ℝ)*(sp4) + (2804616951/100000000000000 : ℝ)*(sp7) + (411800701581347/100000000000000 : ℝ)*(f.failure) + (900009682978571/100000000000000 : ℝ)*(f.sum) + (66586323810027/40000000000000000000000000000 : ℝ)*base65 + (493328053370027/80000000000000000000000000000 : ℝ)*base67 + (89545838490027/80000000000000000000000000000 : ℝ)*base69 + (555179525050027/80000000000000000000000000000 : ℝ)*base71 + (163839267850027/40000000000000000000000000000 : ℝ)*base73 + (825478620250027/80000000000000000000000000000 : ℝ)*base75 + (368364985530027/80000000000000000000000000000 : ℝ)*base77 + (223505854650027/80000000000000000000000000000 : ℝ)*base79 + (82650616210027/40000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (10878261/1000000000000000000000 : ℝ)*base90 + (10878261/1000000000000000000000 : ℝ)*base92 + (10878261/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (166030936566282268142463/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (118997269/12500000000000 : ℝ)*(base19) + (480541451/50000000000000 : ℝ)*(base23) + (55250879/50000000000000 : ℝ)*(base32) + (146011739/100000000000000 : ℝ)*(upper3) + (40445473/50000000000000 : ℝ)*(upper5) + (691851330745579/100000000000000 : ℝ)*(major0) + (691851330745579/100000000000000 : ℝ)*(major1) + (691851330745579/100000000000000 : ℝ)*(major2) + (2302818837/100000000000000 : ℝ)*(sp1) + (2348921997/100000000000000 : ℝ)*(sp2) + (47466682075513/5000000000000 : ℝ)*(sp4) + (118666298339159/12500000000000 : ℝ)*(sp5) + (474665165752681/50000000000000 : ℝ)*(sp6) + (434368771120019/100000000000000 : ℝ)*(sp7) + (434368881621777/100000000000000 : ℝ)*(f.failure) + (47466682075513/5000000000000 : ℝ)*(f.sum) + (14833255086393/40000000000000000000000000000 : ℝ)*base66 + (557082276126393/80000000000000000000000000000 : ℝ)*base68 + (126509131953607/80000000000000000000000000000 : ℝ)*base69 + (148903180446393/80000000000000000000000000000 : ℝ)*base72 + (227684216046393/40000000000000000000000000000 : ℝ)*base74 + (594417305086393/80000000000000000000000000000 : ℝ)*base76 + (368853376606393/80000000000000000000000000000 : ℝ)*base78 + (1072381831006393/80000000000000000000000000000 : ℝ)*base80 + (100168928873607/40000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (7528649/1000000000000000000000 : ℝ)*base89 + (7528649/1000000000000000000000 : ℝ)*base91 + (7528649/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1457_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2243/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13033/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1457_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1457_s1_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-238934267/1250000000 : ℝ)*x 0 + (1398552559/2500000000 : ℝ)*x 1 + (5084089107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (238934267/1250000000 : ℝ)^4417 ≤ (5800387241451/50000000000000 : ℝ)^3393 := by
    have hnat : (238934267 : ℕ)^4417*50000000000000^3393 ≤ 5800387241451^3393*1250000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238934267 1250000000 5800387241451 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1398552559/2500000000 : ℝ)^4417 ≤ (23473448833523/50000000000000 : ℝ)^3393 := by
    have hnat : (1398552559 : ℕ)^4417*50000000000000^3393 ≤ 23473448833523^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1398552559 2500000000 23473448833523 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5084089107/10000000000 : ℝ)^4417 ≤ (20726163916379/50000000000000 : ℝ)^3393 := by
    have hnat : (5084089107 : ℕ)^4417*50000000000000^3393 ≤ 20726163916379^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084089107 10000000000 20726163916379 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-238934267/1250000000 : ℝ), (1398552559/2500000000 : ℝ), (5084089107/10000000000 : ℝ)] ![(5800387241451/50000000000000 : ℝ), (23473448833523/50000000000000 : ℝ), (20726163916379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-238934267/1250000000 : ℝ)|^4417 ≤ (5800387241451/50000000000000 : ℝ)^3393
        have hw : |(-238934267/1250000000 : ℝ)|=(238934267/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1398552559/2500000000 : ℝ)|^4417 ≤ (23473448833523/50000000000000 : ℝ)^3393
        have hw : |(1398552559/2500000000 : ℝ)|=(1398552559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5084089107/10000000000 : ℝ)|^4417 ≤ (20726163916379/50000000000000 : ℝ)^3393
        have hw : |(5084089107/10000000000 : ℝ)|=(5084089107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s1_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53940199/100000000 : ℝ)*x 0 + (-136325949/625000000 : ℝ)*x 1 + (5084091061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53940199/100000000 : ℝ)^4417 ≤ (44771777306179/100000000000000 : ℝ)^3393 := by
    have hnat : (53940199 : ℕ)^4417*100000000000000^3393 ≤ 44771777306179^3393*100000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53940199 100000000 44771777306179 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136325949/625000000 : ℝ)^4417 ≤ (13775874115719/100000000000000 : ℝ)^3393 := by
    have hnat : (136325949 : ℕ)^4417*100000000000000^3393 ≤ 13775874115719^3393*625000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136325949 625000000 13775874115719 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5084091061/10000000000 : ℝ)^4417 ≤ (20726174286263/50000000000000 : ℝ)^3393 := by
    have hnat : (5084091061 : ℕ)^4417*50000000000000^3393 ≤ 20726174286263^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084091061 10000000000 20726174286263 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53940199/100000000 : ℝ), (-136325949/625000000 : ℝ), (5084091061/10000000000 : ℝ)] ![(44771777306179/100000000000000 : ℝ), (13775874115719/100000000000000 : ℝ), (20726174286263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53940199/100000000 : ℝ)|^4417 ≤ (44771777306179/100000000000000 : ℝ)^3393
        have hw : |(53940199/100000000 : ℝ)|=(53940199/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-136325949/625000000 : ℝ)|^4417 ≤ (13775874115719/100000000000000 : ℝ)^3393
        have hw : |(-136325949/625000000 : ℝ)|=(136325949/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5084091061/10000000000 : ℝ)|^4417 ≤ (20726174286263/50000000000000 : ℝ)^3393
        have hw : |(5084091061/10000000000 : ℝ)|=(5084091061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s1_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394021537/10000000000 : ℝ)*x 0 + (1016817849/2000000000 : ℝ)*x 1 + (-136325961/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394021537/10000000000 : ℝ)^4417 ≤ (8954358998879/20000000000000 : ℝ)^3393 := by
    have hnat : (5394021537 : ℕ)^4417*20000000000000^3393 ≤ 8954358998879^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394021537 10000000000 8954358998879 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016817849/2000000000 : ℝ)^4417 ≤ (41452329297491/100000000000000 : ℝ)^3393 := by
    have hnat : (1016817849 : ℕ)^4417*100000000000000^3393 ≤ 41452329297491^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016817849 2000000000 41452329297491 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136325961/625000000 : ℝ)^4417 ≤ (6887937847147/50000000000000 : ℝ)^3393 := by
    have hnat : (136325961 : ℕ)^4417*50000000000000^3393 ≤ 6887937847147^3393*625000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136325961 625000000 6887937847147 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394021537/10000000000 : ℝ), (1016817849/2000000000 : ℝ), (-136325961/625000000 : ℝ)] ![(8954358998879/20000000000000 : ℝ), (41452329297491/100000000000000 : ℝ), (6887937847147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394021537/10000000000 : ℝ)|^4417 ≤ (8954358998879/20000000000000 : ℝ)^3393
        have hw : |(5394021537/10000000000 : ℝ)|=(5394021537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1016817849/2000000000 : ℝ)|^4417 ≤ (41452329297491/100000000000000 : ℝ)^3393
        have hw : |(1016817849/2000000000 : ℝ)|=(1016817849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-136325961/625000000 : ℝ)|^4417 ≤ (6887937847147/50000000000000 : ℝ)^3393
        have hw : |(-136325961/625000000 : ℝ)|=(136325961/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s1_3 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4271537507/10000000000 : ℝ)*x 0 + (3746182591/10000000000 : ℝ)*x 1 + (194442893/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4271537507/10000000000 : ℝ)^4417 ≤ (4130526013579/12500000000000 : ℝ)^3393 := by
    have hnat : (4271537507 : ℕ)^4417*12500000000000^3393 ≤ 4130526013579^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4271537507 10000000000 4130526013579 12500000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3746182591/10000000000 : ℝ)^4417 ≤ (5570946777913/20000000000000 : ℝ)^3393 := by
    have hnat : (3746182591 : ℕ)^4417*20000000000000^3393 ≤ 5570946777913^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3746182591 10000000000 5570946777913 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194442893/400000000 : ℝ)^4417 ≤ (19550528990563/50000000000000 : ℝ)^3393 := by
    have hnat : (194442893 : ℕ)^4417*50000000000000^3393 ≤ 19550528990563^3393*400000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194442893 400000000 19550528990563 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4271537507/10000000000 : ℝ), (3746182591/10000000000 : ℝ), (194442893/400000000 : ℝ)] ![(4130526013579/12500000000000 : ℝ), (5570946777913/20000000000000 : ℝ), (19550528990563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4271537507/10000000000 : ℝ)|^4417 ≤ (4130526013579/12500000000000 : ℝ)^3393
        have hw : |(4271537507/10000000000 : ℝ)|=(4271537507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3746182591/10000000000 : ℝ)|^4417 ≤ (5570946777913/20000000000000 : ℝ)^3393
        have hw : |(3746182591/10000000000 : ℝ)|=(3746182591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(194442893/400000000 : ℝ)|^4417 ≤ (19550528990563/50000000000000 : ℝ)^3393
        have hw : |(194442893/400000000 : ℝ)|=(194442893/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s1_4 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1911835739/10000000000 : ℝ)*x 0 + (318121301/625000000 : ℝ)*x 1 + (69853269/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1911835739/10000000000 : ℝ)^4417 ≤ (1450453932303/12500000000000 : ℝ)^3393 := by
    have hnat : (1911835739 : ℕ)^4417*12500000000000^3393 ≤ 1450453932303^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1911835739 10000000000 1450453932303 12500000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (318121301/625000000 : ℝ)^4417 ≤ (41514448689059/100000000000000 : ℝ)^3393 := by
    have hnat : (318121301 : ℕ)^4417*100000000000000^3393 ≤ 41514448689059^3393*625000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318121301 625000000 41514448689059 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69853269/125000000 : ℝ)^4417 ≤ (23440959920291/50000000000000 : ℝ)^3393 := by
    have hnat : (69853269 : ℕ)^4417*50000000000000^3393 ≤ 23440959920291^3393*125000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69853269 125000000 23440959920291 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1911835739/10000000000 : ℝ), (318121301/625000000 : ℝ), (69853269/125000000 : ℝ)] ![(1450453932303/12500000000000 : ℝ), (41514448689059/100000000000000 : ℝ), (23440959920291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1911835739/10000000000 : ℝ)|^4417 ≤ (1450453932303/12500000000000 : ℝ)^3393
        have hw : |(-1911835739/10000000000 : ℝ)|=(1911835739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(318121301/625000000 : ℝ)|^4417 ≤ (41514448689059/100000000000000 : ℝ)^3393
        have hw : |(318121301/625000000 : ℝ)|=(318121301/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(69853269/125000000 : ℝ)|^4417 ≤ (23440959920291/50000000000000 : ℝ)^3393
        have hw : |(69853269/125000000 : ℝ)|=(69853269/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s1_5 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5260468519/10000000000 : ℝ)*x 0 + (-1677043993/10000000000 : ℝ)*x 1 + (1397065389/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260468519/10000000000 : ℝ)^4417 ≤ (10833535599747/25000000000000 : ℝ)^3393 := by
    have hnat : (5260468519 : ℕ)^4417*25000000000000^3393 ≤ 10833535599747^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260468519 10000000000 10833535599747 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1677043993/10000000000 : ℝ)^4417 ≤ (9783937353233/100000000000000 : ℝ)^3393 := by
    have hnat : (1677043993 : ℕ)^4417*100000000000000^3393 ≤ 9783937353233^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1677043993 10000000000 9783937353233 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1397065389/2500000000 : ℝ)^4417 ≤ (46881920233747/100000000000000 : ℝ)^3393 := by
    have hnat : (1397065389 : ℕ)^4417*100000000000000^3393 ≤ 46881920233747^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397065389 2500000000 46881920233747 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260468519/10000000000 : ℝ), (-1677043993/10000000000 : ℝ), (1397065389/2500000000 : ℝ)] ![(10833535599747/25000000000000 : ℝ), (9783937353233/100000000000000 : ℝ), (46881920233747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260468519/10000000000 : ℝ)|^4417 ≤ (10833535599747/25000000000000 : ℝ)^3393
        have hw : |(5260468519/10000000000 : ℝ)|=(5260468519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1677043993/10000000000 : ℝ)|^4417 ≤ (9783937353233/100000000000000 : ℝ)^3393
        have hw : |(-1677043993/10000000000 : ℝ)|=(1677043993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1397065389/2500000000 : ℝ)|^4417 ≤ (46881920233747/100000000000000 : ℝ)^3393
        have hw : |(1397065389/2500000000 : ℝ)|=(1397065389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s1_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2630234203/5000000000 : ℝ)*x 0 + (69853269/125000000 : ℝ)*x 1 + (-335408841/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2630234203/5000000000 : ℝ)^4417 ≤ (43334141187197/100000000000000 : ℝ)^3393 := by
    have hnat : (2630234203 : ℕ)^4417*100000000000000^3393 ≤ 43334141187197^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630234203 5000000000 43334141187197 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69853269/125000000 : ℝ)^4417 ≤ (23440959920291/50000000000000 : ℝ)^3393 := by
    have hnat : (69853269 : ℕ)^4417*50000000000000^3393 ≤ 23440959920291^3393*125000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69853269 125000000 23440959920291 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (335408841/2000000000 : ℝ)^4417 ≤ (9783938963317/100000000000000 : ℝ)^3393 := by
    have hnat : (335408841 : ℕ)^4417*100000000000000^3393 ≤ 9783938963317^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335408841 2000000000 9783938963317 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2630234203/5000000000 : ℝ), (69853269/125000000 : ℝ), (-335408841/2000000000 : ℝ)] ![(43334141187197/100000000000000 : ℝ), (23440959920291/50000000000000 : ℝ), (9783938963317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2630234203/5000000000 : ℝ)|^4417 ≤ (43334141187197/100000000000000 : ℝ)^3393
        have hw : |(2630234203/5000000000 : ℝ)|=(2630234203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(69853269/125000000 : ℝ)|^4417 ≤ (23440959920291/50000000000000 : ℝ)^3393
        have hw : |(69853269/125000000 : ℝ)|=(69853269/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-335408841/2000000000 : ℝ)|^4417 ≤ (9783938963317/100000000000000 : ℝ)^3393
        have hw : |(-335408841/2000000000 : ℝ)|=(335408841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s1_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2136164259/5000000000 : ℝ)*x 0 + (303017803/625000000 : ℝ)*x 1 + (3759180777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136164259/5000000000 : ℝ)^4417 ≤ (8263043568521/25000000000000 : ℝ)^3393 := by
    have hnat : (2136164259 : ℕ)^4417*25000000000000^3393 ≤ 8263043568521^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136164259 5000000000 8263043568521 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (303017803/625000000 : ℝ)^4417 ≤ (38967209854629/100000000000000 : ℝ)^3393 := by
    have hnat : (303017803 : ℕ)^4417*100000000000000^3393 ≤ 38967209854629^3393*625000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303017803 625000000 38967209854629 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3759180777/10000000000 : ℝ)^4417 ≤ (27980615851467/100000000000000 : ℝ)^3393 := by
    have hnat : (3759180777 : ℕ)^4417*100000000000000^3393 ≤ 27980615851467^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3759180777 10000000000 27980615851467 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2136164259/5000000000 : ℝ), (303017803/625000000 : ℝ), (3759180777/10000000000 : ℝ)] ![(8263043568521/25000000000000 : ℝ), (38967209854629/100000000000000 : ℝ), (27980615851467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2136164259/5000000000 : ℝ)|^4417 ≤ (8263043568521/25000000000000 : ℝ)^3393
        have hw : |(2136164259/5000000000 : ℝ)|=(2136164259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(303017803/625000000 : ℝ)|^4417 ≤ (38967209854629/100000000000000 : ℝ)^3393
        have hw : |(303017803/625000000 : ℝ)|=(303017803/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3759180777/10000000000 : ℝ)|^4417 ≤ (27980615851467/100000000000000 : ℝ)^3393
        have hw : |(3759180777/10000000000 : ℝ)|=(3759180777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1457_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3939/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2333/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13033/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13033/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13033/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2243/100000 : ℝ) ^ (69/16 : ℝ) ≤ (482871151329/6250000000000000000 : ℝ) := by
    have hpowers : (2243/100000 : ℝ)^69 ≤ (482871151329/6250000000000000000 : ℝ)^16 := by
      have hnat : (2243 : ℕ)^69*6250000000000000000^16 ≤ 482871151329^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2243 100000 482871151329 6250000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2243/100000 : ℝ)) (X := (482871151329/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hpowhi : (13033/50000 : ℝ) ^ (69/16 : ℝ) ≤ (37907995802232347/12500000000000000000 : ℝ) := by
    have hpowers : (13033/50000 : ℝ)^69 ≤ (37907995802232347/12500000000000000000 : ℝ)^16 := by
      have hnat : (13033 : ℕ)^69*12500000000000000000^16 ≤ 37907995802232347^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13033 50000 37907995802232347 12500000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13033/50000 : ℝ)) (X := (37907995802232347/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125000482871151329/3125000000000000000 : ℝ) ≤ (1000000035830437/1000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (3125000482871151329/3125000000000000000 : ℝ)^16 ≤ (1000000035830437/1000000000000000 : ℝ)^69 := by
      have hnat : (3125000482871151329 : ℕ)^16*1000000000000000^69 ≤ 1000000035830437^69*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125000482871151329 3125000000000000000 1000000035830437 1000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000035830437/1000000000000000 : ℝ)) (X := (3125000482871151329/3125000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (2507581792308907001/2500000000000000000 : ℝ) ≤ (5003512105391313/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (2507581792308907001/2500000000000000000 : ℝ)^16 ≤ (5003512105391313/5000000000000000 : ℝ)^69 := by
      have hnat : (2507581792308907001 : ℕ)^16*5000000000000000^69 ≤ 5003512105391313^69*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2507581792308907001 2500000000000000000 5003512105391313 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003512105391313/5000000000000000 : ℝ)) (X := (2507581792308907001/2500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (6287907995802232347/6250000000000000000 : ℝ) ≤ (5007024031630441/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (6287907995802232347/6250000000000000000 : ℝ)^16 ≤ (5007024031630441/5000000000000000 : ℝ)^69 := by
      have hnat : (6287907995802232347 : ℕ)^16*5000000000000000^69 ≤ 5007024031630441^69*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6287907995802232347 6250000000000000000 5007024031630441 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007024031630441/5000000000000000 : ℝ)) (X := (6287907995802232347/6250000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(482871151329/6250000000000000000 : ℝ) ≤ ((119099249766833775047/119115000000000000000 : ℝ)+2*(438990779891/148893750000000 : ℝ)*(2243/100000 : ℝ))^(69/16 : ℝ) := by
    rw [show (119099249766833775047/119115000000000000000 : ℝ)+2*(438990779891/148893750000000 : ℝ)*(2243/100000 : ℝ)=(1000000035830437/1000000000000000 : ℝ) by norm_num, show 1+2*(482871151329/6250000000000000000 : ℝ)=(3125000482871151329/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37907995802232347/12500000000000000000 : ℝ)+(482871151329/6250000000000000000 : ℝ) ≤ ((119099249766833775047/119115000000000000000 : ℝ)+(438990779891/148893750000000 : ℝ)*((13033/50000 : ℝ)+(2243/100000 : ℝ)))^(69/16 : ℝ) := by
    rw [show (119099249766833775047/119115000000000000000 : ℝ)+(438990779891/148893750000000 : ℝ)*((13033/50000 : ℝ)+(2243/100000 : ℝ))=(5003512105391313/5000000000000000 : ℝ) by norm_num, show 1+(37907995802232347/12500000000000000000 : ℝ)+(482871151329/6250000000000000000 : ℝ)=(2507581792308907001/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37907995802232347/12500000000000000000 : ℝ) ≤ ((119099249766833775047/119115000000000000000 : ℝ)+2*(438990779891/148893750000000 : ℝ)*(13033/50000 : ℝ))^(69/16 : ℝ) := by
    rw [show (119099249766833775047/119115000000000000000 : ℝ)+2*(438990779891/148893750000000 : ℝ)*(13033/50000 : ℝ)=(5007024031630441/5000000000000000 : ℝ) by norm_num, show 1+2*(37907995802232347/12500000000000000000 : ℝ)=(6287907995802232347/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (119099249766833775047/119115000000000000000 : ℝ)*(X 1 0+X 2 0)+(438990779891/148893750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (2243/100000 : ℝ)) (hi := (13033/50000 : ℝ)) (c := (119099249766833775047/119115000000000000000 : ℝ)) (alpha := (438990779891/148893750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (119099249766833775047/119115000000000000000 : ℝ)*(X 0 1+X 2 1)+(438990779891/148893750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (2243/100000 : ℝ)) (hi := (13033/50000 : ℝ)) (c := (119099249766833775047/119115000000000000000 : ℝ)) (alpha := (438990779891/148893750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (119099249766833775047/119115000000000000000 : ℝ)*(X 0 2+X 1 2)+(438990779891/148893750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (2243/100000 : ℝ)) (hi := (13033/50000 : ℝ)) (c := (119099249766833775047/119115000000000000000 : ℝ)) (alpha := (438990779891/148893750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-238934267/1250000000 : ℝ)*X 0 0+(1398552559/2500000000 : ℝ)*X 0 1+(5084089107/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53940199/100000000 : ℝ)*X 1 0+(-136325949/625000000 : ℝ)*X 1 1+(5084091061/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5394021537/10000000000 : ℝ)*X 2 0+(1016817849/2000000000 : ℝ)*X 2 1+(-136325961/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4271537507/10000000000 : ℝ)*X 0 0+(3746182591/10000000000 : ℝ)*X 0 1+(194442893/400000000 : ℝ)*X 0 2+(4271537507/10000000000 : ℝ)*X 1 0+(3746182591/10000000000 : ℝ)*X 1 1+(194442893/400000000 : ℝ)*X 1 2+(4271537507/10000000000 : ℝ)*X 2 0+(3746182591/10000000000 : ℝ)*X 2 1+(194442893/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1911835739/10000000000 : ℝ)*X 0 0+(318121301/625000000 : ℝ)*X 0 1+(69853269/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5260468519/10000000000 : ℝ)*X 1 0+(-1677043993/10000000000 : ℝ)*X 1 1+(1397065389/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2630234203/5000000000 : ℝ)*X 2 0+(69853269/125000000 : ℝ)*X 2 1+(-335408841/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2136164259/5000000000 : ℝ)*X 0 0+(303017803/625000000 : ℝ)*X 0 1+(3759180777/10000000000 : ℝ)*X 0 2+(2136164259/5000000000 : ℝ)*X 1 0+(303017803/625000000 : ℝ)*X 1 1+(3759180777/10000000000 : ℝ)*X 1 2+(2136164259/5000000000 : ℝ)*X 2 0+(303017803/625000000 : ℝ)*X 2 1+(3759180777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21563355667419348937376389/8271875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74649191/25000000000000 : ℝ)*(base19) + (409211507/50000000000000 : ℝ)*(base23) + (2796281/25000000000000 : ℝ)*(upper2) + (3231061/6250000000000 : ℝ)*(upper4) + (113073/781250000000 : ℝ)*(lower5) + (35716162558289/2500000000000 : ℝ)*(major0) + (35716162558289/2500000000000 : ℝ)*(major1) + (35716162558289/2500000000000 : ℝ)*(major2) + (490081825770947/25000000000000 : ℝ)*(sp0) + (490084378384991/25000000000000 : ℝ)*(sp1) + (980168496856857/50000000000000 : ℝ)*(sp2) + (89695195619959/10000000000000 : ℝ)*(sp3) + (525452647/5000000000000 : ℝ)*(sp4) + (196839533/6250000000000 : ℝ)*(sp7) + (448477552816059/50000000000000 : ℝ)*(f.failure) + (245042226517091/12500000000000 : ℝ)*(f.sum) + (35621555417767/11911500000000000000000000000 : ℝ)*base65 + (830327745467779861/99262500000000000000000000000000 : ℝ)*base67 + (540947711719279861/99262500000000000000000000000000 : ℝ)*base69 + (597277978201879861/99262500000000000000000000000000 : ℝ)*base71 + (16609202275069/11911500000000000000000000000 : ℝ)*base73 + (165274769010820139/99262500000000000000000000000000 : ℝ)*base76 + (431809890330154861/99262500000000000000000000000000 : ℝ)*base77 + (41155838547754861/99262500000000000000000000000000 : ℝ)*base79 + (20061935368903/11911500000000000000000000000 : ℝ)*base81 + (2871517/500000000000000000000 : ℝ)*base90 + (2871517/500000000000000000000 : ℝ)*base92 + (2871517/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16640642543038423141379113957/1985250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (363224499/20000000000000 : ℝ)*(base19) + (1845291633/100000000000000 : ℝ)*(base23) + (22208829/10000000000000 : ℝ)*(upper3) + (37415723/100000000000000 : ℝ)*(lower4) + (171504823/100000000000000 : ℝ)*(upper5) + (1462462506712531/100000000000000 : ℝ)*(major0) + (1462462506712531/100000000000000 : ℝ)*(major1) + (1462462506712531/100000000000000 : ℝ)*(major2) + (11630226667/100000000000000 : ℝ)*(sp1) + (11675354903/100000000000000 : ℝ)*(sp2) + (501684684414783/25000000000000 : ℝ)*(sp4) + (2006725291309969/100000000000000 : ℝ)*(sp5) + (501681304253149/25000000000000 : ℝ)*(sp6) + (918185996361273/100000000000000 : ℝ)*(sp7) + (918185996361273/100000000000000 : ℝ)*(f.failure) + (501684684414783/25000000000000 : ℝ)*(f.sum) + (236914747106173/59557500000000000000000000000 : ℝ)*base65 + (15324784167245728681/3970500000000000000000000000000000 : ℝ)*base68 + (7821835714168228681/3970500000000000000000000000000000 : ℝ)*base70 + (17213862729319771319/3970500000000000000000000000000000 : ℝ)*base71 + (464075904354349/119115000000000000000000000000 : ℝ)*base74 + (57657367998756271319/3970500000000000000000000000000000 : ℝ)*base75 + (91754788738228681/3970500000000000000000000000000000 : ℝ)*base78 + (20170749412177228681/3970500000000000000000000000000000 : ℝ)*base80 + (250757717178559/119115000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3329201/1000000000000000000000 : ℝ)*base89 + (3329201/1000000000000000000000 : ℝ)*base91 + (3329201/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1457_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13033/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3939/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2333/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1457_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1457_s2_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-485642411/2500000000 : ℝ)*x 0 + (2726050177/5000000000 : ℝ)*x 1 + (520615289/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (485642411/2500000000 : ℝ)^4417 ≤ (370220300331/3125000000000 : ℝ)^3393 := by
    have hnat : (485642411 : ℕ)^4417*3125000000000^3393 ≤ 370220300331^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485642411 2500000000 370220300331 3125000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2726050177/5000000000 : ℝ)^4417 ≤ (1135009225441/2500000000000 : ℝ)^3393 := by
    have hnat : (2726050177 : ℕ)^4417*2500000000000^3393 ≤ 1135009225441^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726050177 5000000000 1135009225441 2500000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520615289/1000000000 : ℝ)^4417 ≤ (10688145338209/25000000000000 : ℝ)^3393 := by
    have hnat : (520615289 : ℕ)^4417*25000000000000^3393 ≤ 10688145338209^3393*1000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520615289 1000000000 10688145338209 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-485642411/2500000000 : ℝ), (2726050177/5000000000 : ℝ), (520615289/1000000000 : ℝ)] ![(370220300331/3125000000000 : ℝ), (1135009225441/2500000000000 : ℝ), (10688145338209/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-485642411/2500000000 : ℝ)|^4417 ≤ (370220300331/3125000000000 : ℝ)^3393
        have hw : |(-485642411/2500000000 : ℝ)|=(485642411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2726050177/5000000000 : ℝ)|^4417 ≤ (1135009225441/2500000000000 : ℝ)^3393
        have hw : |(2726050177/5000000000 : ℝ)|=(2726050177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(520615289/1000000000 : ℝ)|^4417 ≤ (10688145338209/25000000000000 : ℝ)^3393
        have hw : |(520615289/1000000000 : ℝ)|=(520615289/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s2_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669799591/1250000000 : ℝ)*x 0 + (-1034478739/5000000000 : ℝ)*x 1 + (2603076437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669799591/1250000000 : ℝ)^4417 ≤ (44387243761607/100000000000000 : ℝ)^3393 := by
    have hnat : (669799591 : ℕ)^4417*100000000000000^3393 ≤ 44387243761607^3393*1250000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669799591 1250000000 44387243761607 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034478739/5000000000 : ℝ)^4417 ≤ (3215043758401/25000000000000 : ℝ)^3393 := by
    have hnat : (1034478739 : ℕ)^4417*25000000000000^3393 ≤ 3215043758401^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034478739 5000000000 3215043758401 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2603076437/5000000000 : ℝ)^4417 ≤ (1336018161931/3125000000000 : ℝ)^3393 := by
    have hnat : (2603076437 : ℕ)^4417*3125000000000^3393 ≤ 1336018161931^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603076437 5000000000 1336018161931 3125000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669799591/1250000000 : ℝ), (-1034478739/5000000000 : ℝ), (2603076437/5000000000 : ℝ)] ![(44387243761607/100000000000000 : ℝ), (3215043758401/25000000000000 : ℝ), (1336018161931/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669799591/1250000000 : ℝ)|^4417 ≤ (44387243761607/100000000000000 : ℝ)^3393
        have hw : |(669799591/1250000000 : ℝ)|=(669799591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1034478739/5000000000 : ℝ)|^4417 ≤ (3215043758401/25000000000000 : ℝ)^3393
        have hw : |(-1034478739/5000000000 : ℝ)|=(1034478739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2603076437/5000000000 : ℝ)|^4417 ≤ (1336018161931/3125000000000 : ℝ)^3393
        have hw : |(2603076437/5000000000 : ℝ)|=(2603076437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s2_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358396823/10000000000 : ℝ)*x 0 + (130153819/250000000 : ℝ)*x 1 + (-32327461/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358396823/10000000000 : ℝ)^4417 ≤ (5548405598257/12500000000000 : ℝ)^3393 := by
    have hnat : (5358396823 : ℕ)^4417*12500000000000^3393 ≤ 5548405598257^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358396823 10000000000 5548405598257 12500000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130153819/250000000 : ℝ)^4417 ≤ (427525799631/1000000000000 : ℝ)^3393 := by
    have hnat : (130153819 : ℕ)^4417*1000000000000^3393 ≤ 427525799631^3393*250000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130153819 250000000 427525799631 1000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32327461/156250000 : ℝ)^4417 ≤ (3215043810997/25000000000000 : ℝ)^3393 := by
    have hnat : (32327461 : ℕ)^4417*25000000000000^3393 ≤ 3215043810997^3393*156250000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32327461 156250000 3215043810997 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358396823/10000000000 : ℝ), (130153819/250000000 : ℝ), (-32327461/156250000 : ℝ)] ![(5548405598257/12500000000000 : ℝ), (427525799631/1000000000000 : ℝ), (3215043810997/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358396823/10000000000 : ℝ)|^4417 ≤ (5548405598257/12500000000000 : ℝ)^3393
        have hw : |(5358396823/10000000000 : ℝ)|=(5358396823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130153819/250000000 : ℝ)|^4417 ≤ (427525799631/1000000000000 : ℝ)^3393
        have hw : |(130153819/250000000 : ℝ)|=(130153819/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-32327461/156250000 : ℝ)|^4417 ≤ (3215043810997/25000000000000 : ℝ)^3393
        have hw : |(-32327461/156250000 : ℝ)|=(32327461/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s2_3 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2146776543/5000000000 : ℝ)*x 0 + (4032249729/10000000000 : ℝ)*x 1 + (4569779813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146776543/5000000000 : ℝ)^4417 ≤ (33266090075431/100000000000000 : ℝ)^3393 := by
    have hnat : (2146776543 : ℕ)^4417*100000000000000^3393 ≤ 33266090075431^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146776543 5000000000 33266090075431 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4032249729/10000000000 : ℝ)^4417 ≤ (30655082796871/100000000000000 : ℝ)^3393 := by
    have hnat : (4032249729 : ℕ)^4417*100000000000000^3393 ≤ 30655082796871^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032249729 10000000000 30655082796871 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4569779813/10000000000 : ℝ)^4417 ≤ (36078827106849/100000000000000 : ℝ)^3393 := by
    have hnat : (4569779813 : ℕ)^4417*100000000000000^3393 ≤ 36078827106849^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4569779813 10000000000 36078827106849 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2146776543/5000000000 : ℝ), (4032249729/10000000000 : ℝ), (4569779813/10000000000 : ℝ)] ![(33266090075431/100000000000000 : ℝ), (30655082796871/100000000000000 : ℝ), (36078827106849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2146776543/5000000000 : ℝ)|^4417 ≤ (33266090075431/100000000000000 : ℝ)^3393
        have hw : |(2146776543/5000000000 : ℝ)|=(2146776543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4032249729/10000000000 : ℝ)|^4417 ≤ (30655082796871/100000000000000 : ℝ)^3393
        have hw : |(4032249729/10000000000 : ℝ)|=(4032249729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4569779813/10000000000 : ℝ)|^4417 ≤ (36078827106849/100000000000000 : ℝ)^3393
        have hw : |(4569779813/10000000000 : ℝ)|=(4569779813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s2_4 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-485652413/2500000000 : ℝ)*x 0 + (5207522869/10000000000 : ℝ)*x 1 + (68133999/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (485652413/2500000000 : ℝ)^4417 ≤ (1184736724339/10000000000000 : ℝ)^3393 := by
    have hnat : (485652413 : ℕ)^4417*10000000000000^3393 ≤ 1184736724339^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485652413 2500000000 1184736724339 10000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5207522869/10000000000 : ℝ)^4417 ≤ (21383613694759/50000000000000 : ℝ)^3393 := by
    have hnat : (5207522869 : ℕ)^4417*50000000000000^3393 ≤ 21383613694759^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207522869 10000000000 21383613694759 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68133999/125000000 : ℝ)^4417 ≤ (9077081069441/20000000000000 : ℝ)^3393 := by
    have hnat : (68133999 : ℕ)^4417*20000000000000^3393 ≤ 9077081069441^3393*125000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68133999 125000000 9077081069441 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-485652413/2500000000 : ℝ), (5207522869/10000000000 : ℝ), (68133999/125000000 : ℝ)] ![(1184736724339/10000000000000 : ℝ), (21383613694759/50000000000000 : ℝ), (9077081069441/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-485652413/2500000000 : ℝ)|^4417 ≤ (1184736724339/10000000000000 : ℝ)^3393
        have hw : |(-485652413/2500000000 : ℝ)|=(485652413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5207522869/10000000000 : ℝ)|^4417 ≤ (21383613694759/50000000000000 : ℝ)^3393
        have hw : |(5207522869/10000000000 : ℝ)|=(5207522869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68133999/125000000 : ℝ)|^4417 ≤ (9077081069441/20000000000000 : ℝ)^3393
        have hw : |(68133999/125000000 : ℝ)|=(68133999/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s2_5 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647138797/5000000000 : ℝ)*x 0 + (-1824388621/10000000000 : ℝ)*x 1 + (2725360613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647138797/5000000000 : ℝ)^4417 ≤ (2731065985551/6250000000000 : ℝ)^3393 := by
    have hnat : (2647138797 : ℕ)^4417*6250000000000^3393 ≤ 2731065985551^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647138797 5000000000 2731065985551 6250000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1824388621/10000000000 : ℝ)^4417 ≤ (10917524720641/100000000000000 : ℝ)^3393 := by
    have hnat : (1824388621 : ℕ)^4417*100000000000000^3393 ≤ 10917524720641^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824388621 10000000000 10917524720641 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725360613/5000000000 : ℝ)^4417 ≤ (45385419503483/100000000000000 : ℝ)^3393 := by
    have hnat : (2725360613 : ℕ)^4417*100000000000000^3393 ≤ 45385419503483^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725360613 5000000000 45385419503483 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647138797/5000000000 : ℝ), (-1824388621/10000000000 : ℝ), (2725360613/5000000000 : ℝ)] ![(2731065985551/6250000000000 : ℝ), (10917524720641/100000000000000 : ℝ), (45385419503483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647138797/5000000000 : ℝ)|^4417 ≤ (2731065985551/6250000000000 : ℝ)^3393
        have hw : |(2647138797/5000000000 : ℝ)|=(2647138797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1824388621/10000000000 : ℝ)|^4417 ≤ (10917524720641/100000000000000 : ℝ)^3393
        have hw : |(-1824388621/10000000000 : ℝ)|=(1824388621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725360613/5000000000 : ℝ)|^4417 ≤ (45385419503483/100000000000000 : ℝ)^3393
        have hw : |(2725360613/5000000000 : ℝ)|=(2725360613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s2_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529427661/1000000000 : ℝ)*x 0 + (5450720333/10000000000 : ℝ)*x 1 + (-1824391219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529427661/1000000000 : ℝ)^4417 ≤ (43697045196161/100000000000000 : ℝ)^3393 := by
    have hnat : (529427661 : ℕ)^4417*100000000000000^3393 ≤ 43697045196161^3393*1000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529427661 1000000000 43697045196161 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5450720333/10000000000 : ℝ)^4417 ≤ (11346352455971/25000000000000 : ℝ)^3393 := by
    have hnat : (5450720333 : ℕ)^4417*25000000000000^3393 ≤ 11346352455971^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450720333 10000000000 11346352455971 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1824391219/10000000000 : ℝ)^4417 ≤ (10917544959667/100000000000000 : ℝ)^3393 := by
    have hnat : (1824391219 : ℕ)^4417*100000000000000^3393 ≤ 10917544959667^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824391219 10000000000 10917544959667 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529427661/1000000000 : ℝ), (5450720333/10000000000 : ℝ), (-1824391219/10000000000 : ℝ)] ![(43697045196161/100000000000000 : ℝ), (11346352455971/25000000000000 : ℝ), (10917544959667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529427661/1000000000 : ℝ)|^4417 ≤ (43697045196161/100000000000000 : ℝ)^3393
        have hw : |(529427661/1000000000 : ℝ)|=(529427661/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5450720333/10000000000 : ℝ)|^4417 ≤ (11346352455971/25000000000000 : ℝ)^3393
        have hw : |(5450720333/10000000000 : ℝ)|=(5450720333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1824391219/10000000000 : ℝ)|^4417 ≤ (10917544959667/100000000000000 : ℝ)^3393
        have hw : |(-1824391219/10000000000 : ℝ)|=(1824391219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s2_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26835263/62500000 : ℝ)*x 0 + (4566789231/10000000000 : ℝ)*x 1 + (2017632037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26835263/62500000 : ℝ)^4417 ≤ (33266987691353/100000000000000 : ℝ)^3393 := by
    have hnat : (26835263 : ℕ)^4417*100000000000000^3393 ≤ 33266987691353^3393*62500000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26835263 62500000 33266987691353 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4566789231/10000000000 : ℝ)^4417 ≤ (18024046751317/50000000000000 : ℝ)^3393 := by
    have hnat : (4566789231 : ℕ)^4417*50000000000000^3393 ≤ 18024046751317^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4566789231 10000000000 18024046751317 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2017632037/5000000000 : ℝ)^4417 ≤ (7671229698357/25000000000000 : ℝ)^3393 := by
    have hnat : (2017632037 : ℕ)^4417*25000000000000^3393 ≤ 7671229698357^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017632037 5000000000 7671229698357 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26835263/62500000 : ℝ), (4566789231/10000000000 : ℝ), (2017632037/5000000000 : ℝ)] ![(33266987691353/100000000000000 : ℝ), (18024046751317/50000000000000 : ℝ), (7671229698357/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26835263/62500000 : ℝ)|^4417 ≤ (33266987691353/100000000000000 : ℝ)^3393
        have hw : |(26835263/62500000 : ℝ)|=(26835263/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4566789231/10000000000 : ℝ)|^4417 ≤ (18024046751317/50000000000000 : ℝ)^3393
        have hw : |(4566789231/10000000000 : ℝ)|=(4566789231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2017632037/5000000000 : ℝ)|^4417 ≤ (7671229698357/25000000000000 : ℝ)^3393
        have hw : |(2017632037/5000000000 : ℝ)|=(2017632037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1457_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2333/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3939/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (657/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15717/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2333/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3939/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2333/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3939/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2333/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3939/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2333/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3939/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2333/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3939/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2333/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3939/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (3939/50000 : ℝ) ^ (69/16 : ℝ) ≤ (870490233459897/50000000000000000000 : ℝ) := by
    have hpowers : (3939/50000 : ℝ)^69 ≤ (870490233459897/50000000000000000000 : ℝ)^16 := by
      have hnat : (3939 : ℕ)^69*50000000000000000000^16 ≤ 870490233459897^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3939 50000 870490233459897 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3939/50000 : ℝ)) (X := (870490233459897/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hpowhi : (2333/12500 : ℝ) ^ (69/16 : ℝ) ≤ (897672442306327/1250000000000000000 : ℝ) := by
    have hpowers : (2333/12500 : ℝ)^69 ≤ (897672442306327/1250000000000000000 : ℝ)^16 := by
      have hnat : (2333 : ℕ)^69*1250000000000000000^16 ≤ 897672442306327^16*12500^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2333 12500 897672442306327 1250000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2333/12500 : ℝ)) (X := (897672442306327/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000870490233459897/25000000000000000000 : ℝ) ≤ (2000016148008679/2000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (25000870490233459897/25000000000000000000 : ℝ)^16 ≤ (2000016148008679/2000000000000000 : ℝ)^69 := by
      have hnat : (25000870490233459897 : ℕ)^16*2000000000000000^69 ≤ 2000016148008679^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000870490233459897 25000000000000000000 2000016148008679 2000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000016148008679/2000000000000000 : ℝ)) (X := (25000870490233459897/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (50036777387925712977/50000000000000000000 : ℝ) ≤ (500085256818721/500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (50036777387925712977/50000000000000000000 : ℝ)^16 ≤ (500085256818721/500000000000000 : ℝ)^69 := by
      have hnat : (50036777387925712977 : ℕ)^16*500000000000000^69 ≤ 500085256818721^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036777387925712977 50000000000000000000 500085256818721 500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500085256818721/500000000000000 : ℝ)) (X := (50036777387925712977/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (625897672442306327/625000000000000000 : ℝ) ≤ (2000665906541089/2000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (625897672442306327/625000000000000000 : ℝ)^16 ≤ (2000665906541089/2000000000000000 : ℝ)^69 := by
      have hnat : (625897672442306327 : ℕ)^16*2000000000000000^69 ≤ 2000665906541089^69*625000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625897672442306327 625000000000000000 2000665906541089 2000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000665906541089/2000000000000000 : ℝ)) (X := (625897672442306327/625000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(870490233459897/50000000000000000000 : ℝ) ≤ ((10783527687351642857/10786000000000000000 : ℝ)+2*(64975853241/43144000000000 : ℝ)*(3939/50000 : ℝ))^(69/16 : ℝ) := by
    rw [show (10783527687351642857/10786000000000000000 : ℝ)+2*(64975853241/43144000000000 : ℝ)*(3939/50000 : ℝ)=(2000016148008679/2000000000000000 : ℝ) by norm_num, show 1+2*(870490233459897/50000000000000000000 : ℝ)=(25000870490233459897/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(897672442306327/1250000000000000000 : ℝ)+(870490233459897/50000000000000000000 : ℝ) ≤ ((10783527687351642857/10786000000000000000 : ℝ)+(64975853241/43144000000000 : ℝ)*((2333/12500 : ℝ)+(3939/50000 : ℝ)))^(69/16 : ℝ) := by
    rw [show (10783527687351642857/10786000000000000000 : ℝ)+(64975853241/43144000000000 : ℝ)*((2333/12500 : ℝ)+(3939/50000 : ℝ))=(500085256818721/500000000000000 : ℝ) by norm_num, show 1+(897672442306327/1250000000000000000 : ℝ)+(870490233459897/50000000000000000000 : ℝ)=(50036777387925712977/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(897672442306327/1250000000000000000 : ℝ) ≤ ((10783527687351642857/10786000000000000000 : ℝ)+2*(64975853241/43144000000000 : ℝ)*(2333/12500 : ℝ))^(69/16 : ℝ) := by
    rw [show (10783527687351642857/10786000000000000000 : ℝ)+2*(64975853241/43144000000000 : ℝ)*(2333/12500 : ℝ)=(2000665906541089/2000000000000000 : ℝ) by norm_num, show 1+2*(897672442306327/1250000000000000000 : ℝ)=(625897672442306327/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10783527687351642857/10786000000000000000 : ℝ)*(X 1 0+X 2 0)+(64975853241/43144000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (3939/50000 : ℝ)) (hi := (2333/12500 : ℝ)) (c := (10783527687351642857/10786000000000000000 : ℝ)) (alpha := (64975853241/43144000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10783527687351642857/10786000000000000000 : ℝ)*(X 0 1+X 2 1)+(64975853241/43144000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (3939/50000 : ℝ)) (hi := (2333/12500 : ℝ)) (c := (10783527687351642857/10786000000000000000 : ℝ)) (alpha := (64975853241/43144000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10783527687351642857/10786000000000000000 : ℝ)*(X 0 2+X 1 2)+(64975853241/43144000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (3939/50000 : ℝ)) (hi := (2333/12500 : ℝ)) (c := (10783527687351642857/10786000000000000000 : ℝ)) (alpha := (64975853241/43144000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-485642411/2500000000 : ℝ)*X 0 0+(2726050177/5000000000 : ℝ)*X 0 1+(520615289/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669799591/1250000000 : ℝ)*X 1 0+(-1034478739/5000000000 : ℝ)*X 1 1+(2603076437/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5358396823/10000000000 : ℝ)*X 2 0+(130153819/250000000 : ℝ)*X 2 1+(-32327461/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2146776543/5000000000 : ℝ)*X 0 0+(4032249729/10000000000 : ℝ)*X 0 1+(4569779813/10000000000 : ℝ)*X 0 2+(2146776543/5000000000 : ℝ)*X 1 0+(4032249729/10000000000 : ℝ)*X 1 1+(4569779813/10000000000 : ℝ)*X 1 2+(2146776543/5000000000 : ℝ)*X 2 0+(4032249729/10000000000 : ℝ)*X 2 1+(4569779813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-485652413/2500000000 : ℝ)*X 0 0+(5207522869/10000000000 : ℝ)*X 0 1+(68133999/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647138797/5000000000 : ℝ)*X 1 0+(-1824388621/10000000000 : ℝ)*X 1 1+(2725360613/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((529427661/1000000000 : ℝ)*X 2 0+(5450720333/10000000000 : ℝ)*X 2 1+(-1824391219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((26835263/62500000 : ℝ)*X 0 0+(4566789231/10000000000 : ℝ)*X 0 1+(2017632037/5000000000 : ℝ)*X 0 2+(26835263/62500000 : ℝ)*X 1 0+(4566789231/10000000000 : ℝ)*X 1 1+(2017632037/5000000000 : ℝ)*X 1 2+(26835263/62500000 : ℝ)*X 2 0+(4566789231/10000000000 : ℝ)*X 2 1+(2017632037/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (477677004662236656182814399/67412500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (146494801/10000000000000 : ℝ)*(base19) + (729686931/50000000000000 : ℝ)*(base23) + (20806681/50000000000000 : ℝ)*(lower2) + (40239683/20000000000000 : ℝ)*(upper3) + (130540393/100000000000000 : ℝ)*(upper5) + (740791381354431/25000000000000 : ℝ)*(major0) + (740791381354431/25000000000000 : ℝ)*(major1) + (740791381354431/25000000000000 : ℝ)*(major2) + (2032964922813453/50000000000000 : ℝ)*(sp0) + (2032974301468187/50000000000000 : ℝ)*(sp1) + (2032974304255261/50000000000000 : ℝ)*(sp2) + (116273141396877/6250000000000 : ℝ)*(sp3) + (20222257479/100000000000000 : ℝ)*(sp4) + (1310550621/12500000000000 : ℝ)*(sp7) + (372076149351/20000000000 : ℝ)*(f.failure) + (127060939621387/3125000000000 : ℝ)*(f.sum) + (114242138093/107860000000000000000000000 : ℝ)*base65 + (1106298998413049367/269650000000000000000000000000000 : ℝ)*base67 + (1596411937787999367/269650000000000000000000000000000 : ℝ)*base69 + (426414131653400633/269650000000000000000000000000000 : ℝ)*base72 + (11476459938129/2696500000000000000000000000 : ℝ)*base73 + (1690439201267599367/269650000000000000000000000000000 : ℝ)*base75 + (1134026868733499367/269650000000000000000000000000000 : ℝ)*base77 + (1282642347323799367/269650000000000000000000000000000 : ℝ)*base79 + (2801570435063/539300000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (687/200000000000000000 : ℝ)*base89 + (687/200000000000000000 : ℝ)*base91 + (687/200000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (502766419022040905261184651/107860000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50837873/100000000000000 : ℝ)*(base21) + (1626669/1250000000000 : ℝ)*(upper2) + (1354373/25000000000000 : ℝ)*(upper3) + (112094161/25000000000000 : ℝ)*(lower4) + (599329845002481/20000000000000 : ℝ)*(major0) + (599329845002481/20000000000000 : ℝ)*(major1) + (599329845002481/20000000000000 : ℝ)*(major2) + (1139537717/12500000000000 : ℝ)*(sp0) + (30852344991/100000000000000 : ℝ)*(sp1) + (7491530549/50000000000000 : ℝ)*(sp3) + (1027971543407741/25000000000000 : ℝ)*(sp4) + (411186443758771/10000000000000 : ℝ)*(sp5) + (1027973809773707/25000000000000 : ℝ)*(sp6) + (1881388021654767/100000000000000 : ℝ)*(sp7) + (235175375589483/12500000000000 : ℝ)*(f.failure) + (41118952899327/1000000000000 : ℝ)*(f.sum) + (171361355174089/10786000000000000000000000000 : ℝ)*base65 + (668251239783298217/215720000000000000000000000000000 : ℝ)*base67 + (350131442387738217/215720000000000000000000000000000 : ℝ)*base69 + (1376799404661541783/215720000000000000000000000000000 : ℝ)*base72 + (25319575978379/10786000000000000000000000000 : ℝ)*base73 + (615402516527541783/215720000000000000000000000000000 : ℝ)*base76 + (1395785761443781783/215720000000000000000000000000000 : ℝ)*base78 + (125988266350781783/215720000000000000000000000000000 : ℝ)*base80 + (2210967814177/431440000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1060029/125000000000000000000 : ℝ)*base90 + (1060029/125000000000000000000 : ℝ)*base92 + (1060029/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1457_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2333/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3939/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (657/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15717/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1457_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1457_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (657/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15717/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1457_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1457_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1457_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (657/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15717/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1457_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
