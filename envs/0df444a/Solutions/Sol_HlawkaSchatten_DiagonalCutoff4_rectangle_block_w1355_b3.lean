-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1355_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:09:15.968235+00:00
-- url     : https://prove2.me/submissions/8d38c80a-38ef-47c8-95cd-0cdfa966f6b2

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
theorem support_rectangle_w1355_box_0 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1866570907/10000000000 : ℝ)*x 0 + (5389394061/10000000000 : ℝ)*x 1 + (1347348681/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1866570907/10000000000 : ℝ)^4315 ≤ (2214413890247/20000000000000 : ℝ)^3291 := by
    have hnat : (1866570907 : ℕ)^4315*20000000000000^3291 ≤ 2214413890247^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866570907 10000000000 2214413890247 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5389394061/10000000000 : ℝ)^4315 ≤ (22231980841589/50000000000000 : ℝ)^3291 := by
    have hnat : (5389394061 : ℕ)^4315*50000000000000^3291 ≤ 22231980841589^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389394061 10000000000 22231980841589 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347348681/2500000000 : ℝ)^4315 ≤ (22231984427543/50000000000000 : ℝ)^3291 := by
    have hnat : (1347348681 : ℕ)^4315*50000000000000^3291 ≤ 22231984427543^3291*2500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347348681 2500000000 22231984427543 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1866570907/10000000000 : ℝ), (5389394061/10000000000 : ℝ), (1347348681/2500000000 : ℝ)] ![(2214413890247/20000000000000 : ℝ), (22231980841589/50000000000000 : ℝ), (22231984427543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1866570907/10000000000 : ℝ)|^4315 ≤ (2214413890247/20000000000000 : ℝ)^3291
        have hw : |(-1866570907/10000000000 : ℝ)|=(1866570907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5389394061/10000000000 : ℝ)|^4315 ≤ (22231980841589/50000000000000 : ℝ)^3291
        have hw : |(5389394061/10000000000 : ℝ)|=(5389394061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347348681/2500000000 : ℝ)|^4315 ≤ (22231984427543/50000000000000 : ℝ)^3291
        have hw : |(1347348681/2500000000 : ℝ)|=(1347348681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_box_1 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285337131/10000000000 : ℝ)*x 0 + (-200919731/1000000000 : ℝ)*x 1 + (673674253/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285337131/10000000000 : ℝ)^4315 ≤ (433417370689/1000000000000 : ℝ)^3291 := by
    have hnat : (5285337131 : ℕ)^4315*1000000000000^3291 ≤ 433417370689^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285337131 10000000000 433417370689 1000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200919731/1000000000 : ℝ)^4315 ≤ (12194301630879/100000000000000 : ℝ)^3291 := by
    have hnat : (200919731 : ℕ)^4315*100000000000000^3291 ≤ 12194301630879^3291*1000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200919731 1000000000 12194301630879 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673674253/1250000000 : ℝ)^4315 ≤ (5557995160367/12500000000000 : ℝ)^3291 := by
    have hnat : (673674253 : ℕ)^4315*12500000000000^3291 ≤ 5557995160367^3291*1250000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673674253 1250000000 5557995160367 12500000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285337131/10000000000 : ℝ), (-200919731/1000000000 : ℝ), (673674253/1250000000 : ℝ)] ![(433417370689/1000000000000 : ℝ), (12194301630879/100000000000000 : ℝ), (5557995160367/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285337131/10000000000 : ℝ)|^4315 ≤ (433417370689/1000000000000 : ℝ)^3291
        have hw : |(5285337131/10000000000 : ℝ)|=(5285337131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-200919731/1000000000 : ℝ)|^4315 ≤ (12194301630879/100000000000000 : ℝ)^3291
        have hw : |(-200919731/1000000000 : ℝ)|=(200919731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673674253/1250000000 : ℝ)|^4315 ≤ (5557995160367/12500000000000 : ℝ)^3291
        have hw : |(673674253/1250000000 : ℝ)|=(673674253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_box_2 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285336953/10000000000 : ℝ)*x 0 + (5389394219/10000000000 : ℝ)*x 1 + (-2009197287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285336953/10000000000 : ℝ)^4315 ≤ (2708858447191/6250000000000 : ℝ)^3291 := by
    have hnat : (5285336953 : ℕ)^4315*6250000000000^3291 ≤ 2708858447191^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285336953 10000000000 2708858447191 6250000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5389394219/10000000000 : ℝ)^4315 ≤ (44463963392321/100000000000000 : ℝ)^3291 := by
    have hnat : (5389394219 : ℕ)^4315*100000000000000^3291 ≤ 44463963392321^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389394219 10000000000 44463963392321 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2009197287/10000000000 : ℝ)^4315 ≤ (3048575361963/25000000000000 : ℝ)^3291 := by
    have hnat : (2009197287 : ℕ)^4315*25000000000000^3291 ≤ 3048575361963^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009197287 10000000000 3048575361963 25000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285336953/10000000000 : ℝ), (5389394219/10000000000 : ℝ), (-2009197287/10000000000 : ℝ)] ![(2708858447191/6250000000000 : ℝ), (44463963392321/100000000000000 : ℝ), (3048575361963/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285336953/10000000000 : ℝ)|^4315 ≤ (2708858447191/6250000000000 : ℝ)^3291
        have hw : |(5285336953/10000000000 : ℝ)|=(5285336953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5389394219/10000000000 : ℝ)|^4315 ≤ (44463963392321/100000000000000 : ℝ)^3291
        have hw : |(5389394219/10000000000 : ℝ)|=(5389394219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2009197287/10000000000 : ℝ)|^4315 ≤ (3048575361963/25000000000000 : ℝ)^3291
        have hw : |(-2009197287/10000000000 : ℝ)|=(2009197287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_box_3 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1117779779/2500000000 : ℝ)*x 0 + (531644019/1250000000 : ℝ)*x 1 + (10632881/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1117779779/2500000000 : ℝ)^4315 ≤ (34805083898371/100000000000000 : ℝ)^3291 := by
    have hnat : (1117779779 : ℕ)^4315*100000000000000^3291 ≤ 34805083898371^3291*2500000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117779779 2500000000 34805083898371 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531644019/1250000000 : ℝ)^4315 ≤ (32597456796951/100000000000000 : ℝ)^3291 := by
    have hnat : (531644019 : ℕ)^4315*100000000000000^3291 ≤ 32597456796951^3291*1250000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531644019 1250000000 32597456796951 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10632881/25000000 : ℝ)^4315 ≤ (32597459289119/100000000000000 : ℝ)^3291 := by
    have hnat : (10632881 : ℕ)^4315*100000000000000^3291 ≤ 32597459289119^3291*25000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10632881 25000000 32597459289119 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1117779779/2500000000 : ℝ), (531644019/1250000000 : ℝ), (10632881/25000000 : ℝ)] ![(34805083898371/100000000000000 : ℝ), (32597456796951/100000000000000 : ℝ), (32597459289119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1117779779/2500000000 : ℝ)|^4315 ≤ (34805083898371/100000000000000 : ℝ)^3291
        have hw : |(1117779779/2500000000 : ℝ)|=(1117779779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(531644019/1250000000 : ℝ)|^4315 ≤ (32597456796951/100000000000000 : ℝ)^3291
        have hw : |(531644019/1250000000 : ℝ)|=(531644019/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10632881/25000000 : ℝ)|^4315 ≤ (32597459289119/100000000000000 : ℝ)^3291
        have hw : |(10632881/25000000 : ℝ)|=(10632881/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_box_4 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2201772197/10000000000 : ℝ)*x 0 + (5265208119/10000000000 : ℝ)*x 1 + (5265208069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2201772197/10000000000 : ℝ)^4315 ≤ (13749121252813/100000000000000 : ℝ)^3291 := by
    have hnat : (2201772197 : ℕ)^4315*100000000000000^3291 ≤ 13749121252813^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201772197 10000000000 13749121252813 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265208119/10000000000 : ℝ)^4315 ≤ (21562719816307/50000000000000 : ℝ)^3291 := by
    have hnat : (5265208119 : ℕ)^4315*50000000000000^3291 ≤ 21562719816307^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265208119 10000000000 21562719816307 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265208069/10000000000 : ℝ)^4315 ≤ (8625087819131/20000000000000 : ℝ)^3291 := by
    have hnat : (5265208069 : ℕ)^4315*20000000000000^3291 ≤ 8625087819131^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265208069 10000000000 8625087819131 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2201772197/10000000000 : ℝ), (5265208119/10000000000 : ℝ), (5265208069/10000000000 : ℝ)] ![(13749121252813/100000000000000 : ℝ), (21562719816307/50000000000000 : ℝ), (8625087819131/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2201772197/10000000000 : ℝ)|^4315 ≤ (13749121252813/100000000000000 : ℝ)^3291
        have hw : |(-2201772197/10000000000 : ℝ)|=(2201772197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265208119/10000000000 : ℝ)|^4315 ≤ (21562719816307/50000000000000 : ℝ)^3291
        have hw : |(5265208119/10000000000 : ℝ)|=(5265208119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265208069/10000000000 : ℝ)|^4315 ≤ (8625087819131/20000000000000 : ℝ)^3291
        have hw : |(5265208069/10000000000 : ℝ)|=(5265208069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_box_5 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2686257367/5000000000 : ℝ)*x 0 + (-128694989/625000000 : ℝ)*x 1 + (131630209/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686257367/5000000000 : ℝ)^4315 ≤ (22140730510703/50000000000000 : ℝ)^3291 := by
    have hnat : (2686257367 : ℕ)^4315*50000000000000^3291 ≤ 22140730510703^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686257367 5000000000 22140730510703 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128694989/625000000 : ℝ)^4315 ≤ (12593096751991/100000000000000 : ℝ)^3291 := by
    have hnat : (128694989 : ℕ)^4315*100000000000000^3291 ≤ 12593096751991^3291*625000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128694989 625000000 12593096751991 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131630209/250000000 : ℝ)^4315 ≤ (8625088444151/20000000000000 : ℝ)^3291 := by
    have hnat : (131630209 : ℕ)^4315*20000000000000^3291 ≤ 8625088444151^3291*250000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131630209 250000000 8625088444151 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686257367/5000000000 : ℝ), (-128694989/625000000 : ℝ), (131630209/250000000 : ℝ)] ![(22140730510703/50000000000000 : ℝ), (12593096751991/100000000000000 : ℝ), (8625088444151/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686257367/5000000000 : ℝ)|^4315 ≤ (22140730510703/50000000000000 : ℝ)^3291
        have hw : |(2686257367/5000000000 : ℝ)|=(2686257367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128694989/625000000 : ℝ)|^4315 ≤ (12593096751991/100000000000000 : ℝ)^3291
        have hw : |(-128694989/625000000 : ℝ)|=(128694989/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131630209/250000000 : ℝ)|^4315 ≤ (8625088444151/20000000000000 : ℝ)^3291
        have hw : |(131630209/250000000 : ℝ)|=(131630209/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_box_6 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5372515003/10000000000 : ℝ)*x 0 + (2632604083/5000000000 : ℝ)*x 1 + (-51477993/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372515003/10000000000 : ℝ)^4315 ≤ (11070365982109/25000000000000 : ℝ)^3291 := by
    have hnat : (5372515003 : ℕ)^4315*25000000000000^3291 ≤ 11070365982109^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372515003 10000000000 11070365982109 25000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632604083/5000000000 : ℝ)^4315 ≤ (8625088027471/20000000000000 : ℝ)^3291 := by
    have hnat : (2632604083 : ℕ)^4315*20000000000000^3291 ≤ 8625088027471^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632604083 5000000000 8625088027471 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51477993/250000000 : ℝ)^4315 ≤ (6296547959023/50000000000000 : ℝ)^3291 := by
    have hnat : (51477993 : ℕ)^4315*50000000000000^3291 ≤ 6296547959023^3291*250000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51477993 250000000 6296547959023 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372515003/10000000000 : ℝ), (2632604083/5000000000 : ℝ), (-51477993/250000000 : ℝ)] ![(11070365982109/25000000000000 : ℝ), (8625088027471/20000000000000 : ℝ), (6296547959023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372515003/10000000000 : ℝ)|^4315 ≤ (11070365982109/25000000000000 : ℝ)^3291
        have hw : |(5372515003/10000000000 : ℝ)|=(5372515003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632604083/5000000000 : ℝ)|^4315 ≤ (8625088027471/20000000000000 : ℝ)^3291
        have hw : |(2632604083/5000000000 : ℝ)|=(2632604083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51477993/250000000 : ℝ)|^4315 ≤ (6296547959023/50000000000000 : ℝ)^3291
        have hw : |(-51477993/250000000 : ℝ)|=(51477993/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_box_7 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4174404969/10000000000 : ℝ)*x 0 + (4401456061/10000000000 : ℝ)*x 1 + (2200728161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4174404969/10000000000 : ℝ)^4315 ≤ (1988025645329/6250000000000 : ℝ)^3291 := by
    have hnat : (4174404969 : ℕ)^4315*6250000000000^3291 ≤ 1988025645329^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4174404969 10000000000 1988025645329 6250000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4401456061/10000000000 : ℝ)^4315 ≤ (17047896750047/50000000000000 : ℝ)^3291 := by
    have hnat : (4401456061 : ℕ)^4315*50000000000000^3291 ≤ 17047896750047^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4401456061 10000000000 17047896750047 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2200728161/5000000000 : ℝ)^4315 ≤ (17047898075511/50000000000000 : ℝ)^3291 := by
    have hnat : (2200728161 : ℕ)^4315*50000000000000^3291 ≤ 17047898075511^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200728161 5000000000 17047898075511 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4174404969/10000000000 : ℝ), (4401456061/10000000000 : ℝ), (2200728161/5000000000 : ℝ)] ![(1988025645329/6250000000000 : ℝ), (17047896750047/50000000000000 : ℝ), (17047898075511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4174404969/10000000000 : ℝ)|^4315 ≤ (1988025645329/6250000000000 : ℝ)^3291
        have hw : |(4174404969/10000000000 : ℝ)|=(4174404969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4401456061/10000000000 : ℝ)|^4315 ≤ (17047896750047/50000000000000 : ℝ)^3291
        have hw : |(4401456061/10000000000 : ℝ)|=(4401456061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2200728161/5000000000 : ℝ)|^4315 ≤ (17047898075511/50000000000000 : ℝ)^3291
        have hw : |(2200728161/5000000000 : ℝ)|=(2200728161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_box_8 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-33302287/156250000 : ℝ)*x 0 + (323728341/625000000 : ℝ)*x 1 + (5403408343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33302287/156250000 : ℝ)^4315 ≤ (205865546887/1562500000000 : ℝ)^3291 := by
    have hnat : (33302287 : ℕ)^4315*1562500000000^3291 ≤ 205865546887^3291*156250000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33302287 156250000 205865546887 1562500000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323728341/625000000 : ℝ)^4315 ≤ (21104492267151/50000000000000 : ℝ)^3291 := by
    have hnat : (323728341 : ℕ)^4315*50000000000000^3291 ≤ 21104492267151^3291*625000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323728341 625000000 21104492267151 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403408343/10000000000 : ℝ)^4315 ≤ (44615620456751/100000000000000 : ℝ)^3291 := by
    have hnat : (5403408343 : ℕ)^4315*100000000000000^3291 ≤ 44615620456751^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403408343 10000000000 44615620456751 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33302287/156250000 : ℝ), (323728341/625000000 : ℝ), (5403408343/10000000000 : ℝ)] ![(205865546887/1562500000000 : ℝ), (21104492267151/50000000000000 : ℝ), (44615620456751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33302287/156250000 : ℝ)|^4315 ≤ (205865546887/1562500000000 : ℝ)^3291
        have hw : |(-33302287/156250000 : ℝ)|=(33302287/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323728341/625000000 : ℝ)|^4315 ≤ (21104492267151/50000000000000 : ℝ)^3291
        have hw : |(323728341/625000000 : ℝ)|=(323728341/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403408343/10000000000 : ℝ)|^4315 ≤ (44615620456751/100000000000000 : ℝ)^3291
        have hw : |(5403408343/10000000000 : ℝ)|=(5403408343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_box_9 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637747091/5000000000 : ℝ)*x 0 + (-400686489/2000000000 : ℝ)*x 1 + (67542599/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637747091/5000000000 : ℝ)^4315 ≤ (43235937019433/100000000000000 : ℝ)^3291 := by
    have hnat : (2637747091 : ℕ)^4315*100000000000000^3291 ≤ 43235937019433^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637747091 5000000000 43235937019433 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (400686489/2000000000 : ℝ)^4315 ≤ (12148447087697/100000000000000 : ℝ)^3291 := by
    have hnat : (400686489 : ℕ)^4315*100000000000000^3291 ≤ 12148447087697^3291*2000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400686489 2000000000 12148447087697 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67542599/125000000 : ℝ)^4315 ≤ (4461561587731/10000000000000 : ℝ)^3291 := by
    have hnat : (67542599 : ℕ)^4315*10000000000000^3291 ≤ 4461561587731^3291*125000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67542599 125000000 4461561587731 10000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637747091/5000000000 : ℝ), (-400686489/2000000000 : ℝ), (67542599/125000000 : ℝ)] ![(43235937019433/100000000000000 : ℝ), (12148447087697/100000000000000 : ℝ), (4461561587731/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637747091/5000000000 : ℝ)|^4315 ≤ (43235937019433/100000000000000 : ℝ)^3291
        have hw : |(2637747091/5000000000 : ℝ)|=(2637747091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-400686489/2000000000 : ℝ)|^4315 ≤ (12148447087697/100000000000000 : ℝ)^3291
        have hw : |(-400686489/2000000000 : ℝ)|=(400686489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67542599/125000000 : ℝ)|^4315 ≤ (4461561587731/10000000000000 : ℝ)^3291
        have hw : |(67542599/125000000 : ℝ)|=(67542599/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_box_10 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275493809/10000000000 : ℝ)*x 0 + (5403408283/10000000000 : ℝ)*x 1 + (-400686491/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275493809/10000000000 : ℝ)^4315 ≤ (43235933011287/100000000000000 : ℝ)^3291 := by
    have hnat : (5275493809 : ℕ)^4315*100000000000000^3291 ≤ 43235933011287^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275493809 10000000000 43235933011287 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403408283/10000000000 : ℝ)^4315 ≤ (8923123961437/20000000000000 : ℝ)^3291 := by
    have hnat : (5403408283 : ℕ)^4315*20000000000000^3291 ≤ 8923123961437^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403408283 10000000000 8923123961437 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (400686491/2000000000 : ℝ)^4315 ≤ (12148447167203/100000000000000 : ℝ)^3291 := by
    have hnat : (400686491 : ℕ)^4315*100000000000000^3291 ≤ 12148447167203^3291*2000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400686491 2000000000 12148447167203 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275493809/10000000000 : ℝ), (5403408283/10000000000 : ℝ), (-400686491/2000000000 : ℝ)] ![(43235933011287/100000000000000 : ℝ), (8923123961437/20000000000000 : ℝ), (12148447167203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275493809/10000000000 : ℝ)|^4315 ≤ (43235933011287/100000000000000 : ℝ)^3291
        have hw : |(5275493809/10000000000 : ℝ)|=(5275493809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403408283/10000000000 : ℝ)|^4315 ≤ (8923123961437/20000000000000 : ℝ)^3291
        have hw : |(5403408283/10000000000 : ℝ)|=(5403408283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-400686491/2000000000 : ℝ)|^4315 ≤ (12148447167203/100000000000000 : ℝ)^3291
        have hw : |(-400686491/2000000000 : ℝ)|=(400686491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_box_11 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2252021283/5000000000 : ℝ)*x 0 + (4236402803/10000000000 : ℝ)*x 1 + (169456141/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2252021283/5000000000 : ℝ)^4315 ≤ (1405660134163/4000000000000 : ℝ)^3291 := by
    have hnat : (2252021283 : ℕ)^4315*4000000000000^3291 ≤ 1405660134163^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252021283 5000000000 1405660134163 4000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4236402803/10000000000 : ℝ)^4315 ≤ (32429244692091/100000000000000 : ℝ)^3291 := by
    have hnat : (4236402803 : ℕ)^4315*100000000000000^3291 ≤ 32429244692091^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236402803 10000000000 32429244692091 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169456141/400000000 : ℝ)^4315 ≤ (6485850387723/20000000000000 : ℝ)^3291 := by
    have hnat : (169456141 : ℕ)^4315*20000000000000^3291 ≤ 6485850387723^3291*400000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169456141 400000000 6485850387723 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2252021283/5000000000 : ℝ), (4236402803/10000000000 : ℝ), (169456141/400000000 : ℝ)] ![(1405660134163/4000000000000 : ℝ), (32429244692091/100000000000000 : ℝ), (6485850387723/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2252021283/5000000000 : ℝ)|^4315 ≤ (1405660134163/4000000000000 : ℝ)^3291
        have hw : |(2252021283/5000000000 : ℝ)|=(2252021283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4236402803/10000000000 : ℝ)|^4315 ≤ (32429244692091/100000000000000 : ℝ)^3291
        have hw : |(4236402803/10000000000 : ℝ)|=(4236402803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169456141/400000000 : ℝ)|^4315 ≤ (6485850387723/20000000000000 : ℝ)^3291
        have hw : |(169456141/400000000 : ℝ)|=(169456141/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_box_12 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1937308669/10000000000 : ℝ)*x 0 + (5472772661/10000000000 : ℝ)*x 1 + (2627064329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1937308669/10000000000 : ℝ)^4315 ≤ (2325088949881/20000000000000 : ℝ)^3291 := by
    have hnat : (1937308669 : ℕ)^4315*20000000000000^3291 ≤ 2325088949881^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1937308669 10000000000 2325088949881 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5472772661/10000000000 : ℝ)^4315 ≤ (9073612181261/20000000000000 : ℝ)^3291 := by
    have hnat : (5472772661 : ℕ)^4315*20000000000000^3291 ≤ 9073612181261^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472772661 10000000000 9073612181261 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627064329/5000000000 : ℝ)^4315 ≤ (10751623583917/25000000000000 : ℝ)^3291 := by
    have hnat : (2627064329 : ℕ)^4315*25000000000000^3291 ≤ 10751623583917^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627064329 5000000000 10751623583917 25000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1937308669/10000000000 : ℝ), (5472772661/10000000000 : ℝ), (2627064329/5000000000 : ℝ)] ![(2325088949881/20000000000000 : ℝ), (9073612181261/20000000000000 : ℝ), (10751623583917/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1937308669/10000000000 : ℝ)|^4315 ≤ (2325088949881/20000000000000 : ℝ)^3291
        have hw : |(-1937308669/10000000000 : ℝ)|=(1937308669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5472772661/10000000000 : ℝ)|^4315 ≤ (9073612181261/20000000000000 : ℝ)^3291
        have hw : |(5472772661/10000000000 : ℝ)|=(5472772661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627064329/5000000000 : ℝ)|^4315 ≤ (10751623583917/25000000000000 : ℝ)^3291
        have hw : |(2627064329/5000000000 : ℝ)|=(2627064329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_box_13 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380290841/10000000000 : ℝ)*x 0 + (-2063470417/10000000000 : ℝ)*x 1 + (328383021/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380290841/10000000000 : ℝ)^4315 ≤ (44365514796233/100000000000000 : ℝ)^3291 := by
    have hnat : (5380290841 : ℕ)^4315*100000000000000^3291 ≤ 44365514796233^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380290841 10000000000 44365514796233 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063470417/10000000000 : ℝ)^4315 ≤ (6313997151783/50000000000000 : ℝ)^3291 := by
    have hnat : (2063470417 : ℕ)^4315*50000000000000^3291 ≤ 6313997151783^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063470417 10000000000 6313997151783 50000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328383021/625000000 : ℝ)^4315 ≤ (537581135999/1250000000000 : ℝ)^3291 := by
    have hnat : (328383021 : ℕ)^4315*1250000000000^3291 ≤ 537581135999^3291*625000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328383021 625000000 537581135999 1250000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380290841/10000000000 : ℝ), (-2063470417/10000000000 : ℝ), (328383021/625000000 : ℝ)] ![(44365514796233/100000000000000 : ℝ), (6313997151783/50000000000000 : ℝ), (537581135999/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380290841/10000000000 : ℝ)|^4315 ≤ (44365514796233/100000000000000 : ℝ)^3291
        have hw : |(5380290841/10000000000 : ℝ)|=(5380290841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2063470417/10000000000 : ℝ)|^4315 ≤ (6313997151783/50000000000000 : ℝ)^3291
        have hw : |(-2063470417/10000000000 : ℝ)|=(2063470417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328383021/625000000 : ℝ)|^4315 ≤ (537581135999/1250000000000 : ℝ)^3291
        have hw : |(328383021/625000000 : ℝ)|=(328383021/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_box_14 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168134079/312500000 : ℝ)*x 0 + (5254128793/10000000000 : ℝ)*x 1 + (-2063470227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168134079/312500000 : ℝ)^4315 ≤ (44365511412181/100000000000000 : ℝ)^3291 := by
    have hnat : (168134079 : ℕ)^4315*100000000000000^3291 ≤ 44365511412181^3291*312500000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168134079 312500000 44365511412181 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254128793/10000000000 : ℝ)^4315 ≤ (43006495784507/100000000000000 : ℝ)^3291 := by
    have hnat : (5254128793 : ℕ)^4315*100000000000000^3291 ≤ 43006495784507^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254128793 10000000000 43006495784507 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063470227/10000000000 : ℝ)^4315 ≤ (3156998194753/25000000000000 : ℝ)^3291 := by
    have hnat : (2063470227 : ℕ)^4315*25000000000000^3291 ≤ 3156998194753^3291*10000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063470227 10000000000 3156998194753 25000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168134079/312500000 : ℝ), (5254128793/10000000000 : ℝ), (-2063470227/10000000000 : ℝ)] ![(44365511412181/100000000000000 : ℝ), (43006495784507/100000000000000 : ℝ), (3156998194753/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168134079/312500000 : ℝ)|^4315 ≤ (44365511412181/100000000000000 : ℝ)^3291
        have hw : |(168134079/312500000 : ℝ)|=(168134079/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254128793/10000000000 : ℝ)|^4315 ≤ (43006495784507/100000000000000 : ℝ)^3291
        have hw : |(5254128793/10000000000 : ℝ)|=(5254128793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2063470227/10000000000 : ℝ)|^4315 ≤ (3156998194753/25000000000000 : ℝ)^3291
        have hw : |(-2063470227/10000000000 : ℝ)|=(2063470227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1355_box_15 (p : ℝ) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (518435619/1250000000 : ℝ)*x 0 + (2207338411/5000000000 : ℝ)*x 1 + (2207338313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518435619/1250000000 : ℝ)^4315 ≤ (3942466003881/12500000000000 : ℝ)^3291 := by
    have hnat : (518435619 : ℕ)^4315*12500000000000^3291 ≤ 3942466003881^3291*1250000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518435619 1250000000 3942466003881 12500000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2207338411/5000000000 : ℝ)^4315 ≤ (6846027394231/20000000000000 : ℝ)^3291 := by
    have hnat : (2207338411 : ℕ)^4315*20000000000000^3291 ≤ 6846027394231^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207338411 5000000000 6846027394231 20000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2207338313/5000000000 : ℝ)^4315 ≤ (34230134978561/100000000000000 : ℝ)^3291 := by
    have hnat : (2207338313 : ℕ)^4315*100000000000000^3291 ≤ 34230134978561^3291*5000000000^4315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207338313 5000000000 34230134978561 100000000000000 4315 3291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4315/1024 : ℝ)) 4315 3291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518435619/1250000000 : ℝ), (2207338411/5000000000 : ℝ), (2207338313/5000000000 : ℝ)] ![(3942466003881/12500000000000 : ℝ), (6846027394231/20000000000000 : ℝ), (34230134978561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518435619/1250000000 : ℝ)|^4315 ≤ (3942466003881/12500000000000 : ℝ)^3291
        have hw : |(518435619/1250000000 : ℝ)|=(518435619/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2207338411/5000000000 : ℝ)|^4315 ≤ (6846027394231/20000000000000 : ℝ)^3291
        have hw : |(2207338411/5000000000 : ℝ)|=(2207338411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2207338313/5000000000 : ℝ)|^4315 ≤ (34230134978561/100000000000000 : ℝ)^3291
        have hw : |(2207338313/5000000000 : ℝ)|=(2207338313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1355_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (559/5000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62861/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58967/100000 : ℝ) ∧ (8003/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84403/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7357/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (559/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7357/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (559/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7357/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (559/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7357/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (559/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7357/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (559/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7357/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (559/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (559/5000 : ℝ) ^ (2157/512 : ℝ) ≤ (4899586161841137/50000000000000000000 : ℝ) := by
    have hpowers : (559/5000 : ℝ)^2157 ≤ (4899586161841137/50000000000000000000 : ℝ)^512 := by
      have hnat : (559 : ℕ)^2157*50000000000000000000^512 ≤ 4899586161841137^512*5000^2157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        559 5000 4899586161841137 50000000000000000000 2157 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (559/5000 : ℝ)) (X := (4899586161841137/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7357/50000 : ℝ) ^ (2157/512 : ℝ) ≤ (15585139385031127/50000000000000000000 : ℝ) := by
    have hpowers : (7357/50000 : ℝ)^2157 ≤ (15585139385031127/50000000000000000000 : ℝ)^512 := by
      have hnat : (7357 : ℕ)^2157*50000000000000000000^512 ≤ 15585139385031127^512*50000^2157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7357 50000 15585139385031127 50000000000000000000 2157 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7357/50000 : ℝ)) (X := (15585139385031127/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004899586161841137/25000000000000000000 : ℝ) ≤ (2000093032940761/2000000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (25004899586161841137/25000000000000000000 : ℝ)^512 ≤ (2000093032940761/2000000000000000 : ℝ)^2157 := by
      have hnat : (25004899586161841137 : ℕ)^512*2000000000000000^2157 ≤ 2000093032940761^2157*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004899586161841137 25000000000000000000 2000093032940761 2000000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000093032940761/2000000000000000 : ℝ)) (X := (25004899586161841137/25000000000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252560590693359033/6250000000000000000 : ℝ) ≤ (10000972326506807/10000000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (6252560590693359033/6250000000000000000 : ℝ)^512 ≤ (10000972326506807/10000000000000000 : ℝ)^2157 := by
      have hnat : (6252560590693359033 : ℕ)^512*10000000000000000^2157 ≤ 10000972326506807^2157*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252560590693359033 6250000000000000000 10000972326506807 10000000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000972326506807/10000000000000000 : ℝ)) (X := (6252560590693359033/6250000000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015585139385031127/25000000000000000000 : ℝ) ≤ (10001479488309809/10000000000000000 : ℝ) ^ (2157/512 : ℝ) := by
    have hpowers : (25015585139385031127/25000000000000000000 : ℝ)^512 ≤ (10001479488309809/10000000000000000 : ℝ)^2157 := by
      have hnat : (25015585139385031127 : ℕ)^512*10000000000000000^2157 ≤ 10001479488309809^2157*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015585139385031127 25000000000000000000 10001479488309809 10000000000000000 512 2157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001479488309809/10000000000000000 : ℝ)) (X := (25015585139385031127/25000000000000000000 : ℝ)) (by norm_num) 2157 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4899586161841137/50000000000000000000 : ℝ) ≤ ((235535358360987481/235600000000000000 : ℝ)+2*(84526967167/58900000000000 : ℝ)*(559/5000 : ℝ))^(2157/512 : ℝ) := by
    rw [show (235535358360987481/235600000000000000 : ℝ)+2*(84526967167/58900000000000 : ℝ)*(559/5000 : ℝ)=(2000093032940761/2000000000000000 : ℝ) by norm_num, show 1+2*(4899586161841137/50000000000000000000 : ℝ)=(25004899586161841137/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15585139385031127/50000000000000000000 : ℝ)+(4899586161841137/50000000000000000000 : ℝ) ≤ ((235535358360987481/235600000000000000 : ℝ)+(84526967167/58900000000000 : ℝ)*((7357/50000 : ℝ)+(559/5000 : ℝ)))^(2157/512 : ℝ) := by
    rw [show (235535358360987481/235600000000000000 : ℝ)+(84526967167/58900000000000 : ℝ)*((7357/50000 : ℝ)+(559/5000 : ℝ))=(10000972326506807/10000000000000000 : ℝ) by norm_num, show 1+(15585139385031127/50000000000000000000 : ℝ)+(4899586161841137/50000000000000000000 : ℝ)=(6252560590693359033/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15585139385031127/50000000000000000000 : ℝ) ≤ ((235535358360987481/235600000000000000 : ℝ)+2*(84526967167/58900000000000 : ℝ)*(7357/50000 : ℝ))^(2157/512 : ℝ) := by
    rw [show (235535358360987481/235600000000000000 : ℝ)+2*(84526967167/58900000000000 : ℝ)*(7357/50000 : ℝ)=(10001479488309809/10000000000000000 : ℝ) by norm_num, show 1+2*(15585139385031127/50000000000000000000 : ℝ)=(25015585139385031127/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (235535358360987481/235600000000000000 : ℝ)*(X 1 0+X 2 0)+(84526967167/58900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (559/5000 : ℝ)) (hi := (7357/50000 : ℝ)) (c := (235535358360987481/235600000000000000 : ℝ)) (alpha := (84526967167/58900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (235535358360987481/235600000000000000 : ℝ)*(X 0 1+X 2 1)+(84526967167/58900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (559/5000 : ℝ)) (hi := (7357/50000 : ℝ)) (c := (235535358360987481/235600000000000000 : ℝ)) (alpha := (84526967167/58900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (235535358360987481/235600000000000000 : ℝ)*(X 0 2+X 1 2)+(84526967167/58900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2157/512 : ℝ)) (lo := (559/5000 : ℝ)) (hi := (7357/50000 : ℝ)) (c := (235535358360987481/235600000000000000 : ℝ)) (alpha := (84526967167/58900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1866570907/10000000000 : ℝ)*X 0 0+(5389394061/10000000000 : ℝ)*X 0 1+(1347348681/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285337131/10000000000 : ℝ)*X 1 0+(-200919731/1000000000 : ℝ)*X 1 1+(673674253/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285336953/10000000000 : ℝ)*X 2 0+(5389394219/10000000000 : ℝ)*X 2 1+(-2009197287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1117779779/2500000000 : ℝ)*X 0 0+(531644019/1250000000 : ℝ)*X 0 1+(10632881/25000000 : ℝ)*X 0 2+(1117779779/2500000000 : ℝ)*X 1 0+(531644019/1250000000 : ℝ)*X 1 1+(10632881/25000000 : ℝ)*X 1 2+(1117779779/2500000000 : ℝ)*X 2 0+(531644019/1250000000 : ℝ)*X 2 1+(10632881/25000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2201772197/10000000000 : ℝ)*X 0 0+(5265208119/10000000000 : ℝ)*X 0 1+(5265208069/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2686257367/5000000000 : ℝ)*X 1 0+(-128694989/625000000 : ℝ)*X 1 1+(131630209/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5372515003/10000000000 : ℝ)*X 2 0+(2632604083/5000000000 : ℝ)*X 2 1+(-51477993/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4174404969/10000000000 : ℝ)*X 0 0+(4401456061/10000000000 : ℝ)*X 0 1+(2200728161/5000000000 : ℝ)*X 0 2+(4174404969/10000000000 : ℝ)*X 1 0+(4401456061/10000000000 : ℝ)*X 1 1+(2200728161/5000000000 : ℝ)*X 1 2+(4174404969/10000000000 : ℝ)*X 2 0+(4401456061/10000000000 : ℝ)*X 2 1+(2200728161/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-33302287/156250000 : ℝ)*X 0 0+(323728341/625000000 : ℝ)*X 0 1+(5403408343/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2637747091/5000000000 : ℝ)*X 1 0+(-400686489/2000000000 : ℝ)*X 1 1+(67542599/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275493809/10000000000 : ℝ)*X 2 0+(5403408283/10000000000 : ℝ)*X 2 1+(-400686491/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2252021283/5000000000 : ℝ)*X 0 0+(4236402803/10000000000 : ℝ)*X 0 1+(169456141/400000000 : ℝ)*X 0 2+(2252021283/5000000000 : ℝ)*X 1 0+(4236402803/10000000000 : ℝ)*X 1 1+(169456141/400000000 : ℝ)*X 1 2+(2252021283/5000000000 : ℝ)*X 2 0+(4236402803/10000000000 : ℝ)*X 2 1+(169456141/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1937308669/10000000000 : ℝ)*X 0 0+(5472772661/10000000000 : ℝ)*X 0 1+(2627064329/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5380290841/10000000000 : ℝ)*X 1 0+(-2063470417/10000000000 : ℝ)*X 1 1+(328383021/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((168134079/312500000 : ℝ)*X 2 0+(5254128793/10000000000 : ℝ)*X 2 1+(-2063470227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((518435619/1250000000 : ℝ)*X 0 0+(2207338411/5000000000 : ℝ)*X 0 1+(2207338313/5000000000 : ℝ)*X 0 2+(518435619/1250000000 : ℝ)*X 1 0+(2207338411/5000000000 : ℝ)*X 1 1+(2207338313/5000000000 : ℝ)*X 1 2+(518435619/1250000000 : ℝ)*X 2 0+(2207338411/5000000000 : ℝ)*X 2 1+(2207338313/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1355_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62861/100000 : ℝ) ≤ (-2961874177024821989851807209/4712000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57370747/100000000000000 : ℝ)*(upper0) + (27740491/100000000000000 : ℝ)*(lower1) + (86415277/100000000000000 : ℝ)*(lower2) + (276637/1562500000000 : ℝ)*(lower3) + (2348179878261/80000000000 : ℝ)*(major0) + (2348179878261/80000000000 : ℝ)*(major1) + (2348179878261/80000000000 : ℝ)*(major2) + (1439624851/100000000000000 : ℝ)*(sp3) + (2000324955411951/50000000000000 : ℝ)*(sp4) + (1000138474330987/25000000000000 : ℝ)*(sp5) + (2000290579007473/50000000000000 : ℝ)*(sp6) + (59085970274261/3125000000000 : ℝ)*(sp7) + (19202699991/20000000000000 : ℝ)*(sp13) + (17188202239/25000000000000 : ℝ)*(sp14) + (472688122100301/25000000000000 : ℝ)*(f.failure) + (2000324955411951/50000000000000 : ℝ)*(f.sum) + (33951784849/14725000000000000000000000 : ℝ)*base65 + (20265410017367/3769600000000000000000000000 : ℝ)*base68 + (1064559700439/3769600000000000000000000000 : ℝ)*base70 + (154667787798227/18848000000000000000000000000 : ℝ)*base72 + (438690968643/589000000000000000000000000 : ℝ)*base74 + (297270118152051/18848000000000000000000000000 : ℝ)*base76 + (101624646966861/18848000000000000000000000000 : ℝ)*base77 + (112399473662323/18848000000000000000000000000 : ℝ)*base80 + (452297348641/294500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (27484647/1250000000000000000000 : ℝ)*base89 + (27484647/1250000000000000000000 : ℝ)*base91 + (27484647/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (58967/100000 : ℝ) ≤ (1736637952834486886192783644197/2945000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (481363/6250000000000 : ℝ)*(lower0) + (21627349/25000000000000 : ℝ)*(lower1) + (1386249/5000000000000 : ℝ)*(lower3) + (91475149/100000000000000 : ℝ)*(lower5) + (751090167760507/25000000000000 : ℝ)*(major0) + (751090167760507/25000000000000 : ℝ)*(major1) + (751090167760507/25000000000000 : ℝ)*(major2) + (2026880147517203/50000000000000 : ℝ)*(sp0) + (1013426178900349/25000000000000 : ℝ)*(sp1) + (2026889012083983/50000000000000 : ℝ)*(sp2) + (967639308188897/50000000000000 : ℝ)*(sp3) + (8357986113/100000000000000 : ℝ)*(sp7) + (7330856657/10000000000000 : ℝ)*(sp9) + (17729133559/100000000000000 : ℝ)*(sp12) + (967643487181953/50000000000000 : ℝ)*(f.failure) + (2026889012083983/50000000000000 : ℝ)*(f.sum) + (577776654249/184062500000000000000000000 : ℝ)*base66 + (53120456404948867/5890000000000000000000000000000 : ℝ)*base67 + (42609852088608867/5890000000000000000000000000000 : ℝ)*base69 + (13900422609758867/5890000000000000000000000000000 : ℝ)*base71 + (36631833233919/2945000000000000000000000000 : ℝ)*base74 + (4870359515788867/5890000000000000000000000000000 : ℝ)*base75 + (50950189585778867/5890000000000000000000000000000 : ℝ)*base77 + (6910489152738867/5890000000000000000000000000000 : ℝ)*base79 + (4175289670351/736250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (19611709/2500000000000000000000 : ℝ)*base90 + (19611709/2500000000000000000000 : ℝ)*base92 + (19611709/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (8003/10000 : ℝ) ≤ (94278480924160152954690452373/117800000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82616407/100000000000000 : ℝ)*(upper0) + (36770021/50000000000000 : ℝ)*(upper2) + (34432993/100000000000000 : ℝ)*(lower3) + (2333177/6250000000000 : ℝ)*(lower4) + (33159198869037/1000000000000 : ℝ)*(major0) + (33159198869037/1000000000000 : ℝ)*(major1) + (33159198869037/1000000000000 : ℝ)*(major2) + (453754153/800000000000 : ℝ)*(sp2) + (32135743639/100000000000000 : ℝ)*(sp3) + (5593816093/50000000000000 : ℝ)*(sp4) + (1117292569704877/25000000000000 : ℝ)*(sp8) + (2234590733225847/50000000000000 : ℝ)*(sp9) + (446912474718257/10000000000000 : ℝ)*(sp10) + (1067974308086141/50000000000000 : ℝ)*(sp11) + (26699759398949/1250000000000 : ℝ)*(f.failure) + (2234590733225847/50000000000000 : ℝ)*(f.sum) + (2208999235577/58900000000000000000000000 : ℝ)*base66 + (1420202553631803/235600000000000000000000000000 : ℝ)*base68 + (1529977162875003/235600000000000000000000000000 : ℝ)*base70 + (3379805008924603/235600000000000000000000000000 : ℝ)*base72 + (504052667409/147250000000000000000000000 : ℝ)*base74 + (2285629388786203/235600000000000000000000000000 : ℝ)*base76 + (1462289816037803/235600000000000000000000000000 : ℝ)*base78 + (4131034507578603/235600000000000000000000000000 : ℝ)*base80 + (43873811451/117800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (105103/62500000000000000000 : ℝ)*base89 + (105103/62500000000000000000 : ℝ)*base91 + (105103/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-84403/100000 : ℝ) ≤ (-4971164429775343478289196332309/5890000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50258963/20000000000000 : ℝ)*(lower0) + (189046337/100000000000000 : ℝ)*(lower1) + (5494261/20000000000000 : ℝ)*(lower2) + (31567327/100000000000000 : ℝ)*(lower3) + (2257347/6250000000000 : ℝ)*(lower4) + (1676269207367137/50000000000000 : ℝ)*(major0) + (1676269207367137/50000000000000 : ℝ)*(major1) + (1676269207367137/50000000000000 : ℝ)*(major2) + (27504476171/10000000000000 : ℝ)*(sp5) + (51037726821/50000000000000 : ℝ)*(sp6) + (4573641269390077/100000000000000 : ℝ)*(sp12) + (2286683112314183/50000000000000 : ℝ)*(sp13) + (914707838787287/20000000000000 : ℝ)*(sp14) + (2159568918481259/100000000000000 : ℝ)*(sp15) + (2159568918481259/100000000000000 : ℝ)*(f.failure) + (4573641269390077/100000000000000 : ℝ)*(f.sum) + (208114582545217/2945000000000000000000000000 : ℝ)*base66 + (10740842913772103/11780000000000000000000000000000 : ℝ)*base68 + (90066361672672103/11780000000000000000000000000000 : ℝ)*base70 + (74001583563592103/11780000000000000000000000000000 : ℝ)*base72 + (2734057054131/1472500000000000000000000000 : ℝ)*base74 + (300754599947527897/11780000000000000000000000000000 : ℝ)*base75 + (229826806998392103/11780000000000000000000000000000 : ℝ)*base78 + (5658935824827897/11780000000000000000000000000000 : ℝ)*base79 + (10515313752047/2945000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (32828673/5000000000000000000000 : ℝ)*base89 + (32828673/5000000000000000000000 : ℝ)*base91 + (32828673/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1355_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (559/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62861/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58967/100000 : ℝ) else (8003/10000 : ℝ) ≤ X j i ∧ X j i ≤ (84403/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1355_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1355_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (559/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62861/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58967/100000 : ℝ) else (8003/10000 : ℝ) ≤ X j i ∧ X j i ≤ (84403/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1355_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2157/512 : ℝ) ≤ p) (hpb : p ≤ (4315/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77620547/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (559/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62861/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58967/100000 : ℝ) else (8003/10000 : ℝ) ≤ X j i ∧ X j i ≤ (84403/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1355_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
