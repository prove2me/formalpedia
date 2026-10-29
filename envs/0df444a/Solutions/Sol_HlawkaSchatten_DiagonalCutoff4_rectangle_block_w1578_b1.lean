-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1578_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:29:50.341989+00:00
-- url     : https://prove2.me/submissions/511c7de5-87cc-4e27-bfce-92b911b2e887

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
theorem support_rectangle_w1578_s3_0 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1774516017/10000000000 : ℝ)*x 0 + (1356575043/2500000000 : ℝ)*x 1 + (1304738353/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1774516017/10000000000 : ℝ)^4653 ≤ (5447055006953/50000000000000 : ℝ)^3629 := by
    have hnat : (1774516017 : ℕ)^4653*50000000000000^3629 ≤ 5447055006953^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1774516017 10000000000 5447055006953 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356575043/2500000000 : ℝ)^4653 ≤ (45665517622099/100000000000000 : ℝ)^3629 := by
    have hnat : (1356575043 : ℕ)^4653*100000000000000^3629 ≤ 45665517622099^3629*2500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356575043 2500000000 45665517622099 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304738353/2500000000 : ℝ)^4653 ≤ (8688074469563/20000000000000 : ℝ)^3629 := by
    have hnat : (1304738353 : ℕ)^4653*20000000000000^3629 ≤ 8688074469563^3629*2500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304738353 2500000000 8688074469563 20000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1774516017/10000000000 : ℝ), (1356575043/2500000000 : ℝ), (1304738353/2500000000 : ℝ)] ![(5447055006953/50000000000000 : ℝ), (45665517622099/100000000000000 : ℝ), (8688074469563/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1774516017/10000000000 : ℝ)|^4653 ≤ (5447055006953/50000000000000 : ℝ)^3629
        have hw : |(-1774516017/10000000000 : ℝ)|=(1774516017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356575043/2500000000 : ℝ)|^4653 ≤ (45665517622099/100000000000000 : ℝ)^3629
        have hw : |(1356575043/2500000000 : ℝ)|=(1356575043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304738353/2500000000 : ℝ)|^4653 ≤ (8688074469563/20000000000000 : ℝ)^3629
        have hw : |(1304738353/2500000000 : ℝ)|=(1304738353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s3_1 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348100843/10000000000 : ℝ)*x 0 + (-75224407/400000000 : ℝ)*x 1 + (1304738353/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348100843/10000000000 : ℝ)^4653 ≤ (44823450520363/100000000000000 : ℝ)^3629 := by
    have hnat : (5348100843 : ℕ)^4653*100000000000000^3629 ≤ 44823450520363^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348100843 10000000000 44823450520363 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75224407/400000000 : ℝ)^4653 ≤ (1173617711109/10000000000000 : ℝ)^3629 := by
    have hnat : (75224407 : ℕ)^4653*10000000000000^3629 ≤ 1173617711109^3629*400000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75224407 400000000 1173617711109 10000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304738353/2500000000 : ℝ)^4653 ≤ (8688074469563/20000000000000 : ℝ)^3629 := by
    have hnat : (1304738353 : ℕ)^4653*20000000000000^3629 ≤ 8688074469563^3629*2500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304738353 2500000000 8688074469563 20000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348100843/10000000000 : ℝ), (-75224407/400000000 : ℝ), (1304738353/2500000000 : ℝ)] ![(44823450520363/100000000000000 : ℝ), (1173617711109/10000000000000 : ℝ), (8688074469563/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348100843/10000000000 : ℝ)|^4653 ≤ (44823450520363/100000000000000 : ℝ)^3629
        have hw : |(5348100843/10000000000 : ℝ)|=(5348100843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-75224407/400000000 : ℝ)|^4653 ≤ (1173617711109/10000000000000 : ℝ)^3629
        have hw : |(-75224407/400000000 : ℝ)|=(75224407/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304738353/2500000000 : ℝ)|^4653 ≤ (8688074469563/20000000000000 : ℝ)^3629
        have hw : |(1304738353/2500000000 : ℝ)|=(1304738353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s3_2 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674050421/5000000000 : ℝ)*x 0 + (5218953413/10000000000 : ℝ)*x 1 + (-14692267/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674050421/5000000000 : ℝ)^4653 ≤ (44823450509617/100000000000000 : ℝ)^3629 := by
    have hnat : (2674050421 : ℕ)^4653*100000000000000^3629 ≤ 44823450509617^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674050421 5000000000 44823450509617 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218953413/10000000000 : ℝ)^4653 ≤ (43440372358487/100000000000000 : ℝ)^3629 := by
    have hnat : (5218953413 : ℕ)^4653*100000000000000^3629 ≤ 43440372358487^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218953413 10000000000 43440372358487 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14692267/78125000 : ℝ)^4653 ≤ (11736177119091/100000000000000 : ℝ)^3629 := by
    have hnat : (14692267 : ℕ)^4653*100000000000000^3629 ≤ 11736177119091^3629*78125000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14692267 78125000 11736177119091 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674050421/5000000000 : ℝ), (5218953413/10000000000 : ℝ), (-14692267/78125000 : ℝ)] ![(44823450509617/100000000000000 : ℝ), (43440372358487/100000000000000 : ℝ), (11736177119091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674050421/5000000000 : ℝ)|^4653 ≤ (44823450509617/100000000000000 : ℝ)^3629
        have hw : |(2674050421/5000000000 : ℝ)|=(2674050421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218953413/10000000000 : ℝ)|^4653 ≤ (43440372358487/100000000000000 : ℝ)^3629
        have hw : |(5218953413/10000000000 : ℝ)|=(5218953413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14692267/78125000 : ℝ)|^4653 ≤ (11736177119091/100000000000000 : ℝ)^3629
        have hw : |(-14692267/78125000 : ℝ)|=(14692267/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s3_3 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529981599/1250000000 : ℝ)*x 0 + (999884151/2500000000 : ℝ)*x 1 + (4491660071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529981599/1250000000 : ℝ)^4653 ≤ (33281265104699/100000000000000 : ℝ)^3629 := by
    have hnat : (529981599 : ℕ)^4653*100000000000000^3629 ≤ 33281265104699^3629*1250000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529981599 1250000000 33281265104699 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999884151/2500000000 : ℝ)^4653 ≤ (7720549267701/25000000000000 : ℝ)^3629 := by
    have hnat : (999884151 : ℕ)^4653*25000000000000^3629 ≤ 7720549267701^3629*2500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999884151 2500000000 7720549267701 25000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491660071/10000000000 : ℝ)^4653 ≤ (8959134451757/25000000000000 : ℝ)^3629 := by
    have hnat : (4491660071 : ℕ)^4653*25000000000000^3629 ≤ 8959134451757^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491660071 10000000000 8959134451757 25000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529981599/1250000000 : ℝ), (999884151/2500000000 : ℝ), (4491660071/10000000000 : ℝ)] ![(33281265104699/100000000000000 : ℝ), (7720549267701/25000000000000 : ℝ), (8959134451757/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529981599/1250000000 : ℝ)|^4653 ≤ (33281265104699/100000000000000 : ℝ)^3629
        have hw : |(529981599/1250000000 : ℝ)|=(529981599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(999884151/2500000000 : ℝ)|^4653 ≤ (7720549267701/25000000000000 : ℝ)^3629
        have hw : |(999884151/2500000000 : ℝ)|=(999884151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491660071/10000000000 : ℝ)|^4653 ≤ (8959134451757/25000000000000 : ℝ)^3629
        have hw : |(4491660071/10000000000 : ℝ)|=(4491660071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s3_4 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-887271997/5000000000 : ℝ)*x 0 + (522005017/1000000000 : ℝ)*x 1 + (1356298733/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (887271997/5000000000 : ℝ)^4653 ≤ (10894330235563/100000000000000 : ℝ)^3629 := by
    have hnat : (887271997 : ℕ)^4653*100000000000000^3629 ≤ 10894330235563^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887271997 5000000000 10894330235563 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522005017/1000000000 : ℝ)^4653 ≤ (43452077576149/100000000000000 : ℝ)^3629 := by
    have hnat : (522005017 : ℕ)^4653*100000000000000^3629 ≤ 43452077576149^3629*1000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522005017 1000000000 43452077576149 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356298733/2500000000 : ℝ)^4653 ≤ (11413398043079/25000000000000 : ℝ)^3629 := by
    have hnat : (1356298733 : ℕ)^4653*25000000000000^3629 ≤ 11413398043079^3629*2500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356298733 2500000000 11413398043079 25000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-887271997/5000000000 : ℝ), (522005017/1000000000 : ℝ), (1356298733/2500000000 : ℝ)] ![(10894330235563/100000000000000 : ℝ), (43452077576149/100000000000000 : ℝ), (11413398043079/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-887271997/5000000000 : ℝ)|^4653 ≤ (10894330235563/100000000000000 : ℝ)^3629
        have hw : |(-887271997/5000000000 : ℝ)|=(887271997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522005017/1000000000 : ℝ)|^4653 ≤ (43452077576149/100000000000000 : ℝ)^3629
        have hw : |(522005017/1000000000 : ℝ)|=(522005017/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356298733/2500000000 : ℝ)|^4653 ≤ (11413398043079/25000000000000 : ℝ)^3629
        have hw : |(1356298733/2500000000 : ℝ)|=(1356298733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s3_5 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293191531/10000000000 : ℝ)*x 0 + (-1674368737/10000000000 : ℝ)*x 1 + (135629871/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293191531/10000000000 : ℝ)^4653 ≤ (11058561292319/25000000000000 : ℝ)^3629 := by
    have hnat : (5293191531 : ℕ)^4653*25000000000000^3629 ≤ 11058561292319^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293191531 10000000000 11058561292319 25000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1674368737/10000000000 : ℝ)^4653 ≤ (2528040909303/25000000000000 : ℝ)^3629 := by
    have hnat : (1674368737 : ℕ)^4653*25000000000000^3629 ≤ 2528040909303^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674368737 10000000000 2528040909303 25000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135629871/250000000 : ℝ)^4653 ≤ (5706698897459/12500000000000 : ℝ)^3629 := by
    have hnat : (135629871 : ℕ)^4653*12500000000000^3629 ≤ 5706698897459^3629*250000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135629871 250000000 5706698897459 12500000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293191531/10000000000 : ℝ), (-1674368737/10000000000 : ℝ), (135629871/250000000 : ℝ)] ![(11058561292319/25000000000000 : ℝ), (2528040909303/25000000000000 : ℝ), (5706698897459/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293191531/10000000000 : ℝ)|^4653 ≤ (11058561292319/25000000000000 : ℝ)^3629
        have hw : |(5293191531/10000000000 : ℝ)|=(5293191531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1674368737/10000000000 : ℝ)|^4653 ≤ (2528040909303/25000000000000 : ℝ)^3629
        have hw : |(-1674368737/10000000000 : ℝ)|=(1674368737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135629871/250000000 : ℝ)|^4653 ≤ (5706698897459/12500000000000 : ℝ)^3629
        have hw : |(135629871/250000000 : ℝ)|=(135629871/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s3_6 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293191671/10000000000 : ℝ)*x 0 + (2712597561/5000000000 : ℝ)*x 1 + (-1674368151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293191671/10000000000 : ℝ)^4653 ≤ (22117123334679/50000000000000 : ℝ)^3629 := by
    have hnat : (5293191671 : ℕ)^4653*50000000000000^3629 ≤ 22117123334679^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293191671 10000000000 22117123334679 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712597561/5000000000 : ℝ)^4653 ≤ (22826797111171/50000000000000 : ℝ)^3629 := by
    have hnat : (2712597561 : ℕ)^4653*50000000000000^3629 ≤ 22826797111171^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712597561 5000000000 22826797111171 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1674368151/10000000000 : ℝ)^4653 ≤ (10112159099503/100000000000000 : ℝ)^3629 := by
    have hnat : (1674368151 : ℕ)^4653*100000000000000^3629 ≤ 10112159099503^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674368151 10000000000 10112159099503 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293191671/10000000000 : ℝ), (2712597561/5000000000 : ℝ), (-1674368151/10000000000 : ℝ)] ![(22117123334679/50000000000000 : ℝ), (22826797111171/50000000000000 : ℝ), (10112159099503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293191671/10000000000 : ℝ)|^4653 ≤ (22117123334679/50000000000000 : ℝ)^3629
        have hw : |(5293191671/10000000000 : ℝ)|=(5293191671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712597561/5000000000 : ℝ)|^4653 ≤ (22826797111171/50000000000000 : ℝ)^3629
        have hw : |(2712597561/5000000000 : ℝ)|=(2712597561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1674368151/10000000000 : ℝ)|^4653 ≤ (10112159099503/100000000000000 : ℝ)^3629
        have hw : |(-1674368151/10000000000 : ℝ)|=(1674368151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s3_7 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4239917869/10000000000 : ℝ)*x 0 + (4489056187/10000000000 : ℝ)*x 1 + (4002160541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4239917869/10000000000 : ℝ)^4653 ≤ (33281920078001/100000000000000 : ℝ)^3629 := by
    have hnat : (4239917869 : ℕ)^4653*100000000000000^3629 ≤ 33281920078001^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239917869 10000000000 33281920078001 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4489056187/10000000000 : ℝ)^4653 ≤ (17904951444813/50000000000000 : ℝ)^3629 := by
    have hnat : (4489056187 : ℕ)^4653*50000000000000^3629 ≤ 17904951444813^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489056187 10000000000 17904951444813 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4002160541/10000000000 : ℝ)^4653 ≤ (30908177013721/100000000000000 : ℝ)^3629 := by
    have hnat : (4002160541 : ℕ)^4653*100000000000000^3629 ≤ 30908177013721^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4002160541 10000000000 30908177013721 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4239917869/10000000000 : ℝ), (4489056187/10000000000 : ℝ), (4002160541/10000000000 : ℝ)] ![(33281920078001/100000000000000 : ℝ), (17904951444813/50000000000000 : ℝ), (30908177013721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4239917869/10000000000 : ℝ)|^4653 ≤ (33281920078001/100000000000000 : ℝ)^3629
        have hw : |(4239917869/10000000000 : ℝ)|=(4239917869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4489056187/10000000000 : ℝ)|^4653 ≤ (17904951444813/50000000000000 : ℝ)^3629
        have hw : |(4489056187/10000000000 : ℝ)|=(4489056187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4002160541/10000000000 : ℝ)|^4653 ≤ (30908177013721/100000000000000 : ℝ)^3629
        have hw : |(4002160541/10000000000 : ℝ)|=(4002160541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1578_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168671607/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15791/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (679/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5559/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3879/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15791/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (679/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15791/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (679/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15791/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (679/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15791/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (679/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15791/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (679/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15791/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (679/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (679/6250 : ℝ) ^ (4651/1024 : ℝ) ≤ (4182856901717867/100000000000000000000 : ℝ) := by
    have hpowers : (679/6250 : ℝ)^4651 ≤ (4182856901717867/100000000000000000000 : ℝ)^1024 := by
      have hnat : (679 : ℕ)^4651*100000000000000000000^1024 ≤ 4182856901717867^1024*6250^4651 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        679 6250 4182856901717867 100000000000000000000 4651 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (679/6250 : ℝ)) (X := (4182856901717867/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15791/100000 : ℝ) ^ (4651/1024 : ℝ) ≤ (22865611376265317/100000000000000000000 : ℝ) := by
    have hpowers : (15791/100000 : ℝ)^4651 ≤ (22865611376265317/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15791 : ℕ)^4651*100000000000000000000^1024 ≤ 22865611376265317^1024*100000^4651 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15791 100000 22865611376265317 100000000000000000000 4651 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15791/100000 : ℝ)) (X := (22865611376265317/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004182856901717867/50000000000000000000 : ℝ) ≤ (2500046044998473/2500000000000000 : ℝ) ^ (4651/1024 : ℝ) := by
    have hpowers : (50004182856901717867/50000000000000000000 : ℝ)^1024 ≤ (2500046044998473/2500000000000000 : ℝ)^4651 := by
      have hnat : (50004182856901717867 : ℕ)^1024*2500000000000000^4651 ≤ 2500046044998473^4651*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004182856901717867 50000000000000000000 2500046044998473 2500000000000000 1024 4651 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500046044998473/2500000000000000 : ℝ)) (X := (50004182856901717867/50000000000000000000 : ℝ)) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6251690529267373949/6250000000000000000 : ℝ) ≤ (10000595457123573/10000000000000000 : ℝ) ^ (4651/1024 : ℝ) := by
    have hpowers : (6251690529267373949/6250000000000000000 : ℝ)^1024 ≤ (10000595457123573/10000000000000000 : ℝ)^4651 := by
      have hnat : (6251690529267373949 : ℕ)^1024*10000000000000000^4651 ≤ 10000595457123573^4651*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251690529267373949 6250000000000000000 10000595457123573 10000000000000000 1024 4651 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000595457123573/10000000000000000 : ℝ)) (X := (6251690529267373949/6250000000000000000 : ℝ)) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022865611376265317/50000000000000000000 : ℝ) ≤ (5000503367126627/5000000000000000 : ℝ) ^ (4651/1024 : ℝ) := by
    have hpowers : (50022865611376265317/50000000000000000000 : ℝ)^1024 ≤ (5000503367126627/5000000000000000 : ℝ)^4651 := by
      have hnat : (50022865611376265317 : ℕ)^1024*5000000000000000^4651 ≤ 5000503367126627^4651*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022865611376265317 50000000000000000000 5000503367126627 5000000000000000 1024 4651 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000503367126627/5000000000000000 : ℝ)) (X := (50022865611376265317/50000000000000000000 : ℝ)) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4182856901717867/100000000000000000000 : ℝ) ≤ ((12315492806339049279/12317500000000000000 : ℝ)+2*(411277129681/492700000000000 : ℝ)*(679/6250 : ℝ))^(4651/1024 : ℝ) := by
    rw [show (12315492806339049279/12317500000000000000 : ℝ)+2*(411277129681/492700000000000 : ℝ)*(679/6250 : ℝ)=(2500046044998473/2500000000000000 : ℝ) by norm_num, show 1+2*(4182856901717867/100000000000000000000 : ℝ)=(50004182856901717867/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22865611376265317/100000000000000000000 : ℝ)+(4182856901717867/100000000000000000000 : ℝ) ≤ ((12315492806339049279/12317500000000000000 : ℝ)+(411277129681/492700000000000 : ℝ)*((15791/100000 : ℝ)+(679/6250 : ℝ)))^(4651/1024 : ℝ) := by
    rw [show (12315492806339049279/12317500000000000000 : ℝ)+(411277129681/492700000000000 : ℝ)*((15791/100000 : ℝ)+(679/6250 : ℝ))=(10000595457123573/10000000000000000 : ℝ) by norm_num, show 1+(22865611376265317/100000000000000000000 : ℝ)+(4182856901717867/100000000000000000000 : ℝ)=(6251690529267373949/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22865611376265317/100000000000000000000 : ℝ) ≤ ((12315492806339049279/12317500000000000000 : ℝ)+2*(411277129681/492700000000000 : ℝ)*(15791/100000 : ℝ))^(4651/1024 : ℝ) := by
    rw [show (12315492806339049279/12317500000000000000 : ℝ)+2*(411277129681/492700000000000 : ℝ)*(15791/100000 : ℝ)=(5000503367126627/5000000000000000 : ℝ) by norm_num, show 1+2*(22865611376265317/100000000000000000000 : ℝ)=(50022865611376265317/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12315492806339049279/12317500000000000000 : ℝ)*(X 1 0+X 2 0)+(411277129681/492700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4651/1024 : ℝ)) (lo := (679/6250 : ℝ)) (hi := (15791/100000 : ℝ)) (c := (12315492806339049279/12317500000000000000 : ℝ)) (alpha := (411277129681/492700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12315492806339049279/12317500000000000000 : ℝ)*(X 0 1+X 2 1)+(411277129681/492700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4651/1024 : ℝ)) (lo := (679/6250 : ℝ)) (hi := (15791/100000 : ℝ)) (c := (12315492806339049279/12317500000000000000 : ℝ)) (alpha := (411277129681/492700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12315492806339049279/12317500000000000000 : ℝ)*(X 0 2+X 1 2)+(411277129681/492700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4651/1024 : ℝ)) (lo := (679/6250 : ℝ)) (hi := (15791/100000 : ℝ)) (c := (12315492806339049279/12317500000000000000 : ℝ)) (alpha := (411277129681/492700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1774516017/10000000000 : ℝ)*X 0 0+(1356575043/2500000000 : ℝ)*X 0 1+(1304738353/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348100843/10000000000 : ℝ)*X 1 0+(-75224407/400000000 : ℝ)*X 1 1+(1304738353/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674050421/5000000000 : ℝ)*X 2 0+(5218953413/10000000000 : ℝ)*X 2 1+(-14692267/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((529981599/1250000000 : ℝ)*X 0 0+(999884151/2500000000 : ℝ)*X 0 1+(4491660071/10000000000 : ℝ)*X 0 2+(529981599/1250000000 : ℝ)*X 1 0+(999884151/2500000000 : ℝ)*X 1 1+(4491660071/10000000000 : ℝ)*X 1 2+(529981599/1250000000 : ℝ)*X 2 0+(999884151/2500000000 : ℝ)*X 2 1+(4491660071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-887271997/5000000000 : ℝ)*X 0 0+(522005017/1000000000 : ℝ)*X 0 1+(1356298733/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293191531/10000000000 : ℝ)*X 1 0+(-1674368737/10000000000 : ℝ)*X 1 1+(135629871/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293191671/10000000000 : ℝ)*X 2 0+(2712597561/5000000000 : ℝ)*X 2 1+(-1674368151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4239917869/10000000000 : ℝ)*X 0 0+(4489056187/10000000000 : ℝ)*X 0 1+(4002160541/10000000000 : ℝ)*X 0 2+(4239917869/10000000000 : ℝ)*X 1 0+(4489056187/10000000000 : ℝ)*X 1 1+(4002160541/10000000000 : ℝ)*X 1 2+(4239917869/10000000000 : ℝ)*X 2 0+(4489056187/10000000000 : ℝ)*X 2 1+(4002160541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1433699196415995413026940541/615875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (395207051/100000000000000 : ℝ)*(base19) + (365985549/100000000000000 : ℝ)*(base23) + (3786417/25000000000000 : ℝ)*(lower2) + (5912739/10000000000000 : ℝ)*(upper3) + (7592929/20000000000000 : ℝ)*(upper5) + (3427433821970403/100000000000000 : ℝ)*(major0) + (3427433821970403/100000000000000 : ℝ)*(major1) + (856858455492601/25000000000000 : ℝ)*(major2) + (1205711350477089/25000000000000 : ℝ)*(sp0) + (4822851301405817/100000000000000 : ℝ)*(sp1) + (4822851330627319/100000000000000 : ℝ)*(sp2) + (508003240516053/25000000000000 : ℝ)*(sp3) + (49177379/781250000000 : ℝ)*(sp4) + (2907666847/100000000000000 : ℝ)*(sp7) + (2032015869731059/100000000000000 : ℝ)*(f.failure) + (1205712924153217/25000000000000 : ℝ)*(f.sum) + (388877913681523/49270000000000000000000000000 : ℝ)*base66 + (10083507047213839437/1231750000000000000000000000000000 : ℝ)*base67 + (4944797127771340929/307937500000000000000000000000000 : ℝ)*base69 + (188465175398089437/1231750000000000000000000000000000 : ℝ)*base71 + (1365939170173/49270000000000000000000000000 : ℝ)*base74 + (6105304632996590929/307937500000000000000000000000000 : ℝ)*base75 + (9859715632271185563/1231750000000000000000000000000000 : ℝ)*base78 + (11711840035140564437/1231750000000000000000000000000000 : ℝ)*base79 + (44605662865359/12317500000000000000000000000 : ℝ)*base81 + (79341813/10000000000000000000000 : ℝ)*base89 + (79341813/10000000000000000000000 : ℝ)*base91 + (20658187/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2558097165267280518276962373/307937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (372004747/25000000000000 : ℝ)*(base19) + (2178955153/100000000000000 : ℝ)*(base23) + (44300721/20000000000000 : ℝ)*(upper2) + (11580203/20000000000000 : ℝ)*(upper3) + (176891439/50000000000000 : ℝ)*(upper5) + (3464218768647671/100000000000000 : ℝ)*(major0) + (3464218768647671/100000000000000 : ℝ)*(major1) + (3464218768647671/100000000000000 : ℝ)*(major2) + (5605006217/20000000000000 : ℝ)*(sp1) + (10465515393/25000000000000 : ℝ)*(sp2) + (2437306386260047/50000000000000 : ℝ)*(sp4) + (4874583259470021/100000000000000 : ℝ)*(sp5) + (4874568731503369/100000000000000 : ℝ)*(sp6) + (2053824487868709/100000000000000 : ℝ)*(sp7) + (2053824487868709/100000000000000 : ℝ)*(f.failure) + (2437306386260047/50000000000000 : ℝ)*(f.sum) + (3121047801689/1539687500000000000000000000 : ℝ)*base66 + (8294459674756104209/1231750000000000000000000000000000 : ℝ)*base67 + (4125840002961604209/1231750000000000000000000000000000 : ℝ)*base69 + (770098649350895791/1231750000000000000000000000000000 : ℝ)*base72 + (10460645508633/12317500000000000000000000000 : ℝ)*base73 + (18052325693910604209/1231750000000000000000000000000000 : ℝ)*base75 + (2096200331509354209/1231750000000000000000000000000000 : ℝ)*base77 + (28473240346006604209/1231750000000000000000000000000000 : ℝ)*base79 + (40207417947921/24635000000000000000000000000 : ℝ)*base81 + (52045363/10000000000000000000000 : ℝ)*base89 + (52045363/10000000000000000000000 : ℝ)*base91 + (52045363/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1578_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168671607/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15791/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (679/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5559/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3879/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1578_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1578_s4_0 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-35494413/200000000 : ℝ)*x 0 + (5424920877/10000000000 : ℝ)*x 1 + (5220196929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35494413/200000000 : ℝ)^4653 ≤ (136196510129/1250000000000 : ℝ)^3629 := by
    have hnat : (35494413 : ℕ)^4653*1250000000000^3629 ≤ 136196510129^3629*200000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35494413 200000000 136196510129 1250000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424920877/10000000000 : ℝ)^4653 ≤ (45650635247197/100000000000000 : ℝ)^3629 := by
    have hnat : (5424920877 : ℕ)^4653*100000000000000^3629 ≤ 45650635247197^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424920877 10000000000 45650635247197 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220196929/10000000000 : ℝ)^4653 ≤ (21726821962369/50000000000000 : ℝ)^3629 := by
    have hnat : (5220196929 : ℕ)^4653*50000000000000^3629 ≤ 21726821962369^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220196929 10000000000 21726821962369 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-35494413/200000000 : ℝ), (5424920877/10000000000 : ℝ), (5220196929/10000000000 : ℝ)] ![(136196510129/1250000000000 : ℝ), (45650635247197/100000000000000 : ℝ), (21726821962369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-35494413/200000000 : ℝ)|^4653 ≤ (136196510129/1250000000000 : ℝ)^3629
        have hw : |(-35494413/200000000 : ℝ)|=(35494413/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424920877/10000000000 : ℝ)|^4653 ≤ (45650635247197/100000000000000 : ℝ)^3629
        have hw : |(5424920877/10000000000 : ℝ)|=(5424920877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220196929/10000000000 : ℝ)|^4653 ≤ (21726821962369/50000000000000 : ℝ)^3629
        have hw : |(5220196929/10000000000 : ℝ)|=(5220196929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s4_1 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668466889/1250000000 : ℝ)*x 0 + (-117465163/625000000 : ℝ)*x 1 + (2610098469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668466889/1250000000 : ℝ)^4653 ≤ (22409760184099/50000000000000 : ℝ)^3629 := by
    have hnat : (668466889 : ℕ)^4653*50000000000000^3629 ≤ 22409760184099^3629*1250000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668466889 1250000000 22409760184099 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (117465163/625000000 : ℝ)^4653 ≤ (2345367117473/20000000000000 : ℝ)^3629 := by
    have hnat : (117465163 : ℕ)^4653*20000000000000^3629 ≤ 2345367117473^3629*625000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117465163 625000000 2345367117473 20000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610098469/5000000000 : ℝ)^4653 ≤ (21726822010397/50000000000000 : ℝ)^3629 := by
    have hnat : (2610098469 : ℕ)^4653*50000000000000^3629 ≤ 21726822010397^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610098469 5000000000 21726822010397 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668466889/1250000000 : ℝ), (-117465163/625000000 : ℝ), (2610098469/5000000000 : ℝ)] ![(22409760184099/50000000000000 : ℝ), (2345367117473/20000000000000 : ℝ), (21726822010397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668466889/1250000000 : ℝ)|^4653 ≤ (22409760184099/50000000000000 : ℝ)^3629
        have hw : |(668466889/1250000000 : ℝ)|=(668466889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-117465163/625000000 : ℝ)|^4653 ≤ (2345367117473/20000000000000 : ℝ)^3629
        have hw : |(-117465163/625000000 : ℝ)|=(117465163/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610098469/5000000000 : ℝ)|^4653 ≤ (21726822010397/50000000000000 : ℝ)^3629
        have hw : |(2610098469/5000000000 : ℝ)|=(2610098469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s4_2 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336933779/2500000000 : ℝ)*x 0 + (1044039387/2000000000 : ℝ)*x 1 + (-117465163/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336933779/2500000000 : ℝ)^4653 ≤ (22409760205591/50000000000000 : ℝ)^3629 := by
    have hnat : (1336933779 : ℕ)^4653*50000000000000^3629 ≤ 22409760205591^3629*2500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336933779 2500000000 22409760205591 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044039387/2000000000 : ℝ)^4653 ≤ (5431705498597/12500000000000 : ℝ)^3629 := by
    have hnat : (1044039387 : ℕ)^4653*12500000000000^3629 ≤ 5431705498597^3629*2000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044039387 2000000000 5431705498597 12500000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117465163/625000000 : ℝ)^4653 ≤ (2345367117473/20000000000000 : ℝ)^3629 := by
    have hnat : (117465163 : ℕ)^4653*20000000000000^3629 ≤ 2345367117473^3629*625000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117465163 625000000 2345367117473 20000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336933779/2500000000 : ℝ), (1044039387/2000000000 : ℝ), (-117465163/625000000 : ℝ)] ![(22409760205591/50000000000000 : ℝ), (5431705498597/12500000000000 : ℝ), (2345367117473/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336933779/2500000000 : ℝ)|^4653 ≤ (22409760205591/50000000000000 : ℝ)^3629
        have hw : |(1336933779/2500000000 : ℝ)|=(1336933779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044039387/2000000000 : ℝ)|^4653 ≤ (5431705498597/12500000000000 : ℝ)^3629
        have hw : |(1044039387/2000000000 : ℝ)|=(1044039387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-117465163/625000000 : ℝ)|^4653 ≤ (2345367117473/20000000000000 : ℝ)^3629
        have hw : |(-117465163/625000000 : ℝ)|=(117465163/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s4_3 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4239982731/10000000000 : ℝ)*x 0 + (400263483/1000000000 : ℝ)*x 1 + (561066647/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4239982731/10000000000 : ℝ)^4653 ≤ (16641286445119/50000000000000 : ℝ)^3629 := by
    have hnat : (4239982731 : ℕ)^4653*50000000000000^3629 ≤ 16641286445119^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239982731 10000000000 16641286445119 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (400263483/1000000000 : ℝ)^4653 ≤ (30912873524061/100000000000000 : ℝ)^3629 := by
    have hnat : (400263483 : ℕ)^4653*100000000000000^3629 ≤ 30912873524061^3629*1000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400263483 1000000000 30912873524061 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561066647/1250000000 : ℝ)^4653 ≤ (35804553578347/100000000000000 : ℝ)^3629 := by
    have hnat : (561066647 : ℕ)^4653*100000000000000^3629 ≤ 35804553578347^3629*1250000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561066647 1250000000 35804553578347 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4239982731/10000000000 : ℝ), (400263483/1000000000 : ℝ), (561066647/1250000000 : ℝ)] ![(16641286445119/50000000000000 : ℝ), (30912873524061/100000000000000 : ℝ), (35804553578347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4239982731/10000000000 : ℝ)|^4653 ≤ (16641286445119/50000000000000 : ℝ)^3629
        have hw : |(4239982731/10000000000 : ℝ)|=(4239982731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(400263483/1000000000 : ℝ)|^4653 ≤ (30912873524061/100000000000000 : ℝ)^3629
        have hw : |(400263483/1000000000 : ℝ)|=(400263483/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561066647/1250000000 : ℝ)|^4653 ≤ (35804553578347/100000000000000 : ℝ)^3629
        have hw : |(561066647/1250000000 : ℝ)|=(561066647/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s4_4 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-221843411/1250000000 : ℝ)*x 0 + (261063321/500000000 : ℝ)*x 1 + (5423843437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221843411/1250000000 : ℝ)^4653 ≤ (2179186099761/20000000000000 : ℝ)^3629 := by
    have hnat : (221843411 : ℕ)^4653*20000000000000^3629 ≤ 2179186099761^3629*1250000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221843411 1250000000 2179186099761 20000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261063321/500000000 : ℝ)^4653 ≤ (21732529451457/50000000000000 : ℝ)^3629 := by
    have hnat : (261063321 : ℕ)^4653*50000000000000^3629 ≤ 21732529451457^3629*500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261063321 500000000 21732529451457 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423843437/10000000000 : ℝ)^4653 ≤ (45639010582741/100000000000000 : ℝ)^3629 := by
    have hnat : (5423843437 : ℕ)^4653*100000000000000^3629 ≤ 45639010582741^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423843437 10000000000 45639010582741 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-221843411/1250000000 : ℝ), (261063321/500000000 : ℝ), (5423843437/10000000000 : ℝ)] ![(2179186099761/20000000000000 : ℝ), (21732529451457/50000000000000 : ℝ), (45639010582741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-221843411/1250000000 : ℝ)|^4653 ≤ (2179186099761/20000000000000 : ℝ)^3629
        have hw : |(-221843411/1250000000 : ℝ)|=(221843411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261063321/500000000 : ℝ)|^4653 ≤ (21732529451457/50000000000000 : ℝ)^3629
        have hw : |(261063321/500000000 : ℝ)|=(261063321/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423843437/10000000000 : ℝ)|^4653 ≤ (45639010582741/100000000000000 : ℝ)^3629
        have hw : |(5423843437/10000000000 : ℝ)|=(5423843437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s4_5 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646760351/5000000000 : ℝ)*x 0 + (-33515923/200000000 : ℝ)*x 1 + (338990209/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646760351/5000000000 : ℝ)^4653 ≤ (8847554445247/20000000000000 : ℝ)^3629 := by
    have hnat : (2646760351 : ℕ)^4653*20000000000000^3629 ≤ 8847554445247^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646760351 5000000000 8847554445247 20000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33515923/200000000 : ℝ)^4653 ≤ (10123218183847/100000000000000 : ℝ)^3629 := by
    have hnat : (33515923 : ℕ)^4653*100000000000000^3629 ≤ 10123218183847^3629*200000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33515923 200000000 10123218183847 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338990209/625000000 : ℝ)^4653 ≤ (22819504789689/50000000000000 : ℝ)^3629 := by
    have hnat : (338990209 : ℕ)^4653*50000000000000^3629 ≤ 22819504789689^3629*625000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338990209 625000000 22819504789689 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646760351/5000000000 : ℝ), (-33515923/200000000 : ℝ), (338990209/625000000 : ℝ)] ![(8847554445247/20000000000000 : ℝ), (10123218183847/100000000000000 : ℝ), (22819504789689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646760351/5000000000 : ℝ)|^4653 ≤ (8847554445247/20000000000000 : ℝ)^3629
        have hw : |(2646760351/5000000000 : ℝ)|=(2646760351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-33515923/200000000 : ℝ)|^4653 ≤ (10123218183847/100000000000000 : ℝ)^3629
        have hw : |(-33515923/200000000 : ℝ)|=(33515923/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338990209/625000000 : ℝ)|^4653 ≤ (22819504789689/50000000000000 : ℝ)^3629
        have hw : |(338990209/625000000 : ℝ)|=(338990209/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s4_6 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058704151/2000000000 : ℝ)*x 0 + (5423843267/10000000000 : ℝ)*x 1 + (-1675796183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058704151/2000000000 : ℝ)^4653 ≤ (44237772794133/100000000000000 : ℝ)^3629 := by
    have hnat : (1058704151 : ℕ)^4653*100000000000000^3629 ≤ 44237772794133^3629*2000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058704151 2000000000 44237772794133 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423843267/10000000000 : ℝ)^4653 ≤ (45639008748637/100000000000000 : ℝ)^3629 := by
    have hnat : (5423843267 : ℕ)^4653*100000000000000^3629 ≤ 45639008748637^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423843267 10000000000 45639008748637 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1675796183/10000000000 : ℝ)^4653 ≤ (2024643687889/20000000000000 : ℝ)^3629 := by
    have hnat : (1675796183 : ℕ)^4653*20000000000000^3629 ≤ 2024643687889^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1675796183 10000000000 2024643687889 20000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058704151/2000000000 : ℝ), (5423843267/10000000000 : ℝ), (-1675796183/10000000000 : ℝ)] ![(44237772794133/100000000000000 : ℝ), (45639008748637/100000000000000 : ℝ), (2024643687889/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058704151/2000000000 : ℝ)|^4653 ≤ (44237772794133/100000000000000 : ℝ)^3629
        have hw : |(1058704151/2000000000 : ℝ)|=(1058704151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423843267/10000000000 : ℝ)|^4653 ≤ (45639008748637/100000000000000 : ℝ)^3629
        have hw : |(5423843267/10000000000 : ℝ)|=(5423843267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1675796183/10000000000 : ℝ)|^4653 ≤ (2024643687889/20000000000000 : ℝ)^3629
        have hw : |(-1675796183/10000000000 : ℝ)|=(1675796183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s4_7 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4240045799/10000000000 : ℝ)*x 0 + (4485994769/10000000000 : ℝ)*x 1 + (40051921/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4240045799/10000000000 : ℝ)^4653 ≤ (16641603824613/50000000000000 : ℝ)^3629 := by
    have hnat : (4240045799 : ℕ)^4653*50000000000000^3629 ≤ 16641603824613^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240045799 10000000000 16641603824613 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4485994769/10000000000 : ℝ)^4653 ≤ (286228747757/800000000000 : ℝ)^3629 := by
    have hnat : (4485994769 : ℕ)^4653*800000000000^3629 ≤ 286228747757^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485994769 10000000000 286228747757 800000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40051921/100000000 : ℝ)^4653 ≤ (30938198859957/100000000000000 : ℝ)^3629 := by
    have hnat : (40051921 : ℕ)^4653*100000000000000^3629 ≤ 30938198859957^3629*100000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40051921 100000000 30938198859957 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4240045799/10000000000 : ℝ), (4485994769/10000000000 : ℝ), (40051921/100000000 : ℝ)] ![(16641603824613/50000000000000 : ℝ), (286228747757/800000000000 : ℝ), (30938198859957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4240045799/10000000000 : ℝ)|^4653 ≤ (16641603824613/50000000000000 : ℝ)^3629
        have hw : |(4240045799/10000000000 : ℝ)|=(4240045799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4485994769/10000000000 : ℝ)|^4653 ≤ (286228747757/800000000000 : ℝ)^3629
        have hw : |(4485994769/10000000000 : ℝ)|=(4485994769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40051921/100000000 : ℝ)|^4653 ≤ (30938198859957/100000000000000 : ℝ)^3629
        have hw : |(40051921/100000000 : ℝ)|=(40051921/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1578_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168671607/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3879/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5559/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1393/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15487/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3879/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5559/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3879/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5559/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3879/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5559/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3879/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5559/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3879/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5559/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3879/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5559/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5559/50000 : ℝ) ^ (4651/1024 : ℝ) ≤ (1161450206080211/25000000000000000000 : ℝ) := by
    have hpowers : (5559/50000 : ℝ)^4651 ≤ (1161450206080211/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5559 : ℕ)^4651*25000000000000000000^1024 ≤ 1161450206080211^1024*50000^4651 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5559 50000 1161450206080211 25000000000000000000 4651 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5559/50000 : ℝ)) (X := (1161450206080211/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3879/25000 : ℝ) ^ (4651/1024 : ℝ) ≤ (659747971016109/3125000000000000000 : ℝ) := by
    have hpowers : (3879/25000 : ℝ)^4651 ≤ (659747971016109/3125000000000000000 : ℝ)^1024 := by
      have hnat : (3879 : ℕ)^4651*3125000000000000000^1024 ≤ 659747971016109^1024*25000^4651 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3879 25000 659747971016109 3125000000000000000 4651 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3879/25000 : ℝ)) (X := (659747971016109/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501161450206080211/12500000000000000000 : ℝ) ≤ (2000040912730159/2000000000000000 : ℝ) ^ (4651/1024 : ℝ) := by
    have hpowers : (12501161450206080211/12500000000000000000 : ℝ)^1024 ≤ (2000040912730159/2000000000000000 : ℝ)^4651 := by
      have hnat : (12501161450206080211 : ℕ)^1024*2000000000000000^4651 ≤ 2000040912730159^4651*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501161450206080211 12500000000000000000 2000040912730159 2000000000000000 1024 4651 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000040912730159/2000000000000000 : ℝ)) (X := (12501161450206080211/12500000000000000000 : ℝ)) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25006439433974209083/25000000000000000000 : ℝ) ≤ (312517720162959/312500000000000 : ℝ) ^ (4651/1024 : ℝ) := by
    have hpowers : (25006439433974209083/25000000000000000000 : ℝ)^1024 ≤ (312517720162959/312500000000000 : ℝ)^4651 := by
      have hnat : (25006439433974209083 : ℕ)^1024*312500000000000^4651 ≤ 312517720162959^4651*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006439433974209083 25000000000000000000 312517720162959 312500000000000 1024 4651 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312517720162959/312500000000000 : ℝ)) (X := (25006439433974209083/25000000000000000000 : ℝ)) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563159747971016109/1562500000000000000 : ℝ) ≤ (10000929526778581/10000000000000000 : ℝ) ^ (4651/1024 : ℝ) := by
    have hpowers : (1563159747971016109/1562500000000000000 : ℝ)^1024 ≤ (10000929526778581/10000000000000000 : ℝ)^4651 := by
      have hnat : (1563159747971016109 : ℕ)^1024*10000000000000000^4651 ≤ 10000929526778581^4651*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563159747971016109 1562500000000000000 10000929526778581 10000000000000000 1024 4651 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000929526778581/10000000000000000 : ℝ)) (X := (1563159747971016109/1562500000000000000 : ℝ)) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1161450206080211/25000000000000000000 : ℝ) ≤ ((7328806588480245277/7330000000000000000 : ℝ)+2*(362481563893/439800000000000 : ℝ)*(5559/50000 : ℝ))^(4651/1024 : ℝ) := by
    rw [show (7328806588480245277/7330000000000000000 : ℝ)+2*(362481563893/439800000000000 : ℝ)*(5559/50000 : ℝ)=(2000040912730159/2000000000000000 : ℝ) by norm_num, show 1+2*(1161450206080211/25000000000000000000 : ℝ)=(12501161450206080211/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(659747971016109/3125000000000000000 : ℝ)+(1161450206080211/25000000000000000000 : ℝ) ≤ ((7328806588480245277/7330000000000000000 : ℝ)+(362481563893/439800000000000 : ℝ)*((3879/25000 : ℝ)+(5559/50000 : ℝ)))^(4651/1024 : ℝ) := by
    rw [show (7328806588480245277/7330000000000000000 : ℝ)+(362481563893/439800000000000 : ℝ)*((3879/25000 : ℝ)+(5559/50000 : ℝ))=(312517720162959/312500000000000 : ℝ) by norm_num, show 1+(659747971016109/3125000000000000000 : ℝ)+(1161450206080211/25000000000000000000 : ℝ)=(25006439433974209083/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(659747971016109/3125000000000000000 : ℝ) ≤ ((7328806588480245277/7330000000000000000 : ℝ)+2*(362481563893/439800000000000 : ℝ)*(3879/25000 : ℝ))^(4651/1024 : ℝ) := by
    rw [show (7328806588480245277/7330000000000000000 : ℝ)+2*(362481563893/439800000000000 : ℝ)*(3879/25000 : ℝ)=(10000929526778581/10000000000000000 : ℝ) by norm_num, show 1+2*(659747971016109/3125000000000000000 : ℝ)=(1563159747971016109/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7328806588480245277/7330000000000000000 : ℝ)*(X 1 0+X 2 0)+(362481563893/439800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4651/1024 : ℝ)) (lo := (5559/50000 : ℝ)) (hi := (3879/25000 : ℝ)) (c := (7328806588480245277/7330000000000000000 : ℝ)) (alpha := (362481563893/439800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7328806588480245277/7330000000000000000 : ℝ)*(X 0 1+X 2 1)+(362481563893/439800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4651/1024 : ℝ)) (lo := (5559/50000 : ℝ)) (hi := (3879/25000 : ℝ)) (c := (7328806588480245277/7330000000000000000 : ℝ)) (alpha := (362481563893/439800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7328806588480245277/7330000000000000000 : ℝ)*(X 0 2+X 1 2)+(362481563893/439800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4651/1024 : ℝ)) (lo := (5559/50000 : ℝ)) (hi := (3879/25000 : ℝ)) (c := (7328806588480245277/7330000000000000000 : ℝ)) (alpha := (362481563893/439800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-35494413/200000000 : ℝ)*X 0 0+(5424920877/10000000000 : ℝ)*X 0 1+(5220196929/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668466889/1250000000 : ℝ)*X 1 0+(-117465163/625000000 : ℝ)*X 1 1+(2610098469/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336933779/2500000000 : ℝ)*X 2 0+(1044039387/2000000000 : ℝ)*X 2 1+(-117465163/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4239982731/10000000000 : ℝ)*X 0 0+(400263483/1000000000 : ℝ)*X 0 1+(561066647/1250000000 : ℝ)*X 0 2+(4239982731/10000000000 : ℝ)*X 1 0+(400263483/1000000000 : ℝ)*X 1 1+(561066647/1250000000 : ℝ)*X 1 2+(4239982731/10000000000 : ℝ)*X 2 0+(400263483/1000000000 : ℝ)*X 2 1+(561066647/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-221843411/1250000000 : ℝ)*X 0 0+(261063321/500000000 : ℝ)*X 0 1+(5423843437/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646760351/5000000000 : ℝ)*X 1 0+(-33515923/200000000 : ℝ)*X 1 1+(338990209/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058704151/2000000000 : ℝ)*X 2 0+(5423843267/10000000000 : ℝ)*X 2 1+(-1675796183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4240045799/10000000000 : ℝ)*X 0 0+(4485994769/10000000000 : ℝ)*X 0 1+(40051921/100000000 : ℝ)*X 0 2+(4240045799/10000000000 : ℝ)*X 1 0+(4485994769/10000000000 : ℝ)*X 1 1+(40051921/100000000 : ℝ)*X 1 2+(4240045799/10000000000 : ℝ)*X 2 0+(4485994769/10000000000 : ℝ)*X 2 1+(40051921/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3360769840650638022570743623/366500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1542234811/100000000000000 : ℝ)*(base19) + (1446174043/100000000000000 : ℝ)*(base23) + (426597/800000000000 : ℝ)*(lower2) + (225997303/100000000000000 : ℝ)*(upper3) + (15556267/10000000000000 : ℝ)*(upper5) + (3471371718054767/100000000000000 : ℝ)*(major0) + (3471371718054767/100000000000000 : ℝ)*(major1) + (216960732378423/6250000000000 : ℝ)*(major2) + (4884652571437197/100000000000000 : ℝ)*(sp0) + (4884676345461313/100000000000000 : ℝ)*(sp1) + (4884676441522081/100000000000000 : ℝ)*(sp2) + (2058053841895129/100000000000000 : ℝ)*(sp3) + (25316258927/100000000000000 : ℝ)*(sp4) + (5700427403/50000000000000 : ℝ)*(sp7) + (128629077671871/6250000000000 : ℝ)*(f.failure) + (1221169471924031/25000000000000 : ℝ)*(f.sum) + (30024837131419/8796000000000000000000000000 : ℝ)*base65 + (2538258682140485459/733000000000000000000000000000000 : ℝ)*base67 + (272426883355394861/17179687500000000000000000000000 : ℝ)*base69 + (1634797072192485459/733000000000000000000000000000000 : ℝ)*base71 + (33981196014271/8796000000000000000000000000 : ℝ)*base73 + (8290746529013507/8589843750000000000000000000000 : ℝ)*base76 + (9976128964722806377/2199000000000000000000000000000000 : ℝ)*base77 + (2301109980347193623/2199000000000000000000000000000000 : ℝ)*base80 + (112393905546491/21990000000000000000000000000 : ℝ)*base81 + (6516697/625000000000000000000 : ℝ)*base89 + (6516697/625000000000000000000 : ℝ)*base91 + (266697/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (678523788903240771814455419/91625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1316942409/100000000000000 : ℝ)*(base19) + (17217537/1250000000000 : ℝ)*(base23) + (146576981/100000000000000 : ℝ)*(upper3) + (10534227/100000000000000 : ℝ)*(lower4) + (1673837/1000000000000 : ℝ)*(upper5) + (1754062551246251/50000000000000 : ℝ)*(major0) + (1754062551246251/50000000000000 : ℝ)*(major1) + (1754062551246251/50000000000000 : ℝ)*(major2) + (10070593269/50000000000000 : ℝ)*(sp1) + (9637857781/50000000000000 : ℝ)*(sp2) + (617049351186429/12500000000000 : ℝ)*(sp4) + (2468186675681243/50000000000000 : ℝ)*(sp5) + (493637415637291/10000000000000 : ℝ)*(sp6) + (6499547339517/312500000000 : ℝ)*(sp7) + (6499547339517/312500000000 : ℝ)*(f.failure) + (617049351186429/12500000000000 : ℝ)*(f.sum) + (3641282018137/10995000000000000000000000000 : ℝ)*base66 + (3916041400677269581/1099500000000000000000000000000000 : ℝ)*base67 + (7573925087769269581/1099500000000000000000000000000000 : ℝ)*base69 + (2492501207528730419/1099500000000000000000000000000000 : ℝ)*base72 + (25389317384077/10995000000000000000000000000 : ℝ)*base74 + (10195262780391269581/1099500000000000000000000000000000 : ℝ)*base75 + (2578046654478269581/1099500000000000000000000000000000 : ℝ)*base77 + (5510771593677269581/1099500000000000000000000000000000 : ℝ)*base79 + (53819005519987/10995000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (118819/31250000000000000000 : ℝ)*base89 + (118819/31250000000000000000 : ℝ)*base91 + (118819/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1578_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168671607/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3879/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5559/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15487/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1578_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1578_s5_0 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-887370977/5000000000 : ℝ)*x 0 + (2712392917/5000000000 : ℝ)*x 1 + (5220317733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (887370977/5000000000 : ℝ)^4653 ≤ (5447944255329/50000000000000 : ℝ)^3629 := by
    have hnat : (887370977 : ℕ)^4653*50000000000000^3629 ≤ 5447944255329^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887370977 5000000000 5447944255329 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712392917/5000000000 : ℝ)^4653 ≤ (22824589105983/50000000000000 : ℝ)^3629 := by
    have hnat : (2712392917 : ℕ)^4653*50000000000000^3629 ≤ 22824589105983^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712392917 5000000000 22824589105983 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220317733/10000000000 : ℝ)^4653 ≤ (21727466633371/50000000000000 : ℝ)^3629 := by
    have hnat : (5220317733 : ℕ)^4653*50000000000000^3629 ≤ 21727466633371^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220317733 10000000000 21727466633371 50000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-887370977/5000000000 : ℝ), (2712392917/5000000000 : ℝ), (5220317733/10000000000 : ℝ)] ![(5447944255329/50000000000000 : ℝ), (22824589105983/50000000000000 : ℝ), (21727466633371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-887370977/5000000000 : ℝ)|^4653 ≤ (5447944255329/50000000000000 : ℝ)^3629
        have hw : |(-887370977/5000000000 : ℝ)|=(887370977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712392917/5000000000 : ℝ)|^4653 ≤ (22824589105983/50000000000000 : ℝ)^3629
        have hw : |(2712392917/5000000000 : ℝ)|=(2712392917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220317733/10000000000 : ℝ)|^4653 ≤ (21727466633371/50000000000000 : ℝ)^3629
        have hw : |(5220317733/10000000000 : ℝ)|=(5220317733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s5_1 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336924693/2500000000 : ℝ)*x 0 + (-939664713/5000000000 : ℝ)*x 1 + (5220318363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336924693/2500000000 : ℝ)^4653 ≤ (44819129862021/100000000000000 : ℝ)^3629 := by
    have hnat : (1336924693 : ℕ)^4653*100000000000000^3629 ≤ 44819129862021^3629*2500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336924693 2500000000 44819129862021 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (939664713/5000000000 : ℝ)^4653 ≤ (586296506133/5000000000000 : ℝ)^3629 := by
    have hnat : (939664713 : ℕ)^4653*5000000000000^3629 ≤ 586296506133^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939664713 5000000000 586296506133 5000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220318363/10000000000 : ℝ)^4653 ≤ (43454939990759/100000000000000 : ℝ)^3629 := by
    have hnat : (5220318363 : ℕ)^4653*100000000000000^3629 ≤ 43454939990759^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220318363 10000000000 43454939990759 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336924693/2500000000 : ℝ), (-939664713/5000000000 : ℝ), (5220318363/10000000000 : ℝ)] ![(44819129862021/100000000000000 : ℝ), (586296506133/5000000000000 : ℝ), (43454939990759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336924693/2500000000 : ℝ)|^4653 ≤ (44819129862021/100000000000000 : ℝ)^3629
        have hw : |(1336924693/2500000000 : ℝ)|=(1336924693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-939664713/5000000000 : ℝ)|^4653 ≤ (586296506133/5000000000000 : ℝ)^3629
        have hw : |(-939664713/5000000000 : ℝ)|=(939664713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220318363/10000000000 : ℝ)|^4653 ≤ (43454939990759/100000000000000 : ℝ)^3629
        have hw : |(5220318363/10000000000 : ℝ)|=(5220318363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s5_2 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336924739/2500000000 : ℝ)*x 0 + (208812727/400000000 : ℝ)*x 1 + (-1879329431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336924739/2500000000 : ℝ)^4653 ≤ (8963826367853/20000000000000 : ℝ)^3629 := by
    have hnat : (1336924739 : ℕ)^4653*20000000000000^3629 ≤ 8963826367853^3629*2500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336924739 2500000000 8963826367853 20000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208812727/400000000 : ℝ)^4653 ≤ (43454937984227/100000000000000 : ℝ)^3629 := by
    have hnat : (208812727 : ℕ)^4653*100000000000000^3629 ≤ 43454937984227^3629*400000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208812727 400000000 43454937984227 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1879329431/10000000000 : ℝ)^4653 ≤ (586296508133/5000000000000 : ℝ)^3629 := by
    have hnat : (1879329431 : ℕ)^4653*5000000000000^3629 ≤ 586296508133^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879329431 10000000000 586296508133 5000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336924739/2500000000 : ℝ), (208812727/400000000 : ℝ), (-1879329431/10000000000 : ℝ)] ![(8963826367853/20000000000000 : ℝ), (43454937984227/100000000000000 : ℝ), (586296508133/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336924739/2500000000 : ℝ)|^4653 ≤ (8963826367853/20000000000000 : ℝ)^3629
        have hw : |(1336924739/2500000000 : ℝ)|=(1336924739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208812727/400000000 : ℝ)|^4653 ≤ (43454937984227/100000000000000 : ℝ)^3629
        have hw : |(208812727/400000000 : ℝ)|=(208812727/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1879329431/10000000000 : ℝ)|^4653 ≤ (586296508133/5000000000000 : ℝ)^3629
        have hw : |(-1879329431/10000000000 : ℝ)|=(1879329431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s5_3 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4239995923/10000000000 : ℝ)*x 0 + (2001469181/5000000000 : ℝ)*x 1 + (561028289/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4239995923/10000000000 : ℝ)^4653 ≤ (4160338207903/12500000000000 : ℝ)^3629 := by
    have hnat : (4239995923 : ℕ)^4653*12500000000000^3629 ≤ 4160338207903^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239995923 10000000000 4160338207903 12500000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2001469181/5000000000 : ℝ)^4653 ≤ (30915879244753/100000000000000 : ℝ)^3629 := by
    have hnat : (2001469181 : ℕ)^4653*100000000000000^3629 ≤ 30915879244753^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001469181 5000000000 30915879244753 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561028289/1250000000 : ℝ)^4653 ≤ (223758844261/625000000000 : ℝ)^3629 := by
    have hnat : (561028289 : ℕ)^4653*625000000000^3629 ≤ 223758844261^3629*1250000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561028289 1250000000 223758844261 625000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4239995923/10000000000 : ℝ), (2001469181/5000000000 : ℝ), (561028289/1250000000 : ℝ)] ![(4160338207903/12500000000000 : ℝ), (30915879244753/100000000000000 : ℝ), (223758844261/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4239995923/10000000000 : ℝ)|^4653 ≤ (4160338207903/12500000000000 : ℝ)^3629
        have hw : |(4239995923/10000000000 : ℝ)|=(4239995923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2001469181/5000000000 : ℝ)|^4653 ≤ (30915879244753/100000000000000 : ℝ)^3629
        have hw : |(2001469181/5000000000 : ℝ)|=(2001469181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561028289/1250000000 : ℝ)|^4653 ≤ (223758844261/625000000000 : ℝ)^3629
        have hw : |(561028289/1250000000 : ℝ)|=(561028289/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s5_4 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-887384257/5000000000 : ℝ)*x 0 + (5221385227/10000000000 : ℝ)*x 1 + (1355927603/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (887384257/5000000000 : ℝ)^4653 ≤ (10896097585851/100000000000000 : ℝ)^3629 := by
    have hnat : (887384257 : ℕ)^4653*100000000000000^3629 ≤ 10896097585851^3629*5000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887384257 5000000000 10896097585851 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221385227/10000000000 : ℝ)^4653 ≤ (5433290875519/12500000000000 : ℝ)^3629 := by
    have hnat : (5221385227 : ℕ)^4653*12500000000000^3629 ≤ 5433290875519^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221385227 10000000000 5433290875519 12500000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355927603/2500000000 : ℝ)^4653 ≤ (45637575400919/100000000000000 : ℝ)^3629 := by
    have hnat : (1355927603 : ℕ)^4653*100000000000000^3629 ≤ 45637575400919^3629*2500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355927603 2500000000 45637575400919 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-887384257/5000000000 : ℝ), (5221385227/10000000000 : ℝ), (1355927603/2500000000 : ℝ)] ![(10896097585851/100000000000000 : ℝ), (5433290875519/12500000000000 : ℝ), (45637575400919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-887384257/5000000000 : ℝ)|^4653 ≤ (10896097585851/100000000000000 : ℝ)^3629
        have hw : |(-887384257/5000000000 : ℝ)|=(887384257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221385227/10000000000 : ℝ)|^4653 ≤ (5433290875519/12500000000000 : ℝ)^3629
        have hw : |(5221385227/10000000000 : ℝ)|=(5221385227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355927603/2500000000 : ℝ)|^4653 ≤ (45637575400919/100000000000000 : ℝ)^3629
        have hw : |(1355927603/2500000000 : ℝ)|=(1355927603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s5_5 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293552211/10000000000 : ℝ)*x 0 + (-1675937433/10000000000 : ℝ)*x 1 + (271185531/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293552211/10000000000 : ℝ)^4653 ≤ (44238109847429/100000000000000 : ℝ)^3629 := by
    have hnat : (5293552211 : ℕ)^4653*100000000000000^3629 ≤ 44238109847429^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293552211 10000000000 44238109847429 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1675937433/10000000000 : ℝ)^4653 ≤ (10124312489309/100000000000000 : ℝ)^3629 := by
    have hnat : (1675937433 : ℕ)^4653*100000000000000^3629 ≤ 10124312489309^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1675937433 10000000000 10124312489309 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271185531/500000000 : ℝ)^4653 ≤ (5704697205623/12500000000000 : ℝ)^3629 := by
    have hnat : (271185531 : ℕ)^4653*12500000000000^3629 ≤ 5704697205623^3629*500000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271185531 500000000 5704697205623 12500000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293552211/10000000000 : ℝ), (-1675937433/10000000000 : ℝ), (271185531/500000000 : ℝ)] ![(44238109847429/100000000000000 : ℝ), (10124312489309/100000000000000 : ℝ), (5704697205623/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293552211/10000000000 : ℝ)|^4653 ≤ (44238109847429/100000000000000 : ℝ)^3629
        have hw : |(5293552211/10000000000 : ℝ)|=(5293552211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1675937433/10000000000 : ℝ)|^4653 ≤ (10124312489309/100000000000000 : ℝ)^3629
        have hw : |(-1675937433/10000000000 : ℝ)|=(1675937433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271185531/500000000 : ℝ)|^4653 ≤ (5704697205623/12500000000000 : ℝ)^3629
        have hw : |(271185531/500000000 : ℝ)|=(271185531/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s5_6 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661694067/1250000000 : ℝ)*x 0 + (338981897/625000000 : ℝ)*x 1 + (-1675937357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661694067/1250000000 : ℝ)^4653 ≤ (4423811332983/10000000000000 : ℝ)^3629 := by
    have hnat : (661694067 : ℕ)^4653*10000000000000^3629 ≤ 4423811332983^3629*1250000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661694067 1250000000 4423811332983 10000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338981897/625000000 : ℝ)^4653 ≤ (45637574753593/100000000000000 : ℝ)^3629 := by
    have hnat : (338981897 : ℕ)^4653*100000000000000^3629 ≤ 45637574753593^3629*625000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338981897 625000000 45637574753593 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1675937357/10000000000 : ℝ)^4653 ≤ (2024862380129/20000000000000 : ℝ)^3629 := by
    have hnat : (1675937357 : ℕ)^4653*20000000000000^3629 ≤ 2024862380129^3629*10000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1675937357 10000000000 2024862380129 20000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661694067/1250000000 : ℝ), (338981897/625000000 : ℝ), (-1675937357/10000000000 : ℝ)] ![(4423811332983/10000000000000 : ℝ), (45637574753593/100000000000000 : ℝ), (2024862380129/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661694067/1250000000 : ℝ)|^4653 ≤ (4423811332983/10000000000000 : ℝ)^3629
        have hw : |(661694067/1250000000 : ℝ)|=(661694067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338981897/625000000 : ℝ)|^4653 ≤ (45637574753593/100000000000000 : ℝ)^3629
        have hw : |(338981897/625000000 : ℝ)|=(338981897/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1675937357/10000000000 : ℝ)|^4653 ≤ (2024862380129/20000000000000 : ℝ)^3629
        have hw : |(-1675937357/10000000000 : ℝ)|=(1675937357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1578_s5_7 (p : ℝ) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (848011651/2000000000 : ℝ)*x 0 + (560711837/1250000000 : ℝ)*x 1 + (250343079/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848011651/2000000000 : ℝ)^4653 ≤ (6656666603029/20000000000000 : ℝ)^3629 := by
    have hnat : (848011651 : ℕ)^4653*20000000000000^3629 ≤ 6656666603029^3629*2000000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848011651 2000000000 6656666603029 20000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560711837/1250000000 : ℝ)^4653 ≤ (7155104983639/20000000000000 : ℝ)^3629 := by
    have hnat : (560711837 : ℕ)^4653*20000000000000^3629 ≤ 7155104983639^3629*1250000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560711837 1250000000 7155104983639 20000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250343079/625000000 : ℝ)^4653 ≤ (30941142051329/100000000000000 : ℝ)^3629 := by
    have hnat : (250343079 : ℕ)^4653*100000000000000^3629 ≤ 30941142051329^3629*625000000^4653 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250343079 625000000 30941142051329 100000000000000 4653 3629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4653/1024 : ℝ)) 4653 3629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(848011651/2000000000 : ℝ), (560711837/1250000000 : ℝ), (250343079/625000000 : ℝ)] ![(6656666603029/20000000000000 : ℝ), (7155104983639/20000000000000 : ℝ), (30941142051329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(848011651/2000000000 : ℝ)|^4653 ≤ (6656666603029/20000000000000 : ℝ)^3629
        have hw : |(848011651/2000000000 : ℝ)|=(848011651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560711837/1250000000 : ℝ)|^4653 ≤ (7155104983639/20000000000000 : ℝ)^3629
        have hw : |(560711837/1250000000 : ℝ)|=(560711837/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(250343079/625000000 : ℝ)|^4653 ≤ (30941142051329/100000000000000 : ℝ)^3629
        have hw : |(250343079/625000000 : ℝ)|=(250343079/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1578_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168671607/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15487/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11147/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15487/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1393/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15487/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1393/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15487/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1393/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15487/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1393/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15487/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1393/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15487/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1393/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1393/12500 : ℝ) ^ (4651/1024 : ℝ) ≤ (4695351792435003/100000000000000000000 : ℝ) := by
    have hpowers : (1393/12500 : ℝ)^4651 ≤ (4695351792435003/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1393 : ℕ)^4651*100000000000000000000^1024 ≤ 4695351792435003^1024*12500^4651 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1393 12500 4695351792435003 100000000000000000000 4651 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1393/12500 : ℝ)) (X := (4695351792435003/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15487/100000 : ℝ) ^ (4651/1024 : ℝ) ≤ (4186660964271589/20000000000000000000 : ℝ) := by
    have hpowers : (15487/100000 : ℝ)^4651 ≤ (4186660964271589/20000000000000000000 : ℝ)^1024 := by
      have hnat : (15487 : ℕ)^4651*20000000000000000000^1024 ≤ 4186660964271589^1024*100000^4651 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15487 100000 4186660964271589 20000000000000000000 4651 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15487/100000 : ℝ)) (X := (4186660964271589/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004695351792435003/50000000000000000000 : ℝ) ≤ (10000206745396461/10000000000000000 : ℝ) ^ (4651/1024 : ℝ) := by
    have hpowers : (50004695351792435003/50000000000000000000 : ℝ)^1024 ≤ (10000206745396461/10000000000000000 : ℝ)^4651 := by
      have hnat : (50004695351792435003 : ℕ)^1024*10000000000000000^4651 ≤ 10000206745396461^4651*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004695351792435003 50000000000000000000 10000206745396461 10000000000000000 1024 4651 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000206745396461/10000000000000000 : ℝ)) (X := (50004695351792435003/50000000000000000000 : ℝ)) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25006407164153448237/25000000000000000000 : ℝ) ≤ (10000564203875011/10000000000000000 : ℝ) ^ (4651/1024 : ℝ) := by
    have hpowers : (25006407164153448237/25000000000000000000 : ℝ)^1024 ≤ (10000564203875011/10000000000000000 : ℝ)^4651 := by
      have hnat : (25006407164153448237 : ℕ)^1024*10000000000000000^4651 ≤ 10000564203875011^4651*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006407164153448237 25000000000000000000 10000564203875011 10000000000000000 1024 4651 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000564203875011/10000000000000000 : ℝ)) (X := (25006407164153448237/25000000000000000000 : ℝ)) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004186660964271589/10000000000000000000 : ℝ) ≤ (10000921662353561/10000000000000000 : ℝ) ^ (4651/1024 : ℝ) := by
    have hpowers : (10004186660964271589/10000000000000000000 : ℝ)^1024 ≤ (10000921662353561/10000000000000000 : ℝ)^4651 := by
      have hnat : (10004186660964271589 : ℕ)^1024*10000000000000000^4651 ≤ 10000921662353561^4651*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004186660964271589 10000000000000000000 10000921662353561 10000000000000000 1024 4651 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000921662353561/10000000000000000 : ℝ)) (X := (10004186660964271589/10000000000000000000 : ℝ)) (by norm_num) 4651 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4695351792435003/100000000000000000000 : ℝ) ≤ ((43422930860686907723/43430000000000000000 : ℝ)+2*(7149169571/8686000000000 : ℝ)*(1393/12500 : ℝ))^(4651/1024 : ℝ) := by
    rw [show (43422930860686907723/43430000000000000000 : ℝ)+2*(7149169571/8686000000000 : ℝ)*(1393/12500 : ℝ)=(10000206745396461/10000000000000000 : ℝ) by norm_num, show 1+2*(4695351792435003/100000000000000000000 : ℝ)=(50004695351792435003/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4186660964271589/20000000000000000000 : ℝ)+(4695351792435003/100000000000000000000 : ℝ) ≤ ((43422930860686907723/43430000000000000000 : ℝ)+(7149169571/8686000000000 : ℝ)*((15487/100000 : ℝ)+(1393/12500 : ℝ)))^(4651/1024 : ℝ) := by
    rw [show (43422930860686907723/43430000000000000000 : ℝ)+(7149169571/8686000000000 : ℝ)*((15487/100000 : ℝ)+(1393/12500 : ℝ))=(10000564203875011/10000000000000000 : ℝ) by norm_num, show 1+(4186660964271589/20000000000000000000 : ℝ)+(4695351792435003/100000000000000000000 : ℝ)=(25006407164153448237/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4186660964271589/20000000000000000000 : ℝ) ≤ ((43422930860686907723/43430000000000000000 : ℝ)+2*(7149169571/8686000000000 : ℝ)*(15487/100000 : ℝ))^(4651/1024 : ℝ) := by
    rw [show (43422930860686907723/43430000000000000000 : ℝ)+2*(7149169571/8686000000000 : ℝ)*(15487/100000 : ℝ)=(10000921662353561/10000000000000000 : ℝ) by norm_num, show 1+2*(4186660964271589/20000000000000000000 : ℝ)=(10004186660964271589/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43422930860686907723/43430000000000000000 : ℝ)*(X 1 0+X 2 0)+(7149169571/8686000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4651/1024 : ℝ)) (lo := (1393/12500 : ℝ)) (hi := (15487/100000 : ℝ)) (c := (43422930860686907723/43430000000000000000 : ℝ)) (alpha := (7149169571/8686000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43422930860686907723/43430000000000000000 : ℝ)*(X 0 1+X 2 1)+(7149169571/8686000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4651/1024 : ℝ)) (lo := (1393/12500 : ℝ)) (hi := (15487/100000 : ℝ)) (c := (43422930860686907723/43430000000000000000 : ℝ)) (alpha := (7149169571/8686000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43422930860686907723/43430000000000000000 : ℝ)*(X 0 2+X 1 2)+(7149169571/8686000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4651/1024 : ℝ)) (lo := (1393/12500 : ℝ)) (hi := (15487/100000 : ℝ)) (c := (43422930860686907723/43430000000000000000 : ℝ)) (alpha := (7149169571/8686000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-887370977/5000000000 : ℝ)*X 0 0+(2712392917/5000000000 : ℝ)*X 0 1+(5220317733/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336924693/2500000000 : ℝ)*X 1 0+(-939664713/5000000000 : ℝ)*X 1 1+(5220318363/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336924739/2500000000 : ℝ)*X 2 0+(208812727/400000000 : ℝ)*X 2 1+(-1879329431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4239995923/10000000000 : ℝ)*X 0 0+(2001469181/5000000000 : ℝ)*X 0 1+(561028289/1250000000 : ℝ)*X 0 2+(4239995923/10000000000 : ℝ)*X 1 0+(2001469181/5000000000 : ℝ)*X 1 1+(561028289/1250000000 : ℝ)*X 1 2+(4239995923/10000000000 : ℝ)*X 2 0+(2001469181/5000000000 : ℝ)*X 2 1+(561028289/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-887384257/5000000000 : ℝ)*X 0 0+(5221385227/10000000000 : ℝ)*X 0 1+(1355927603/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293552211/10000000000 : ℝ)*X 1 0+(-1675937433/10000000000 : ℝ)*X 1 1+(271185531/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661694067/1250000000 : ℝ)*X 2 0+(338981897/625000000 : ℝ)*X 2 1+(-1675937357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((848011651/2000000000 : ℝ)*X 0 0+(560711837/1250000000 : ℝ)*X 0 1+(250343079/625000000 : ℝ)*X 0 2+(848011651/2000000000 : ℝ)*X 1 0+(560711837/1250000000 : ℝ)*X 1 1+(250343079/625000000 : ℝ)*X 1 2+(848011651/2000000000 : ℝ)*X 2 0+(560711837/1250000000 : ℝ)*X 2 1+(250343079/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1578_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (871517220685643652219/217150000000000000000000000 : ℝ) := by norm_num
    linear_combination (35781523/3125000000000 : ℝ)*(base19) + (502469443/50000000000000 : ℝ)*(base23) + (164895867/100000000000000 : ℝ)*(lower2) + (115135043/50000000000000 : ℝ)*(upper3) + (14979373/50000000000000 : ℝ)*(upper5) + (868930877820867/25000000000000 : ℝ)*(major0) + (868930877820867/25000000000000 : ℝ)*(major1) + (868930877820867/25000000000000 : ℝ)*(major2) + (2445385436003833/50000000000000 : ℝ)*(sp0) + (978160092407063/20000000000000 : ℝ)*(sp1) + (978160120421033/20000000000000 : ℝ)*(sp2) + (2060636954521909/100000000000000 : ℝ)*(sp3) + (15367518193/50000000000000 : ℝ)*(sp4) + (832721983/10000000000000 : ℝ)*(sp7) + (2060645281741739/100000000000000 : ℝ)*(f.failure) + (1222700401761013/25000000000000 : ℝ)*(f.sum) + (18915028567647/4343000000000000000000000000 : ℝ)*base66 + (4094322884955144159/1085750000000000000000000000000000 : ℝ)*base68 + (8385748819695644159/1085750000000000000000000000000000 : ℝ)*base70 + (3475266584965105841/1085750000000000000000000000000000 : ℝ)*base71 + (5861749925671/1085750000000000000000000000 : ℝ)*base74 + (5544209640978105841/1085750000000000000000000000000000 : ℝ)*base75 + (2633786743554894159/1085750000000000000000000000000000 : ℝ)*base78 + (11880533136673105841/1085750000000000000000000000000000 : ℝ)*base79 + (16449326751021/4343000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (76104573/10000000000000000000000 : ℝ)*base89 + (76104573/10000000000000000000000 : ℝ)*base91 + (76104573/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (815163088936461427509/135718750000000000000000000 : ℝ) := by norm_num
    linear_combination (719213899/100000000000000 : ℝ)*(base19) + (1135029187/100000000000000 : ℝ)*(base23) + (69483551/25000000000000 : ℝ)*(lower1) + (30800677/20000000000000 : ℝ)*(upper3) + (31113849/100000000000000 : ℝ)*(lower4) + (18611507/20000000000000 : ℝ)*(upper5) + (878120232132861/25000000000000 : ℝ)*(major0) + (878120232132861/25000000000000 : ℝ)*(major1) + (878120232132861/25000000000000 : ℝ)*(major2) + (5239154449/100000000000000 : ℝ)*(sp2) + (2471262039146271/50000000000000 : ℝ)*(sp4) + (4942523359078643/100000000000000 : ℝ)*(sp5) + (2471258852054453/50000000000000 : ℝ)*(sp6) + (1041218789280713/50000000000000 : ℝ)*(sp7) + (1041218789280713/50000000000000 : ℝ)*(f.failure) + (2471262039146271/50000000000000 : ℝ)*(f.sum) + (2812687157917/2171500000000000000000000000 : ℝ)*base65 + (9480588322059514497/1085750000000000000000000000000000 : ℝ)*base68 + (11415751576531985503/1085750000000000000000000000000000 : ℝ)*base69 + (31300936226594264497/1085750000000000000000000000000000 : ℝ)*base72 + (6581079008171/4343000000000000000000000000 : ℝ)*base74 + (38775150000745014497/1085750000000000000000000000000000 : ℝ)*base76 + (4918585877120485503/1085750000000000000000000000000000 : ℝ)*base77 + (3579541810095735503/1085750000000000000000000000000000 : ℝ)*base79 + (5746146800711/4343000000000000000000000000 : ℝ)*base81 + (35815791/5000000000000000000000 : ℝ)*base89 + (35815791/5000000000000000000000 : ℝ)*base91 + (35815791/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1578_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168671607/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15487/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11147/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1578_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1578_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168671607/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15791/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (679/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11147/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1578_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1578_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1578_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4651/1024 : ℝ) ≤ p) (hpb : p ≤ (4653/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168671607/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15791/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (679/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11147/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1578_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
