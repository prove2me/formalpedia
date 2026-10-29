-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1546_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:09:18.488482+00:00
-- url     : https://prove2.me/submissions/bb58d724-ac46-4406-a373-c5cff44d91eb

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
theorem support_rectangle_w1546_s0_0 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-825179837/5000000000 : ℝ)*x 0 + (22996587/39062500 : ℝ)*x 1 + (973918701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (825179837/5000000000 : ℝ)^4589 ≤ (4918222949627/50000000000000 : ℝ)^3565 := by
    have hnat : (825179837 : ℕ)^4589*50000000000000^3565 ≤ 4918222949627^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825179837 5000000000 4918222949627 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22996587/39062500 : ℝ)^4589 ≤ (50560466661229/100000000000000 : ℝ)^3565 := by
    have hnat : (22996587 : ℕ)^4589*100000000000000^3565 ≤ 50560466661229^3565*39062500^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22996587 39062500 50560466661229 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (973918701/2000000000 : ℝ)^4589 ≤ (618798241103/1562500000000 : ℝ)^3565 := by
    have hnat : (973918701 : ℕ)^4589*1562500000000^3565 ≤ 618798241103^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973918701 2000000000 618798241103 1562500000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-825179837/5000000000 : ℝ), (22996587/39062500 : ℝ), (973918701/2000000000 : ℝ)] ![(4918222949627/50000000000000 : ℝ), (50560466661229/100000000000000 : ℝ), (618798241103/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-825179837/5000000000 : ℝ)|^4589 ≤ (4918222949627/50000000000000 : ℝ)^3565
        have hw : |(-825179837/5000000000 : ℝ)|=(825179837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(22996587/39062500 : ℝ)|^4589 ≤ (50560466661229/100000000000000 : ℝ)^3565
        have hw : |(22996587/39062500 : ℝ)|=(22996587/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(973918701/2000000000 : ℝ)|^4589 ≤ (618798241103/1562500000000 : ℝ)^3565
        have hw : |(973918701/2000000000 : ℝ)|=(973918701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s0_1 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1094124217/2000000000 : ℝ)*x 0 + (-2218260627/10000000000 : ℝ)*x 1 + (4869593583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094124217/2000000000 : ℝ)^4589 ≤ (23001759660187/50000000000000 : ℝ)^3565 := by
    have hnat : (1094124217 : ℕ)^4589*50000000000000^3565 ≤ 23001759660187^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094124217 2000000000 23001759660187 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2218260627/10000000000 : ℝ)^4589 ≤ (7196696210217/50000000000000 : ℝ)^3565 := by
    have hnat : (2218260627 : ℕ)^4589*50000000000000^3565 ≤ 7196696210217^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218260627 10000000000 7196696210217 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4869593583/10000000000 : ℝ)^4589 ≤ (7920617649431/20000000000000 : ℝ)^3565 := by
    have hnat : (4869593583 : ℕ)^4589*20000000000000^3565 ≤ 7920617649431^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4869593583 10000000000 7920617649431 20000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094124217/2000000000 : ℝ), (-2218260627/10000000000 : ℝ), (4869593583/10000000000 : ℝ)] ![(23001759660187/50000000000000 : ℝ), (7196696210217/50000000000000 : ℝ), (7920617649431/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094124217/2000000000 : ℝ)|^4589 ≤ (23001759660187/50000000000000 : ℝ)^3565
        have hw : |(1094124217/2000000000 : ℝ)|=(1094124217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2218260627/10000000000 : ℝ)|^4589 ≤ (7196696210217/50000000000000 : ℝ)^3565
        have hw : |(-2218260627/10000000000 : ℝ)|=(2218260627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4869593583/10000000000 : ℝ)|^4589 ≤ (7920617649431/20000000000000 : ℝ)^3565
        have hw : |(4869593583/10000000000 : ℝ)|=(4869593583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s0_2 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5470621001/10000000000 : ℝ)*x 0 + (4869593541/10000000000 : ℝ)*x 1 + (-2218260789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5470621001/10000000000 : ℝ)^4589 ≤ (9200703682221/20000000000000 : ℝ)^3565 := by
    have hnat : (5470621001 : ℕ)^4589*20000000000000^3565 ≤ 9200703682221^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470621001 10000000000 9200703682221 20000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4869593541/10000000000 : ℝ)^4589 ≤ (39603087807467/100000000000000 : ℝ)^3565 := by
    have hnat : (4869593541 : ℕ)^4589*100000000000000^3565 ≤ 39603087807467^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4869593541 10000000000 39603087807467 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2218260789/10000000000 : ℝ)^4589 ≤ (3598348443379/25000000000000 : ℝ)^3565 := by
    have hnat : (2218260789 : ℕ)^4589*25000000000000^3565 ≤ 3598348443379^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218260789 10000000000 3598348443379 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5470621001/10000000000 : ℝ), (4869593541/10000000000 : ℝ), (-2218260789/10000000000 : ℝ)] ![(9200703682221/20000000000000 : ℝ), (39603087807467/100000000000000 : ℝ), (3598348443379/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5470621001/10000000000 : ℝ)|^4589 ≤ (9200703682221/20000000000000 : ℝ)^3565
        have hw : |(5470621001/10000000000 : ℝ)|=(5470621001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4869593541/10000000000 : ℝ)|^4589 ≤ (39603087807467/100000000000000 : ℝ)^3565
        have hw : |(4869593541/10000000000 : ℝ)|=(4869593541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2218260789/10000000000 : ℝ)|^4589 ≤ (3598348443379/25000000000000 : ℝ)^3565
        have hw : |(-2218260789/10000000000 : ℝ)|=(2218260789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s0_3 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4136097563/10000000000 : ℝ)*x 0 + (38650563/125000000 : ℝ)*x 1 + (2727386549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4136097563/10000000000 : ℝ)^4589 ≤ (8024194685899/25000000000000 : ℝ)^3565 := by
    have hnat : (4136097563 : ℕ)^4589*25000000000000^3565 ≤ 8024194685899^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4136097563 10000000000 8024194685899 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38650563/125000000 : ℝ)^4589 ≤ (22071179050431/100000000000000 : ℝ)^3565 := by
    have hnat : (38650563 : ℕ)^4589*100000000000000^3565 ≤ 22071179050431^3565*125000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38650563 125000000 22071179050431 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727386549/5000000000 : ℝ)^4589 ≤ (2864502637041/6250000000000 : ℝ)^3565 := by
    have hnat : (2727386549 : ℕ)^4589*6250000000000^3565 ≤ 2864502637041^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727386549 5000000000 2864502637041 6250000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4136097563/10000000000 : ℝ), (38650563/125000000 : ℝ), (2727386549/5000000000 : ℝ)] ![(8024194685899/25000000000000 : ℝ), (22071179050431/100000000000000 : ℝ), (2864502637041/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4136097563/10000000000 : ℝ)|^4589 ≤ (8024194685899/25000000000000 : ℝ)^3565
        have hw : |(4136097563/10000000000 : ℝ)|=(4136097563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38650563/125000000 : ℝ)|^4589 ≤ (22071179050431/100000000000000 : ℝ)^3565
        have hw : |(38650563/125000000 : ℝ)|=(38650563/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727386549/5000000000 : ℝ)|^4589 ≤ (2864502637041/6250000000000 : ℝ)^3565
        have hw : |(2727386549/5000000000 : ℝ)|=(2727386549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s0_4 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-413400261/2500000000 : ℝ)*x 0 + (1223842771/2500000000 : ℝ)*x 1 + (293021503/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (413400261/2500000000 : ℝ)^4589 ≤ (9861321247203/100000000000000 : ℝ)^3565 := by
    have hnat : (413400261 : ℕ)^4589*100000000000000^3565 ≤ 9861321247203^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413400261 2500000000 9861321247203 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1223842771/2500000000 : ℝ)^4589 ≤ (3987315138381/10000000000000 : ℝ)^3565 := by
    have hnat : (1223842771 : ℕ)^4589*10000000000000^3565 ≤ 3987315138381^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1223842771 2500000000 3987315138381 10000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (293021503/500000000 : ℝ)^4589 ≤ (50265527357339/100000000000000 : ℝ)^3565 := by
    have hnat : (293021503 : ℕ)^4589*100000000000000^3565 ≤ 50265527357339^3565*500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293021503 500000000 50265527357339 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-413400261/2500000000 : ℝ), (1223842771/2500000000 : ℝ), (293021503/500000000 : ℝ)] ![(9861321247203/100000000000000 : ℝ), (3987315138381/10000000000000 : ℝ), (50265527357339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-413400261/2500000000 : ℝ)|^4589 ≤ (9861321247203/100000000000000 : ℝ)^3565
        have hw : |(-413400261/2500000000 : ℝ)|=(413400261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1223842771/2500000000 : ℝ)|^4589 ≤ (3987315138381/10000000000000 : ℝ)^3565
        have hw : |(1223842771/2500000000 : ℝ)|=(1223842771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(293021503/500000000 : ℝ)|^4589 ≤ (50265527357339/100000000000000 : ℝ)^3565
        have hw : |(293021503/500000000 : ℝ)|=(293021503/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s0_5 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5192501637/10000000000 : ℝ)*x 0 + (-306856127/2500000000 : ℝ)*x 1 + (2930214887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5192501637/10000000000 : ℝ)^4589 ≤ (10753808136421/25000000000000 : ℝ)^3565 := by
    have hnat : (5192501637 : ℕ)^4589*25000000000000^3565 ≤ 10753808136421^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192501637 10000000000 10753808136421 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (306856127/2500000000 : ℝ)^4589 ≤ (3359621619491/50000000000000 : ℝ)^3565 := by
    have hnat : (306856127 : ℕ)^4589*50000000000000^3565 ≤ 3359621619491^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306856127 2500000000 3359621619491 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2930214887/5000000000 : ℝ)^4589 ≤ (39269940781/78125000000 : ℝ)^3565 := by
    have hnat : (2930214887 : ℕ)^4589*78125000000^3565 ≤ 39269940781^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2930214887 5000000000 39269940781 78125000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5192501637/10000000000 : ℝ), (-306856127/2500000000 : ℝ), (2930214887/5000000000 : ℝ)] ![(10753808136421/25000000000000 : ℝ), (3359621619491/50000000000000 : ℝ), (39269940781/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5192501637/10000000000 : ℝ)|^4589 ≤ (10753808136421/25000000000000 : ℝ)^3565
        have hw : |(5192501637/10000000000 : ℝ)|=(5192501637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-306856127/2500000000 : ℝ)|^4589 ≤ (3359621619491/50000000000000 : ℝ)^3565
        have hw : |(-306856127/2500000000 : ℝ)|=(306856127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2930214887/5000000000 : ℝ)|^4589 ≤ (39269940781/78125000000 : ℝ)^3565
        have hw : |(2930214887/5000000000 : ℝ)|=(2930214887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s0_6 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5192500691/10000000000 : ℝ)*x 0 + (1172086239/2000000000 : ℝ)*x 1 + (-1227423713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5192500691/10000000000 : ℝ)^4589 ≤ (5376902807239/12500000000000 : ℝ)^3565 := by
    have hnat : (5192500691 : ℕ)^4589*12500000000000^3565 ≤ 5376902807239^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192500691 10000000000 5376902807239 12500000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1172086239/2000000000 : ℝ)^4589 ≤ (50265539888611/100000000000000 : ℝ)^3565 := by
    have hnat : (1172086239 : ℕ)^4589*100000000000000^3565 ≤ 50265539888611^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1172086239 2000000000 50265539888611 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1227423713/10000000000 : ℝ)^4589 ≤ (3359618818439/50000000000000 : ℝ)^3565 := by
    have hnat : (1227423713 : ℕ)^4589*50000000000000^3565 ≤ 3359618818439^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1227423713 10000000000 3359618818439 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5192500691/10000000000 : ℝ), (1172086239/2000000000 : ℝ), (-1227423713/10000000000 : ℝ)] ![(5376902807239/12500000000000 : ℝ), (50265539888611/100000000000000 : ℝ), (3359618818439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5192500691/10000000000 : ℝ)|^4589 ≤ (5376902807239/12500000000000 : ℝ)^3565
        have hw : |(5192500691/10000000000 : ℝ)|=(5192500691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1172086239/2000000000 : ℝ)|^4589 ≤ (50265539888611/100000000000000 : ℝ)^3565
        have hw : |(1172086239/2000000000 : ℝ)|=(1172086239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1227423713/10000000000 : ℝ)|^4589 ≤ (3359618818439/50000000000000 : ℝ)^3565
        have hw : |(-1227423713/10000000000 : ℝ)|=(1227423713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s0_7 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (828724279/2000000000 : ℝ)*x 0 + (2697457853/5000000000 : ℝ)*x 1 + (126161297/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (828724279/2000000000 : ℝ)^4589 ≤ (32171955171081/100000000000000 : ℝ)^3565 := by
    have hnat : (828724279 : ℕ)^4589*100000000000000^3565 ≤ 32171955171081^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828724279 2000000000 32171955171081 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697457853/5000000000 : ℝ)^4589 ≤ (4518567090441/10000000000000 : ℝ)^3565 := by
    have hnat : (2697457853 : ℕ)^4589*10000000000000^3565 ≤ 4518567090441^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697457853 5000000000 4518567090441 10000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126161297/400000000 : ℝ)^4589 ≤ (11321186952271/50000000000000 : ℝ)^3565 := by
    have hnat : (126161297 : ℕ)^4589*50000000000000^3565 ≤ 11321186952271^3565*400000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126161297 400000000 11321186952271 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(828724279/2000000000 : ℝ), (2697457853/5000000000 : ℝ), (126161297/400000000 : ℝ)] ![(32171955171081/100000000000000 : ℝ), (4518567090441/10000000000000 : ℝ), (11321186952271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(828724279/2000000000 : ℝ)|^4589 ≤ (32171955171081/100000000000000 : ℝ)^3565
        have hw : |(828724279/2000000000 : ℝ)|=(828724279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697457853/5000000000 : ℝ)|^4589 ≤ (4518567090441/10000000000000 : ℝ)^3565
        have hw : |(2697457853/5000000000 : ℝ)|=(2697457853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(126161297/400000000 : ℝ)|^4589 ≤ (11321186952271/50000000000000 : ℝ)^3565
        have hw : |(126161297/400000000 : ℝ)|=(126161297/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1546_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (651/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25051/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4587/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4587 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4587*1^1024 ≤ 0^1024*1^4587 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4587 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4587/1024 : ℝ) ≤ (329959651111917607/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4587 ≤ (329959651111917607/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4587*20000000000000000000^1024 ≤ 329959651111917607^1024*5^4587 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 329959651111917607 20000000000000000000 4587 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (329959651111917607/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4587 := by
      have hnat : (1 : ℕ)^1024*1^4587 ≤ 1^4587*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20329959651111917607/20000000000000000000 : ℝ) ≤ (2509149080089441/2500000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (20329959651111917607/20000000000000000000 : ℝ)^1024 ≤ (2509149080089441/2500000000000000 : ℝ)^4587 := by
      have hnat : (20329959651111917607 : ℕ)^1024*2500000000000000^4587 ≤ 2509149080089441^4587*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20329959651111917607 20000000000000000000 2509149080089441 2500000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2509149080089441/2500000000000000 : ℝ)) (X := (20329959651111917607/20000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10329959651111917607/10000000000000000000 : ℝ) ≤ (1259149080089441/1250000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (10329959651111917607/10000000000000000000 : ℝ)^1024 ≤ (1259149080089441/1250000000000000 : ℝ)^4587 := by
      have hnat : (10329959651111917607 : ℕ)^1024*1250000000000000^4587 ≤ 1259149080089441^4587*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10329959651111917607 10000000000000000000 1259149080089441 1250000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1259149080089441/1250000000000000 : ℝ)) (X := (10329959651111917607/10000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9149080089441/1000000000000000 : ℝ)*(0 : ℝ))^(4587/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9149080089441/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(329959651111917607/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9149080089441/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4587/1024 : ℝ) := by
    rw [show (1 : ℝ)+(9149080089441/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2509149080089441/2500000000000000 : ℝ) by norm_num, show 1+(329959651111917607/20000000000000000000 : ℝ)+(0 : ℝ)=(20329959651111917607/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(329959651111917607/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9149080089441/1000000000000000 : ℝ)*(2/5 : ℝ))^(4587/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9149080089441/1000000000000000 : ℝ)*(2/5 : ℝ)=(1259149080089441/1250000000000000 : ℝ) by norm_num, show 1+2*(329959651111917607/20000000000000000000 : ℝ)=(10329959651111917607/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9149080089441/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9149080089441/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9149080089441/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9149080089441/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9149080089441/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9149080089441/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-825179837/5000000000 : ℝ)*X 0 0+(22996587/39062500 : ℝ)*X 0 1+(973918701/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1094124217/2000000000 : ℝ)*X 1 0+(-2218260627/10000000000 : ℝ)*X 1 1+(4869593583/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5470621001/10000000000 : ℝ)*X 2 0+(4869593541/10000000000 : ℝ)*X 2 1+(-2218260789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4136097563/10000000000 : ℝ)*X 0 0+(38650563/125000000 : ℝ)*X 0 1+(2727386549/5000000000 : ℝ)*X 0 2+(4136097563/10000000000 : ℝ)*X 1 0+(38650563/125000000 : ℝ)*X 1 1+(2727386549/5000000000 : ℝ)*X 1 2+(4136097563/10000000000 : ℝ)*X 2 0+(38650563/125000000 : ℝ)*X 2 1+(2727386549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-413400261/2500000000 : ℝ)*X 0 0+(1223842771/2500000000 : ℝ)*X 0 1+(293021503/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5192501637/10000000000 : ℝ)*X 1 0+(-306856127/2500000000 : ℝ)*X 1 1+(2930214887/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5192500691/10000000000 : ℝ)*X 2 0+(1172086239/2000000000 : ℝ)*X 2 1+(-1227423713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((828724279/2000000000 : ℝ)*X 0 0+(2697457853/5000000000 : ℝ)*X 0 1+(126161297/400000000 : ℝ)*X 0 2+(828724279/2000000000 : ℝ)*X 1 0+(2697457853/5000000000 : ℝ)*X 1 1+(126161297/400000000 : ℝ)*X 1 2+(828724279/2000000000 : ℝ)*X 2 0+(2697457853/5000000000 : ℝ)*X 2 1+(126161297/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23399513731841720913867/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31733/48828125000 : ℝ)*(base1) + (913756813/100000000000000 : ℝ)*(base19) + (224666639/25000000000000 : ℝ)*(base23) + (141269761/100000000000000 : ℝ)*(upper3) + (11171651/12500000000000 : ℝ)*(upper5) + (140601806827471/20000000000000 : ℝ)*(major0) + (140601806827471/20000000000000 : ℝ)*(major1) + (140601806827471/20000000000000 : ℝ)*(major2) + (982772633141087/100000000000000 : ℝ)*(sp0) + (982774717899141/100000000000000 : ℝ)*(sp1) + (982774732989399/100000000000000 : ℝ)*(sp2) + (211620392672667/50000000000000 : ℝ)*(sp3) + (3063504051/100000000000000 : ℝ)*(sp4) + (1430287471/100000000000000 : ℝ)*(sp7) + (423242280621989/100000000000000 : ℝ)*(f.failure) + (196555126331191/20000000000000 : ℝ)*(f.sum) + (4795946216289/10000000000000000000000000000 : ℝ)*base66 + (40233899153711/20000000000000000000000000000 : ℝ)*base67 + (173295437793711/20000000000000000000000000000 : ℝ)*base69 + (133284114393711/20000000000000000000000000000 : ℝ)*base71 + (49792278956289/10000000000000000000000000000 : ℝ)*base74 + (216519453633711/20000000000000000000000000000 : ℝ)*base75 + (12848506113711/20000000000000000000000000000 : ℝ)*base77 + (63248440933711/20000000000000000000000000000 : ℝ)*base79 + (18642174873711/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (9291343/2500000000000000000000 : ℝ)*base90 + (9291343/2500000000000000000000 : ℝ)*base92 + (9291343/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18255915742814227514493/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (467871991/100000000000000 : ℝ)*(base19) + (99594383/12500000000000 : ℝ)*(base23) + (557621609/100000000000000 : ℝ)*(base39) + (4680359/50000000000000 : ℝ)*(upper3) + (182379719/50000000000000 : ℝ)*(upper5) + (370613760647359/50000000000000 : ℝ)*(major0) + (370613760647359/50000000000000 : ℝ)*(major1) + (741226963673109/100000000000000 : ℝ)*(major2) + (390283417/25000000000000 : ℝ)*(sp1) + (499282861/50000000000000 : ℝ)*(sp2) + (518101468760559/50000000000000 : ℝ)*(sp4) + (518100454257729/50000000000000 : ℝ)*(sp5) + (51810084991097/5000000000000 : ℝ)*(sp6) + (8925029731873/2000000000000 : ℝ)*(sp7) + (8925029731873/2000000000000 : ℝ)*(f.failure) + (1036203495142727/100000000000000 : ℝ)*(f.sum) + (26809711614707/100000000000000000000000000000 : ℝ)*base65 + (1403194274657931/100000000000000000000000000000 : ℝ)*base68 + (369090363936319/50000000000000000000000000000 : ℝ)*base69 + (289066021057931/100000000000000000000000000000 : ℝ)*base72 + (598794072585293/100000000000000000000000000000 : ℝ)*base74 + (354665771136319/50000000000000000000000000000 : ℝ)*base75 + (30144279836319/50000000000000000000000000000 : ℝ)*base77 + (1571440336319/50000000000000000000000000000 : ℝ)*base79 + (66811696136319/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (213949/50000000000000000000 : ℝ)*base89 + (213949/50000000000000000000 : ℝ)*base91 + (213949/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1546_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (651/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25051/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1546_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1546_s1_0 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-22438833/125000000 : ℝ)*x 0 + (5548911247/10000000000 : ℝ)*x 1 + (19979013/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22438833/125000000 : ℝ)^4589 ≤ (10960676390683/100000000000000 : ℝ)^3565 := by
    have hnat : (22438833 : ℕ)^4589*100000000000000^3565 ≤ 10960676390683^3565*125000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22438833 125000000 10960676390683 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5548911247/10000000000 : ℝ)^4589 ≤ (23426358528567/50000000000000 : ℝ)^3565 := by
    have hnat : (5548911247 : ℕ)^4589*50000000000000^3565 ≤ 23426358528567^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5548911247 10000000000 23426358528567 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19979013/39062500 : ℝ)^4589 ≤ (21093303269607/50000000000000 : ℝ)^3565 := by
    have hnat : (19979013 : ℕ)^4589*50000000000000^3565 ≤ 21093303269607^3565*39062500^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19979013 39062500 21093303269607 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22438833/125000000 : ℝ), (5548911247/10000000000 : ℝ), (19979013/39062500 : ℝ)] ![(10960676390683/100000000000000 : ℝ), (23426358528567/50000000000000 : ℝ), (21093303269607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22438833/125000000 : ℝ)|^4589 ≤ (10960676390683/100000000000000 : ℝ)^3565
        have hw : |(-22438833/125000000 : ℝ)|=(22438833/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5548911247/10000000000 : ℝ)|^4589 ≤ (23426358528567/50000000000000 : ℝ)^3565
        have hw : |(5548911247/10000000000 : ℝ)|=(5548911247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19979013/39062500 : ℝ)|^4589 ≤ (21093303269607/50000000000000 : ℝ)^3565
        have hw : |(19979013/39062500 : ℝ)|=(19979013/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s1_1 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672569833/1250000000 : ℝ)*x 0 + (-252857993/1250000000 : ℝ)*x 1 + (255731307/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672569833/1250000000 : ℝ)^4589 ≤ (22515470645267/50000000000000 : ℝ)^3565 := by
    have hnat : (672569833 : ℕ)^4589*50000000000000^3565 ≤ 22515470645267^3565*1250000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672569833 1250000000 22515470645267 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (252857993/1250000000 : ℝ)^4589 ≤ (159780809613/1250000000000 : ℝ)^3565 := by
    have hnat : (252857993 : ℕ)^4589*1250000000000^3565 ≤ 159780809613^3565*1250000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252857993 1250000000 159780809613 1250000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (255731307/500000000 : ℝ)^4589 ≤ (10546648481429/25000000000000 : ℝ)^3565 := by
    have hnat : (255731307 : ℕ)^4589*25000000000000^3565 ≤ 10546648481429^3565*500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255731307 500000000 10546648481429 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672569833/1250000000 : ℝ), (-252857993/1250000000 : ℝ), (255731307/500000000 : ℝ)] ![(22515470645267/50000000000000 : ℝ), (159780809613/1250000000000 : ℝ), (10546648481429/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672569833/1250000000 : ℝ)|^4589 ≤ (22515470645267/50000000000000 : ℝ)^3565
        have hw : |(672569833/1250000000 : ℝ)|=(672569833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-252857993/1250000000 : ℝ)|^4589 ≤ (159780809613/1250000000000 : ℝ)^3565
        have hw : |(-252857993/1250000000 : ℝ)|=(252857993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(255731307/500000000 : ℝ)|^4589 ≤ (10546648481429/25000000000000 : ℝ)^3565
        have hw : |(255731307/500000000 : ℝ)|=(255731307/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s1_2 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345139463/2500000000 : ℝ)*x 0 + (511462677/1000000000 : ℝ)*x 1 + (-2022864197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345139463/2500000000 : ℝ)^4589 ≤ (45030932542747/100000000000000 : ℝ)^3565 := by
    have hnat : (1345139463 : ℕ)^4589*100000000000000^3565 ≤ 45030932542747^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345139463 2500000000 45030932542747 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (511462677/1000000000 : ℝ)^4589 ≤ (10546650153673/25000000000000 : ℝ)^3565 := by
    have hnat : (511462677 : ℕ)^4589*25000000000000^3565 ≤ 10546650153673^3565*1000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511462677 1000000000 10546650153673 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2022864197/10000000000 : ℝ)^4589 ≤ (12782466826953/100000000000000 : ℝ)^3565 := by
    have hnat : (2022864197 : ℕ)^4589*100000000000000^3565 ≤ 12782466826953^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022864197 10000000000 12782466826953 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345139463/2500000000 : ℝ), (511462677/1000000000 : ℝ), (-2022864197/10000000000 : ℝ)] ![(45030932542747/100000000000000 : ℝ), (10546650153673/25000000000000 : ℝ), (12782466826953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345139463/2500000000 : ℝ)|^4589 ≤ (45030932542747/100000000000000 : ℝ)^3565
        have hw : |(1345139463/2500000000 : ℝ)|=(1345139463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(511462677/1000000000 : ℝ)|^4589 ≤ (10546650153673/25000000000000 : ℝ)^3565
        have hw : |(511462677/1000000000 : ℝ)|=(511462677/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2022864197/10000000000 : ℝ)|^4589 ≤ (12782466826953/100000000000000 : ℝ)^3565
        have hw : |(-2022864197/10000000000 : ℝ)|=(2022864197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s1_3 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2118603127/5000000000 : ℝ)*x 0 + (3757644689/10000000000 : ℝ)*x 1 + (4766060283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118603127/5000000000 : ℝ)^4589 ≤ (8277573919743/25000000000000 : ℝ)^3565 := by
    have hnat : (2118603127 : ℕ)^4589*25000000000000^3565 ≤ 8277573919743^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118603127 5000000000 8277573919743 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3757644689/10000000000 : ℝ)^4589 ≤ (2836715392817/10000000000000 : ℝ)^3565 := by
    have hnat : (3757644689 : ℕ)^4589*10000000000000^3565 ≤ 2836715392817^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3757644689 10000000000 2836715392817 10000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4766060283/10000000000 : ℝ)^4589 ≤ (38522550383723/100000000000000 : ℝ)^3565 := by
    have hnat : (4766060283 : ℕ)^4589*100000000000000^3565 ≤ 38522550383723^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4766060283 10000000000 38522550383723 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2118603127/5000000000 : ℝ), (3757644689/10000000000 : ℝ), (4766060283/10000000000 : ℝ)] ![(8277573919743/25000000000000 : ℝ), (2836715392817/10000000000000 : ℝ), (38522550383723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2118603127/5000000000 : ℝ)|^4589 ≤ (8277573919743/25000000000000 : ℝ)^3565
        have hw : |(2118603127/5000000000 : ℝ)|=(2118603127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3757644689/10000000000 : ℝ)|^4589 ≤ (2836715392817/10000000000000 : ℝ)^3565
        have hw : |(3757644689/10000000000 : ℝ)|=(3757644689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4766060283/10000000000 : ℝ)|^4589 ≤ (38522550383723/100000000000000 : ℝ)^3565
        have hw : |(4766060283/10000000000 : ℝ)|=(4766060283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s1_4 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1795351993/10000000000 : ℝ)*x 0 + (5119257053/10000000000 : ℝ)*x 1 + (2772105027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1795351993/10000000000 : ℝ)^4589 ≤ (10962604827983/100000000000000 : ℝ)^3565 := by
    have hnat : (1795351993 : ℕ)^4589*100000000000000^3565 ≤ 10962604827983^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1795351993 10000000000 10962604827983 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5119257053/10000000000 : ℝ)^4589 ≤ (42235768677033/100000000000000 : ℝ)^3565 := by
    have hnat : (5119257053 : ℕ)^4589*100000000000000^3565 ≤ 42235768677033^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5119257053 10000000000 42235768677033 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2772105027/5000000000 : ℝ)^4589 ≤ (46801626486967/100000000000000 : ℝ)^3565 := by
    have hnat : (2772105027 : ℕ)^4589*100000000000000^3565 ≤ 46801626486967^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2772105027 5000000000 46801626486967 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1795351993/10000000000 : ℝ), (5119257053/10000000000 : ℝ), (2772105027/5000000000 : ℝ)] ![(10962604827983/100000000000000 : ℝ), (42235768677033/100000000000000 : ℝ), (46801626486967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1795351993/10000000000 : ℝ)|^4589 ≤ (10962604827983/100000000000000 : ℝ)^3565
        have hw : |(-1795351993/10000000000 : ℝ)|=(1795351993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5119257053/10000000000 : ℝ)|^4589 ≤ (42235768677033/100000000000000 : ℝ)^3565
        have hw : |(5119257053/10000000000 : ℝ)|=(5119257053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2772105027/5000000000 : ℝ)|^4589 ≤ (46801626486967/100000000000000 : ℝ)^3565
        have hw : |(2772105027/5000000000 : ℝ)|=(2772105027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s1_5 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5265726183/10000000000 : ℝ)*x 0 + (-1593281893/10000000000 : ℝ)*x 1 + (5544209883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265726183/10000000000 : ℝ)^4589 ≤ (43797646540771/100000000000000 : ℝ)^3565 := by
    have hnat : (5265726183 : ℕ)^4589*100000000000000^3565 ≤ 43797646540771^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265726183 10000000000 43797646540771 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1593281893/10000000000 : ℝ)^4589 ≤ (4700364408787/50000000000000 : ℝ)^3565 := by
    have hnat : (1593281893 : ℕ)^4589*50000000000000^3565 ≤ 4700364408787^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1593281893 10000000000 4700364408787 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5544209883/10000000000 : ℝ)^4589 ≤ (23400812314419/50000000000000 : ℝ)^3565 := by
    have hnat : (5544209883 : ℕ)^4589*50000000000000^3565 ≤ 23400812314419^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5544209883 10000000000 23400812314419 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265726183/10000000000 : ℝ), (-1593281893/10000000000 : ℝ), (5544209883/10000000000 : ℝ)] ![(43797646540771/100000000000000 : ℝ), (4700364408787/50000000000000 : ℝ), (23400812314419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265726183/10000000000 : ℝ)|^4589 ≤ (43797646540771/100000000000000 : ℝ)^3565
        have hw : |(5265726183/10000000000 : ℝ)|=(5265726183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1593281893/10000000000 : ℝ)|^4589 ≤ (4700364408787/50000000000000 : ℝ)^3565
        have hw : |(-1593281893/10000000000 : ℝ)|=(1593281893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5544209883/10000000000 : ℝ)|^4589 ≤ (23400812314419/50000000000000 : ℝ)^3565
        have hw : |(5544209883/10000000000 : ℝ)|=(5544209883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s1_6 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526572731/1000000000 : ℝ)*x 0 + (5544209673/10000000000 : ℝ)*x 1 + (-318656121/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526572731/1000000000 : ℝ)^4589 ≤ (21898829303547/50000000000000 : ℝ)^3565 := by
    have hnat : (526572731 : ℕ)^4589*50000000000000^3565 ≤ 21898829303547^3565*1000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526572731 1000000000 21898829303547 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5544209673/10000000000 : ℝ)^4589 ≤ (1872064893877/4000000000000 : ℝ)^3565 := by
    have hnat : (5544209673 : ℕ)^4589*4000000000000^3565 ≤ 1872064893877^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5544209673 10000000000 1872064893877 4000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318656121/2000000000 : ℝ)^4589 ≤ (9400719035223/100000000000000 : ℝ)^3565 := by
    have hnat : (318656121 : ℕ)^4589*100000000000000^3565 ≤ 9400719035223^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318656121 2000000000 9400719035223 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526572731/1000000000 : ℝ), (5544209673/10000000000 : ℝ), (-318656121/2000000000 : ℝ)] ![(21898829303547/50000000000000 : ℝ), (1872064893877/4000000000000 : ℝ), (9400719035223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526572731/1000000000 : ℝ)|^4589 ≤ (21898829303547/50000000000000 : ℝ)^3565
        have hw : |(526572731/1000000000 : ℝ)|=(526572731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5544209673/10000000000 : ℝ)|^4589 ≤ (1872064893877/4000000000000 : ℝ)^3565
        have hw : |(5544209673/10000000000 : ℝ)|=(5544209673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-318656121/2000000000 : ℝ)|^4589 ≤ (9400719035223/100000000000000 : ℝ)^3565
        have hw : |(-318656121/2000000000 : ℝ)|=(318656121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s1_7 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2118886927/5000000000 : ℝ)*x 0 + (4755307841/10000000000 : ℝ)*x 1 + (1884280591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118886927/5000000000 : ℝ)^4589 ≤ (33116005108537/100000000000000 : ℝ)^3565 := by
    have hnat : (2118886927 : ℕ)^4589*100000000000000^3565 ≤ 33116005108537^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118886927 5000000000 33116005108537 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4755307841/10000000000 : ℝ)^4589 ≤ (38410714720183/100000000000000 : ℝ)^3565 := by
    have hnat : (4755307841 : ℕ)^4589*100000000000000^3565 ≤ 38410714720183^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4755307841 10000000000 38410714720183 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1884280591/5000000000 : ℝ)^4589 ≤ (28473280162933/100000000000000 : ℝ)^3565 := by
    have hnat : (1884280591 : ℕ)^4589*100000000000000^3565 ≤ 28473280162933^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884280591 5000000000 28473280162933 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2118886927/5000000000 : ℝ), (4755307841/10000000000 : ℝ), (1884280591/5000000000 : ℝ)] ![(33116005108537/100000000000000 : ℝ), (38410714720183/100000000000000 : ℝ), (28473280162933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2118886927/5000000000 : ℝ)|^4589 ≤ (33116005108537/100000000000000 : ℝ)^3565
        have hw : |(2118886927/5000000000 : ℝ)|=(2118886927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4755307841/10000000000 : ℝ)|^4589 ≤ (38410714720183/100000000000000 : ℝ)^3565
        have hw : |(4755307841/10000000000 : ℝ)|=(4755307841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1884280591/5000000000 : ℝ)|^4589 ≤ (28473280162933/100000000000000 : ℝ)^3565
        have hw : |(1884280591/5000000000 : ℝ)|=(1884280591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1546_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (651/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (879/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8991/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (651/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (651/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (651/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (651/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (651/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (651/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (651/20000 : ℝ) ^ (4587/1024 : ℝ) ≤ (10863100507857/50000000000000000000 : ℝ) := by
    have hpowers : (651/20000 : ℝ)^4587 ≤ (10863100507857/50000000000000000000 : ℝ)^1024 := by
      have hnat : (651 : ℕ)^4587*50000000000000000000^1024 ≤ 10863100507857^1024*20000^4587 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        651 20000 10863100507857 50000000000000000000 4587 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (651/20000 : ℝ)) (X := (10863100507857/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25051/100000 : ℝ) ^ (4587/1024 : ℝ) ≤ (101393844074595697/50000000000000000000 : ℝ) := by
    have hpowers : (25051/100000 : ℝ)^4587 ≤ (101393844074595697/50000000000000000000 : ℝ)^1024 := by
      have hnat : (25051 : ℕ)^4587*50000000000000000000^1024 ≤ 101393844074595697^1024*100000^4587 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25051 100000 101393844074595697 50000000000000000000 4587 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25051/100000 : ℝ)) (X := (101393844074595697/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000010863100507857/25000000000000000000 : ℝ) ≤ (10000000970029479/10000000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (25000010863100507857/25000000000000000000 : ℝ)^1024 ≤ (10000000970029479/10000000000000000 : ℝ)^4587 := by
      have hnat : (25000010863100507857 : ℕ)^1024*10000000000000000^4587 ≤ 10000000970029479^4587*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000010863100507857 25000000000000000000 10000000970029479 10000000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000970029479/10000000000000000 : ℝ)) (X := (25000010863100507857/25000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25050702353587551777/25000000000000000000 : ℝ) ≤ (10004523947140837/10000000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (25050702353587551777/25000000000000000000 : ℝ)^1024 ≤ (10004523947140837/10000000000000000 : ℝ)^4587 := by
      have hnat : (25050702353587551777 : ℕ)^1024*10000000000000000^4587 ≤ 10004523947140837^4587*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25050702353587551777 25000000000000000000 10004523947140837 10000000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004523947140837/10000000000000000 : ℝ)) (X := (25050702353587551777/25000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25101393844074595697/25000000000000000000 : ℝ) ≤ (2001809384850439/2000000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (25101393844074595697/25000000000000000000 : ℝ)^1024 ≤ (2001809384850439/2000000000000000 : ℝ)^4587 := by
      have hnat : (25101393844074595697 : ℕ)^1024*2000000000000000^4587 ≤ 2001809384850439^4587*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25101393844074595697 25000000000000000000 2001809384850439 2000000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001809384850439/2000000000000000 : ℝ)) (X := (25101393844074595697/25000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10863100507857/50000000000000000000 : ℝ) ≤ ((27241322070220947963/27245000000000000000 : ℝ)+2*(2261488555679/1089800000000000 : ℝ)*(651/20000 : ℝ))^(4587/1024 : ℝ) := by
    rw [show (27241322070220947963/27245000000000000000 : ℝ)+2*(2261488555679/1089800000000000 : ℝ)*(651/20000 : ℝ)=(10000000970029479/10000000000000000 : ℝ) by norm_num, show 1+2*(10863100507857/50000000000000000000 : ℝ)=(25000010863100507857/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(101393844074595697/50000000000000000000 : ℝ)+(10863100507857/50000000000000000000 : ℝ) ≤ ((27241322070220947963/27245000000000000000 : ℝ)+(2261488555679/1089800000000000 : ℝ)*((25051/100000 : ℝ)+(651/20000 : ℝ)))^(4587/1024 : ℝ) := by
    rw [show (27241322070220947963/27245000000000000000 : ℝ)+(2261488555679/1089800000000000 : ℝ)*((25051/100000 : ℝ)+(651/20000 : ℝ))=(10004523947140837/10000000000000000 : ℝ) by norm_num, show 1+(101393844074595697/50000000000000000000 : ℝ)+(10863100507857/50000000000000000000 : ℝ)=(25050702353587551777/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(101393844074595697/50000000000000000000 : ℝ) ≤ ((27241322070220947963/27245000000000000000 : ℝ)+2*(2261488555679/1089800000000000 : ℝ)*(25051/100000 : ℝ))^(4587/1024 : ℝ) := by
    rw [show (27241322070220947963/27245000000000000000 : ℝ)+2*(2261488555679/1089800000000000 : ℝ)*(25051/100000 : ℝ)=(2001809384850439/2000000000000000 : ℝ) by norm_num, show 1+2*(101393844074595697/50000000000000000000 : ℝ)=(25101393844074595697/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27241322070220947963/27245000000000000000 : ℝ)*(X 1 0+X 2 0)+(2261488555679/1089800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (651/20000 : ℝ)) (hi := (25051/100000 : ℝ)) (c := (27241322070220947963/27245000000000000000 : ℝ)) (alpha := (2261488555679/1089800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27241322070220947963/27245000000000000000 : ℝ)*(X 0 1+X 2 1)+(2261488555679/1089800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (651/20000 : ℝ)) (hi := (25051/100000 : ℝ)) (c := (27241322070220947963/27245000000000000000 : ℝ)) (alpha := (2261488555679/1089800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27241322070220947963/27245000000000000000 : ℝ)*(X 0 2+X 1 2)+(2261488555679/1089800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (651/20000 : ℝ)) (hi := (25051/100000 : ℝ)) (c := (27241322070220947963/27245000000000000000 : ℝ)) (alpha := (2261488555679/1089800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-22438833/125000000 : ℝ)*X 0 0+(5548911247/10000000000 : ℝ)*X 0 1+(19979013/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((672569833/1250000000 : ℝ)*X 1 0+(-252857993/1250000000 : ℝ)*X 1 1+(255731307/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1345139463/2500000000 : ℝ)*X 2 0+(511462677/1000000000 : ℝ)*X 2 1+(-2022864197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2118603127/5000000000 : ℝ)*X 0 0+(3757644689/10000000000 : ℝ)*X 0 1+(4766060283/10000000000 : ℝ)*X 0 2+(2118603127/5000000000 : ℝ)*X 1 0+(3757644689/10000000000 : ℝ)*X 1 1+(4766060283/10000000000 : ℝ)*X 1 2+(2118603127/5000000000 : ℝ)*X 2 0+(3757644689/10000000000 : ℝ)*X 2 1+(4766060283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1795351993/10000000000 : ℝ)*X 0 0+(5119257053/10000000000 : ℝ)*X 0 1+(2772105027/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5265726183/10000000000 : ℝ)*X 1 0+(-1593281893/10000000000 : ℝ)*X 1 1+(5544209883/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((526572731/1000000000 : ℝ)*X 2 0+(5544209673/10000000000 : ℝ)*X 2 1+(-318656121/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2118886927/5000000000 : ℝ)*X 0 0+(4755307841/10000000000 : ℝ)*X 0 1+(1884280591/5000000000 : ℝ)*X 0 2+(2118886927/5000000000 : ℝ)*X 1 0+(4755307841/10000000000 : ℝ)*X 1 1+(1884280591/5000000000 : ℝ)*X 1 2+(2118886927/5000000000 : ℝ)*X 2 0+(4755307841/10000000000 : ℝ)*X 2 1+(1884280591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2163279205170065074661858457/681125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24227793/50000000000000 : ℝ)*(base1) + (76334227/12500000000000 : ℝ)*(base19) + (117690757/100000000000000 : ℝ)*(lower2) + (1383219/6250000000000 : ℝ)*(lower4) + (16740581/100000000000000 : ℝ)*(upper5) + (1647148404571387/100000000000000 : ℝ)*(major0) + (1647148404571387/100000000000000 : ℝ)*(major1) + (1647148404571387/100000000000000 : ℝ)*(major2) + (2302641149282687/100000000000000 : ℝ)*(sp0) + (460528098030657/20000000000000 : ℝ)*(sp1) + (1151318545593353/50000000000000 : ℝ)*(sp2) + (15494612848951/1562500000000 : ℝ)*(sp3) + (2004820197/50000000000000 : ℝ)*(sp6) + (331659263/100000000000000 : ℝ)*(sp7) + (198331120489543/20000000000000 : ℝ)*(f.failure) + (2302641100827101/100000000000000 : ℝ)*(f.sum) + (407134444649553/54490000000000000000000000000 : ℝ)*base65 + (18506703709549059681/2724500000000000000000000000000000 : ℝ)*base67 + (13709353580972059681/2724500000000000000000000000000000 : ℝ)*base69 + (30713741145864059681/2724500000000000000000000000000000 : ℝ)*base71 + (139796420675663/54490000000000000000000000000 : ℝ)*base73 + (1385465031145940319/2724500000000000000000000000000000 : ℝ)*base76 + (23530693855370059681/2724500000000000000000000000000000 : ℝ)*base77 + (25684752891170559681/2724500000000000000000000000000000 : ℝ)*base79 + (134905317249033/54490000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2347659/500000000000000000000 : ℝ)*base89 + (2347659/500000000000000000000 : ℝ)*base91 + (2347659/500000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (379329509757801203330211/54490000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22143923/2500000000000 : ℝ)*(base19) + (1573027737/100000000000000 : ℝ)*(base23) + (4809899/25000000000000 : ℝ)*(upper2) + (90837303/50000000000000 : ℝ)*(upper3) + (4612431/1562500000000 : ℝ)*(upper5) + (1683318265770413/100000000000000 : ℝ)*(major0) + (1683318265770413/100000000000000 : ℝ)*(major1) + (1683318265770413/100000000000000 : ℝ)*(major2) + (4021574079/100000000000000 : ℝ)*(sp1) + (5383285563/50000000000000 : ℝ)*(sp2) + (1176602426888147/50000000000000 : ℝ)*(sp4) + (470639989289059/20000000000000 : ℝ)*(sp5) + (294149064272179/12500000000000 : ℝ)*(sp6) + (253357861429033/25000000000000 : ℝ)*(sp7) + (253357861429033/25000000000000 : ℝ)*(f.failure) + (1176602426888147/50000000000000 : ℝ)*(f.sum) + (245956993076287/54490000000000000000000000000 : ℝ)*base65 + (3855078563839306281/2724500000000000000000000000000000 : ℝ)*base68 + (1556568595036306281/2724500000000000000000000000000000 : ℝ)*base70 + (1151872469073193719/2724500000000000000000000000000000 : ℝ)*base71 + (86463677329063/54490000000000000000000000000 : ℝ)*base74 + (13166586714773193719/2724500000000000000000000000000000 : ℝ)*base75 + (13020012889513693719/2724500000000000000000000000000000 : ℝ)*base77 + (40738381942402306281/2724500000000000000000000000000000 : ℝ)*base80 + (221902160005153/54490000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1540971/625000000000000000000 : ℝ)*base90 + (1540971/625000000000000000000 : ℝ)*base92 + (1540971/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1546_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (651/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (879/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8991/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1546_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1546_s2_0 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-363195661/2000000000 : ℝ)*x 0 + (5447788759/10000000000 : ℝ)*x 1 + (2601091073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (363195661/2000000000 : ℝ)^4589 ≤ (444999778539/4000000000000 : ℝ)^3565 := by
    have hnat : (363195661 : ℕ)^4589*4000000000000^3565 ≤ 444999778539^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363195661 2000000000 444999778539 4000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5447788759/10000000000 : ℝ)^4589 ≤ (45756516197051/100000000000000 : ℝ)^3565 := by
    have hnat : (5447788759 : ℕ)^4589*100000000000000^3565 ≤ 45756516197051^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447788759 10000000000 45756516197051 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2601091073/5000000000 : ℝ)^4589 ≤ (43118489322789/100000000000000 : ℝ)^3565 := by
    have hnat : (2601091073 : ℕ)^4589*100000000000000^3565 ≤ 43118489322789^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601091073 5000000000 43118489322789 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-363195661/2000000000 : ℝ), (5447788759/10000000000 : ℝ), (2601091073/5000000000 : ℝ)] ![(444999778539/4000000000000 : ℝ), (45756516197051/100000000000000 : ℝ), (43118489322789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-363195661/2000000000 : ℝ)|^4589 ≤ (444999778539/4000000000000 : ℝ)^3565
        have hw : |(-363195661/2000000000 : ℝ)|=(363195661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5447788759/10000000000 : ℝ)|^4589 ≤ (45756516197051/100000000000000 : ℝ)^3565
        have hw : |(5447788759/10000000000 : ℝ)|=(5447788759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2601091073/5000000000 : ℝ)|^4589 ≤ (43118489322789/100000000000000 : ℝ)^3565
        have hw : |(2601091073/5000000000 : ℝ)|=(2601091073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s2_1 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677303213/5000000000 : ℝ)*x 0 + (-1942178247/10000000000 : ℝ)*x 1 + (2601091203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677303213/5000000000 : ℝ)^4589 ≤ (22375774088111/50000000000000 : ℝ)^3565 := by
    have hnat : (2677303213 : ℕ)^4589*50000000000000^3565 ≤ 22375774088111^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677303213 5000000000 22375774088111 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1942178247/10000000000 : ℝ)^4589 ≤ (2425991943909/20000000000000 : ℝ)^3565 := by
    have hnat : (1942178247 : ℕ)^4589*20000000000000^3565 ≤ 2425991943909^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1942178247 10000000000 2425991943909 20000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2601091203/5000000000 : ℝ)^4589 ≤ (43118492096811/100000000000000 : ℝ)^3565 := by
    have hnat : (2601091203 : ℕ)^4589*100000000000000^3565 ≤ 43118492096811^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601091203 5000000000 43118492096811 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677303213/5000000000 : ℝ), (-1942178247/10000000000 : ℝ), (2601091203/5000000000 : ℝ)] ![(22375774088111/50000000000000 : ℝ), (2425991943909/20000000000000 : ℝ), (43118492096811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677303213/5000000000 : ℝ)|^4589 ≤ (22375774088111/50000000000000 : ℝ)^3565
        have hw : |(2677303213/5000000000 : ℝ)|=(2677303213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1942178247/10000000000 : ℝ)|^4589 ≤ (2425991943909/20000000000000 : ℝ)^3565
        have hw : |(-1942178247/10000000000 : ℝ)|=(1942178247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2601091203/5000000000 : ℝ)|^4589 ≤ (43118492096811/100000000000000 : ℝ)^3565
        have hw : |(2601091203/5000000000 : ℝ)|=(2601091203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s2_2 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354607117/10000000000 : ℝ)*x 0 + (2601090947/5000000000 : ℝ)*x 1 + (-971089001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354607117/10000000000 : ℝ)^4589 ≤ (2796972225633/6250000000000 : ℝ)^3565 := by
    have hnat : (5354607117 : ℕ)^4589*6250000000000^3565 ≤ 2796972225633^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354607117 10000000000 2796972225633 6250000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2601090947/5000000000 : ℝ)^4589 ≤ (21559243317061/50000000000000 : ℝ)^3565 := by
    have hnat : (2601090947 : ℕ)^4589*50000000000000^3565 ≤ 21559243317061^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601090947 5000000000 21559243317061 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (971089001/5000000000 : ℝ)^4589 ≤ (12129957749869/100000000000000 : ℝ)^3565 := by
    have hnat : (971089001 : ℕ)^4589*100000000000000^3565 ≤ 12129957749869^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971089001 5000000000 12129957749869 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354607117/10000000000 : ℝ), (2601090947/5000000000 : ℝ), (-971089001/5000000000 : ℝ)] ![(2796972225633/6250000000000 : ℝ), (21559243317061/50000000000000 : ℝ), (12129957749869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354607117/10000000000 : ℝ)|^4589 ≤ (2796972225633/6250000000000 : ℝ)^3565
        have hw : |(5354607117/10000000000 : ℝ)|=(5354607117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2601090947/5000000000 : ℝ)|^4589 ≤ (21559243317061/50000000000000 : ℝ)^3565
        have hw : |(2601090947/5000000000 : ℝ)|=(2601090947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-971089001/5000000000 : ℝ)|^4589 ≤ (12129957749869/100000000000000 : ℝ)^3565
        have hw : |(-971089001/5000000000 : ℝ)|=(971089001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s2_3 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4252275497/10000000000 : ℝ)*x 0 + (3975011551/10000000000 : ℝ)*x 1 + (2272657881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4252275497/10000000000 : ℝ)^4589 ≤ (1039435939731/3125000000000 : ℝ)^3565 := by
    have hnat : (4252275497 : ℕ)^4589*3125000000000^3565 ≤ 1039435939731^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252275497 10000000000 1039435939731 3125000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3975011551/10000000000 : ℝ)^4589 ≤ (15248374554211/50000000000000 : ℝ)^3565 := by
    have hnat : (3975011551 : ℕ)^4589*50000000000000^3565 ≤ 15248374554211^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3975011551 10000000000 15248374554211 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2272657881/5000000000 : ℝ)^4589 ≤ (18120650404339/50000000000000 : ℝ)^3565 := by
    have hnat : (2272657881 : ℕ)^4589*50000000000000^3565 ≤ 18120650404339^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272657881 5000000000 18120650404339 50000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4252275497/10000000000 : ℝ), (3975011551/10000000000 : ℝ), (2272657881/5000000000 : ℝ)] ![(1039435939731/3125000000000 : ℝ), (15248374554211/50000000000000 : ℝ), (18120650404339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4252275497/10000000000 : ℝ)|^4589 ≤ (1039435939731/3125000000000 : ℝ)^3565
        have hw : |(4252275497/10000000000 : ℝ)|=(4252275497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3975011551/10000000000 : ℝ)|^4589 ≤ (15248374554211/50000000000000 : ℝ)^3565
        have hw : |(3975011551/10000000000 : ℝ)|=(3975011551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2272657881/5000000000 : ℝ)|^4589 ≤ (18120650404339/50000000000000 : ℝ)^3565
        have hw : |(2272657881/5000000000 : ℝ)|=(2272657881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s2_4 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-454005509/2500000000 : ℝ)*x 0 + (1300917807/2500000000 : ℝ)*x 1 + (5446287261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (454005509/2500000000 : ℝ)^4589 ≤ (11125339320107/100000000000000 : ℝ)^3565 := by
    have hnat : (454005509 : ℕ)^4589*100000000000000^3565 ≤ 11125339320107^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454005509 2500000000 11125339320107 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1300917807/2500000000 : ℝ)^4589 ≤ (43134377459643/100000000000000 : ℝ)^3565 := by
    have hnat : (1300917807 : ℕ)^4589*100000000000000^3565 ≤ 43134377459643^3565*2500000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300917807 2500000000 43134377459643 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5446287261/10000000000 : ℝ)^4589 ≤ (45740283197347/100000000000000 : ℝ)^3565 := by
    have hnat : (5446287261 : ℕ)^4589*100000000000000^3565 ≤ 45740283197347^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446287261 10000000000 45740283197347 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-454005509/2500000000 : ℝ), (1300917807/2500000000 : ℝ), (5446287261/10000000000 : ℝ)] ![(11125339320107/100000000000000 : ℝ), (43134377459643/100000000000000 : ℝ), (45740283197347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-454005509/2500000000 : ℝ)|^4589 ≤ (11125339320107/100000000000000 : ℝ)^3565
        have hw : |(-454005509/2500000000 : ℝ)|=(454005509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1300917807/2500000000 : ℝ)|^4589 ≤ (43134377459643/100000000000000 : ℝ)^3565
        have hw : |(1300917807/2500000000 : ℝ)|=(1300917807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5446287261/10000000000 : ℝ)|^4589 ≤ (45740283197347/100000000000000 : ℝ)^3565
        have hw : |(5446287261/10000000000 : ℝ)|=(5446287261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s2_5 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661226563/1250000000 : ℝ)*x 0 + (-1698073239/10000000000 : ℝ)*x 1 + (2723143477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661226563/1250000000 : ℝ)^4589 ≤ (44055698045709/100000000000000 : ℝ)^3565 := by
    have hnat : (661226563 : ℕ)^4589*100000000000000^3565 ≤ 44055698045709^3565*1250000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661226563 1250000000 44055698045709 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1698073239/10000000000 : ℝ)^4589 ≤ (204080441159/2000000000000 : ℝ)^3565 := by
    have hnat : (1698073239 : ℕ)^4589*2000000000000^3565 ≤ 204080441159^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1698073239 10000000000 204080441159 2000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2723143477/5000000000 : ℝ)^4589 ≤ (45740279878439/100000000000000 : ℝ)^3565 := by
    have hnat : (2723143477 : ℕ)^4589*100000000000000^3565 ≤ 45740279878439^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723143477 5000000000 45740279878439 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661226563/1250000000 : ℝ), (-1698073239/10000000000 : ℝ), (2723143477/5000000000 : ℝ)] ![(44055698045709/100000000000000 : ℝ), (204080441159/2000000000000 : ℝ), (45740279878439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661226563/1250000000 : ℝ)|^4589 ≤ (44055698045709/100000000000000 : ℝ)^3565
        have hw : |(661226563/1250000000 : ℝ)|=(661226563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1698073239/10000000000 : ℝ)|^4589 ≤ (204080441159/2000000000000 : ℝ)^3565
        have hw : |(-1698073239/10000000000 : ℝ)|=(1698073239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2723143477/5000000000 : ℝ)|^4589 ≤ (45740279878439/100000000000000 : ℝ)^3565
        have hw : |(2723143477/5000000000 : ℝ)|=(2723143477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s2_6 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057962467/2000000000 : ℝ)*x 0 + (680785921/1250000000 : ℝ)*x 1 + (-339614579/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057962467/2000000000 : ℝ)^4589 ≤ (44055696233923/100000000000000 : ℝ)^3565 := by
    have hnat : (1057962467 : ℕ)^4589*100000000000000^3565 ≤ 44055696233923^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057962467 2000000000 44055696233923 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680785921/1250000000 : ℝ)^4589 ≤ (457402843541/1000000000000 : ℝ)^3565 := by
    have hnat : (680785921 : ℕ)^4589*1000000000000^3565 ≤ 457402843541^3565*1250000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680785921 1250000000 457402843541 1000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339614579/2000000000 : ℝ)^4589 ≤ (10204019397029/100000000000000 : ℝ)^3565 := by
    have hnat : (339614579 : ℕ)^4589*100000000000000^3565 ≤ 10204019397029^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339614579 2000000000 10204019397029 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057962467/2000000000 : ℝ), (680785921/1250000000 : ℝ), (-339614579/2000000000 : ℝ)] ![(44055696233923/100000000000000 : ℝ), (457402843541/1000000000000 : ℝ), (10204019397029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057962467/2000000000 : ℝ)|^4589 ≤ (44055696233923/100000000000000 : ℝ)^3565
        have hw : |(1057962467/2000000000 : ℝ)|=(1057962467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(680785921/1250000000 : ℝ)|^4589 ≤ (457402843541/1000000000000 : ℝ)^3565
        have hw : |(680785921/1250000000 : ℝ)|=(680785921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-339614579/2000000000 : ℝ)|^4589 ≤ (10204019397029/100000000000000 : ℝ)^3565
        have hw : |(-339614579/2000000000 : ℝ)|=(339614579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1546_s2_7 (p : ℝ) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2126188901/5000000000 : ℝ)*x 0 + (4541857397/10000000000 : ℝ)*x 1 + (795700111/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126188901/5000000000 : ℝ)^4589 ≤ (33262980180429/100000000000000 : ℝ)^3565 := by
    have hnat : (2126188901 : ℕ)^4589*100000000000000^3565 ≤ 33262980180429^3565*5000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126188901 5000000000 33262980180429 100000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4541857397/10000000000 : ℝ)^4589 ≤ (9051452383427/25000000000000 : ℝ)^3565 := by
    have hnat : (4541857397 : ℕ)^4589*25000000000000^3565 ≤ 9051452383427^3565*10000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4541857397 10000000000 9051452383427 25000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (795700111/2000000000 : ℝ)^4589 ≤ (1221248410681/4000000000000 : ℝ)^3565 := by
    have hnat : (795700111 : ℕ)^4589*4000000000000^3565 ≤ 1221248410681^3565*2000000000^4589 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795700111 2000000000 1221248410681 4000000000000 4589 3565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4589/1024 : ℝ)) 4589 3565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2126188901/5000000000 : ℝ), (4541857397/10000000000 : ℝ), (795700111/2000000000 : ℝ)] ![(33262980180429/100000000000000 : ℝ), (9051452383427/25000000000000 : ℝ), (1221248410681/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2126188901/5000000000 : ℝ)|^4589 ≤ (33262980180429/100000000000000 : ℝ)^3565
        have hw : |(2126188901/5000000000 : ℝ)|=(2126188901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4541857397/10000000000 : ℝ)|^4589 ≤ (9051452383427/25000000000000 : ℝ)^3565
        have hw : |(4541857397/10000000000 : ℝ)|=(4541857397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(795700111/2000000000 : ℝ)|^4589 ≤ (1221248410681/4000000000000 : ℝ)^3565
        have hw : |(795700111/2000000000 : ℝ)|=(795700111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1546_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8991/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (879/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10677/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (397/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8991/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (879/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8991/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (879/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8991/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (879/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8991/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (879/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8991/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (879/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8991/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (879/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (879/10000 : ℝ) ^ (4587/1024 : ℝ) ≤ (372080072943689/20000000000000000000 : ℝ) := by
    have hpowers : (879/10000 : ℝ)^4587 ≤ (372080072943689/20000000000000000000 : ℝ)^1024 := by
      have hnat : (879 : ℕ)^4587*20000000000000000000^1024 ≤ 372080072943689^1024*10000^4587 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        879 10000 372080072943689 20000000000000000000 4587 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (879/10000 : ℝ)) (X := (372080072943689/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8991/50000 : ℝ) ^ (4587/1024 : ℝ) ≤ (45925364584687543/100000000000000000000 : ℝ) := by
    have hpowers : (8991/50000 : ℝ)^4587 ≤ (45925364584687543/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8991 : ℕ)^4587*100000000000000000000^1024 ≤ 45925364584687543^1024*50000^4587 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8991 50000 45925364584687543 100000000000000000000 4587 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8991/50000 : ℝ)) (X := (45925364584687543/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000372080072943689/10000000000000000000 : ℝ) ≤ (10000083061802681/10000000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (10000372080072943689/10000000000000000000 : ℝ)^1024 ≤ (10000083061802681/10000000000000000 : ℝ)^4587 := by
      have hnat : (10000372080072943689 : ℕ)^1024*10000000000000000^4587 ≤ 10000083061802681^4587*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000372080072943689 10000000000000000000 10000083061802681 10000000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000083061802681/10000000000000000 : ℝ)) (X := (10000372080072943689/10000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011946441237351497/25000000000000000000 : ℝ) ≤ (10001066569532371/10000000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (25011946441237351497/25000000000000000000 : ℝ)^1024 ≤ (10001066569532371/10000000000000000 : ℝ)^4587 := by
      have hnat : (25011946441237351497 : ℕ)^1024*10000000000000000^4587 ≤ 10001066569532371^4587*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011946441237351497 25000000000000000000 10001066569532371 10000000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001066569532371/10000000000000000 : ℝ)) (X := (25011946441237351497/25000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50045925364584687543/50000000000000000000 : ℝ) ≤ (10002050077262061/10000000000000000 : ℝ) ^ (4587/1024 : ℝ) := by
    have hpowers : (50045925364584687543/50000000000000000000 : ℝ)^1024 ≤ (10002050077262061/10000000000000000 : ℝ)^4587 := by
      have hnat : (50045925364584687543 : ℕ)^1024*10000000000000000^4587 ≤ 10002050077262061^4587*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50045925364584687543 50000000000000000000 10002050077262061 10000000000000000 1024 4587 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002050077262061/10000000000000000 : ℝ)) (X := (50045925364584687543/50000000000000000000 : ℝ)) (by norm_num) 4587 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(372080072943689/20000000000000000000 : ℝ) ≤ ((1914655696629214449/1915000000000000000 : ℝ)+2*(98350772969/91920000000000 : ℝ)*(879/10000 : ℝ))^(4587/1024 : ℝ) := by
    rw [show (1914655696629214449/1915000000000000000 : ℝ)+2*(98350772969/91920000000000 : ℝ)*(879/10000 : ℝ)=(10000083061802681/10000000000000000 : ℝ) by norm_num, show 1+2*(372080072943689/20000000000000000000 : ℝ)=(10000372080072943689/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(45925364584687543/100000000000000000000 : ℝ)+(372080072943689/20000000000000000000 : ℝ) ≤ ((1914655696629214449/1915000000000000000 : ℝ)+(98350772969/91920000000000 : ℝ)*((8991/50000 : ℝ)+(879/10000 : ℝ)))^(4587/1024 : ℝ) := by
    rw [show (1914655696629214449/1915000000000000000 : ℝ)+(98350772969/91920000000000 : ℝ)*((8991/50000 : ℝ)+(879/10000 : ℝ))=(10001066569532371/10000000000000000 : ℝ) by norm_num, show 1+(45925364584687543/100000000000000000000 : ℝ)+(372080072943689/20000000000000000000 : ℝ)=(25011946441237351497/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(45925364584687543/100000000000000000000 : ℝ) ≤ ((1914655696629214449/1915000000000000000 : ℝ)+2*(98350772969/91920000000000 : ℝ)*(8991/50000 : ℝ))^(4587/1024 : ℝ) := by
    rw [show (1914655696629214449/1915000000000000000 : ℝ)+2*(98350772969/91920000000000 : ℝ)*(8991/50000 : ℝ)=(10002050077262061/10000000000000000 : ℝ) by norm_num, show 1+2*(45925364584687543/100000000000000000000 : ℝ)=(50045925364584687543/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1914655696629214449/1915000000000000000 : ℝ)*(X 1 0+X 2 0)+(98350772969/91920000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (879/10000 : ℝ)) (hi := (8991/50000 : ℝ)) (c := (1914655696629214449/1915000000000000000 : ℝ)) (alpha := (98350772969/91920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1914655696629214449/1915000000000000000 : ℝ)*(X 0 1+X 2 1)+(98350772969/91920000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (879/10000 : ℝ)) (hi := (8991/50000 : ℝ)) (c := (1914655696629214449/1915000000000000000 : ℝ)) (alpha := (98350772969/91920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1914655696629214449/1915000000000000000 : ℝ)*(X 0 2+X 1 2)+(98350772969/91920000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4587/1024 : ℝ)) (lo := (879/10000 : ℝ)) (hi := (8991/50000 : ℝ)) (c := (1914655696629214449/1915000000000000000 : ℝ)) (alpha := (98350772969/91920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-363195661/2000000000 : ℝ)*X 0 0+(5447788759/10000000000 : ℝ)*X 0 1+(2601091073/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677303213/5000000000 : ℝ)*X 1 0+(-1942178247/10000000000 : ℝ)*X 1 1+(2601091203/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354607117/10000000000 : ℝ)*X 2 0+(2601090947/5000000000 : ℝ)*X 2 1+(-971089001/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4252275497/10000000000 : ℝ)*X 0 0+(3975011551/10000000000 : ℝ)*X 0 1+(2272657881/5000000000 : ℝ)*X 0 2+(4252275497/10000000000 : ℝ)*X 1 0+(3975011551/10000000000 : ℝ)*X 1 1+(2272657881/5000000000 : ℝ)*X 1 2+(4252275497/10000000000 : ℝ)*X 2 0+(3975011551/10000000000 : ℝ)*X 2 1+(2272657881/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-454005509/2500000000 : ℝ)*X 0 0+(1300917807/2500000000 : ℝ)*X 0 1+(5446287261/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661226563/1250000000 : ℝ)*X 1 0+(-1698073239/10000000000 : ℝ)*X 1 1+(2723143477/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1057962467/2000000000 : ℝ)*X 2 0+(680785921/1250000000 : ℝ)*X 2 1+(-339614579/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2126188901/5000000000 : ℝ)*X 0 0+(4541857397/10000000000 : ℝ)*X 0 1+(795700111/2000000000 : ℝ)*X 0 2+(2126188901/5000000000 : ℝ)*X 1 0+(4541857397/10000000000 : ℝ)*X 1 1+(795700111/2000000000 : ℝ)*X 1 2+(2126188901/5000000000 : ℝ)*X 2 0+(4541857397/10000000000 : ℝ)*X 2 1+(795700111/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1546_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1012274119708472697/2393750000000000000000000 : ℝ) := by norm_num
    linear_combination (376301799/50000000000000 : ℝ)*(base19) + (84306421/10000000000000 : ℝ)*(base23) + (112156971/100000000000000 : ℝ)*(upper3) + (232907613/100000000000000 : ℝ)*(upper4) + (26253311/25000000000000 : ℝ)*(upper5) + (29125192132823/1000000000000 : ℝ)*(major0) + (29125192132823/1000000000000 : ℝ)*(major1) + (29125192132823/1000000000000 : ℝ)*(major2) + (1017889883788351/25000000000000 : ℝ)*(sp0) + (4071573316838979/100000000000000 : ℝ)*(sp1) + (4071573226378367/100000000000000 : ℝ)*(sp2) + (876728050647497/50000000000000 : ℝ)*(sp3) + (14534289173/100000000000000 : ℝ)*(sp4) + (1030216369/12500000000000 : ℝ)*(sp7) + (1753464343025947/100000000000000 : ℝ)*(f.failure) + (4071574069442577/100000000000000 : ℝ)*(f.sum) + (3671053475149/1149000000000000000000000000 : ℝ)*base65 + (22939964179306081/5745000000000000000000000000000 : ℝ)*base67 + (9979438529908919/5745000000000000000000000000000 : ℝ)*base70 + (7230712549903919/5745000000000000000000000000000 : ℝ)*base72 + (2204180861/919200000000000000000000 : ℝ)*base73 + (20485626450973919/5745000000000000000000000000000 : ℝ)*base76 + (20848785655771081/5745000000000000000000000000000 : ℝ)*base77 + (49499748260896081/5745000000000000000000000000000 : ℝ)*base79 + (3676203316129/1149000000000000000000000000 : ℝ)*base81 + (13701711/2500000000000000000000 : ℝ)*base89 + (13701711/2500000000000000000000 : ℝ)*base91 + (13701711/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (602179413395346580011589663/95750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (913635887/100000000000000 : ℝ)*(base19) + (982304129/100000000000000 : ℝ)*(base23) + (65236131/100000000000000 : ℝ)*(upper2) + (44661051/100000000000000 : ℝ)*(upper5) + (2948411474790829/100000000000000 : ℝ)*(major0) + (2948411474790829/100000000000000 : ℝ)*(major1) + (2948411474790829/100000000000000 : ℝ)*(major2) + (5313309357/100000000000000 : ℝ)*(sp0) + (17173233859/100000000000000 : ℝ)*(sp1) + (4692283783/20000000000000 : ℝ)*(sp2) + (412174436753433/10000000000000 : ℝ)*(sp4) + (206086579698697/5000000000000 : ℝ)*(sp5) + (4121725237120643/100000000000000 : ℝ)*(sp6) + (887536529550983/50000000000000 : ℝ)*(sp7) + (887536529550983/50000000000000 : ℝ)*(f.failure) + (4121749680843687/100000000000000 : ℝ)*(f.sum) + (7246923495031/4596000000000000000000000000 : ℝ)*base66 + (3615786709112722837/574500000000000000000000000000000 : ℝ)*base68 + (212554231549222837/574500000000000000000000000000000 : ℝ)*base70 + (2376383458672777163/574500000000000000000000000000000 : ℝ)*base71 + (15254638633423/4596000000000000000000000000 : ℝ)*base74 + (2069311380568222837/574500000000000000000000000000000 : ℝ)*base76 + (2758282543894222837/574500000000000000000000000000000 : ℝ)*base78 + (1354966861777777163/574500000000000000000000000000000 : ℝ)*base79 + (4479086399561/4596000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (934379/1250000000000000000000 : ℝ)*base89 + (934379/1250000000000000000000 : ℝ)*base91 + (934379/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1546_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8991/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (879/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10677/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (397/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1546_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1546_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10677/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (397/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1546_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1546_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1546_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4587/1024 : ℝ) ≤ p) (hpb : p ≤ (4589/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41525213/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10677/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (397/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1546_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
