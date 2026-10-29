-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1508_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:54:52.997471+00:00
-- url     : https://prove2.me/submissions/434a6ede-afbb-4c4d-9121-185de31f544c

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
theorem support_rectangle_w1508_s0_0 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1690084609/10000000000 : ℝ)*x 0 + (5915914857/10000000000 : ℝ)*x 1 + (2426801287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1690084609/10000000000 : ℝ)^4513 ≤ (10030078539741/100000000000000 : ℝ)^3489 := by
    have hnat : (1690084609 : ℕ)^4513*100000000000000^3489 ≤ 10030078539741^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1690084609 10000000000 10030078539741 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5915914857/10000000000 : ℝ)^4513 ≤ (50712118291011/100000000000000 : ℝ)^3489 := by
    have hnat : (5915914857 : ℕ)^4513*100000000000000^3489 ≤ 50712118291011^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5915914857 10000000000 50712118291011 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2426801287/5000000000 : ℝ)^4513 ≤ (1962890157883/5000000000000 : ℝ)^3489 := by
    have hnat : (2426801287 : ℕ)^4513*5000000000000^3489 ≤ 1962890157883^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2426801287 5000000000 1962890157883 5000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1690084609/10000000000 : ℝ), (5915914857/10000000000 : ℝ), (2426801287/5000000000 : ℝ)] ![(10030078539741/100000000000000 : ℝ), (50712118291011/100000000000000 : ℝ), (1962890157883/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1690084609/10000000000 : ℝ)|^4513 ≤ (10030078539741/100000000000000 : ℝ)^3489
        have hw : |(-1690084609/10000000000 : ℝ)|=(1690084609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5915914857/10000000000 : ℝ)|^4513 ≤ (50712118291011/100000000000000 : ℝ)^3489
        have hw : |(5915914857/10000000000 : ℝ)|=(5915914857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2426801287/5000000000 : ℝ)|^4513 ≤ (1962890157883/5000000000000 : ℝ)^3489
        have hw : |(2426801287/5000000000 : ℝ)|=(2426801287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s0_1 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5478851093/10000000000 : ℝ)*x 0 + (-571459601/2500000000 : ℝ)*x 1 + (4853602519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5478851093/10000000000 : ℝ)^4513 ≤ (45919428548413/100000000000000 : ℝ)^3489 := by
    have hnat : (5478851093 : ℕ)^4513*100000000000000^3489 ≤ 45919428548413^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478851093 10000000000 45919428548413 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (571459601/2500000000 : ℝ)^4513 ≤ (14822768852259/100000000000000 : ℝ)^3489 := by
    have hnat : (571459601 : ℕ)^4513*100000000000000^3489 ≤ 14822768852259^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571459601 2500000000 14822768852259 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4853602519/10000000000 : ℝ)^4513 ≤ (7851560516447/20000000000000 : ℝ)^3489 := by
    have hnat : (4853602519 : ℕ)^4513*20000000000000^3489 ≤ 7851560516447^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4853602519 10000000000 7851560516447 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5478851093/10000000000 : ℝ), (-571459601/2500000000 : ℝ), (4853602519/10000000000 : ℝ)] ![(45919428548413/100000000000000 : ℝ), (14822768852259/100000000000000 : ℝ), (7851560516447/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5478851093/10000000000 : ℝ)|^4513 ≤ (45919428548413/100000000000000 : ℝ)^3489
        have hw : |(5478851093/10000000000 : ℝ)|=(5478851093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-571459601/2500000000 : ℝ)|^4513 ≤ (14822768852259/100000000000000 : ℝ)^3489
        have hw : |(-571459601/2500000000 : ℝ)|=(571459601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4853602519/10000000000 : ℝ)|^4513 ≤ (7851560516447/20000000000000 : ℝ)^3489
        have hw : |(4853602519/10000000000 : ℝ)|=(4853602519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s0_2 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (85607049/156250000 : ℝ)*x 0 + (485360253/1000000000 : ℝ)*x 1 + (-457167667/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85607049/156250000 : ℝ)^4513 ≤ (22959714507289/50000000000000 : ℝ)^3489 := by
    have hnat : (85607049 : ℕ)^4513*50000000000000^3489 ≤ 22959714507289^3489*156250000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85607049 156250000 22959714507289 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (485360253/1000000000 : ℝ)^4513 ≤ (981445067433/2500000000000 : ℝ)^3489 := by
    have hnat : (485360253 : ℕ)^4513*2500000000000^3489 ≤ 981445067433^3489*1000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485360253 1000000000 981445067433 2500000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (457167667/2000000000 : ℝ)^4513 ≤ (14822768273501/100000000000000 : ℝ)^3489 := by
    have hnat : (457167667 : ℕ)^4513*100000000000000^3489 ≤ 14822768273501^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457167667 2000000000 14822768273501 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(85607049/156250000 : ℝ), (485360253/1000000000 : ℝ), (-457167667/2000000000 : ℝ)] ![(22959714507289/50000000000000 : ℝ), (981445067433/2500000000000 : ℝ), (14822768273501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(85607049/156250000 : ℝ)|^4513 ≤ (22959714507289/50000000000000 : ℝ)^3489
        have hw : |(85607049/156250000 : ℝ)|=(85607049/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(485360253/1000000000 : ℝ)|^4513 ≤ (981445067433/2500000000000 : ℝ)^3489
        have hw : |(485360253/1000000000 : ℝ)|=(485360253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-457167667/2000000000 : ℝ)|^4513 ≤ (14822768273501/100000000000000 : ℝ)^3489
        have hw : |(-457167667/2000000000 : ℝ)|=(457167667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s0_3 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2073112019/5000000000 : ℝ)*x 0 + (3091244033/10000000000 : ℝ)*x 1 + (5493339681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2073112019/5000000000 : ℝ)^4513 ≤ (32021097121919/100000000000000 : ℝ)^3489 := by
    have hnat : (2073112019 : ℕ)^4513*100000000000000^3489 ≤ 32021097121919^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073112019 5000000000 32021097121919 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091244033/10000000000 : ℝ)^4513 ≤ (1368896368087/6250000000000 : ℝ)^3489 := by
    have hnat : (3091244033 : ℕ)^4513*6250000000000^3489 ≤ 1368896368087^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091244033 10000000000 1368896368087 6250000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5493339681/10000000000 : ℝ)^4513 ≤ (23038280484737/50000000000000 : ℝ)^3489 := by
    have hnat : (5493339681 : ℕ)^4513*50000000000000^3489 ≤ 23038280484737^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493339681 10000000000 23038280484737 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2073112019/5000000000 : ℝ), (3091244033/10000000000 : ℝ), (5493339681/10000000000 : ℝ)] ![(32021097121919/100000000000000 : ℝ), (1368896368087/6250000000000 : ℝ), (23038280484737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2073112019/5000000000 : ℝ)|^4513 ≤ (32021097121919/100000000000000 : ℝ)^3489
        have hw : |(2073112019/5000000000 : ℝ)|=(2073112019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091244033/10000000000 : ℝ)|^4513 ≤ (1368896368087/6250000000000 : ℝ)^3489
        have hw : |(3091244033/10000000000 : ℝ)|=(3091244033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5493339681/10000000000 : ℝ)|^4513 ≤ (23038280484737/50000000000000 : ℝ)^3489
        have hw : |(5493339681/10000000000 : ℝ)|=(5493339681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s0_4 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-338727869/2000000000 : ℝ)*x 0 + (195228793/400000000 : ℝ)*x 1 + (5887825647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338727869/2000000000 : ℝ)^4513 ≤ (1257171837521/12500000000000 : ℝ)^3489 := by
    have hnat : (338727869 : ℕ)^4513*12500000000000^3489 ≤ 1257171837521^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338727869 2000000000 1257171837521 12500000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195228793/400000000 : ℝ)^4513 ≤ (39541743605187/100000000000000 : ℝ)^3489 := by
    have hnat : (195228793 : ℕ)^4513*100000000000000^3489 ≤ 39541743605187^3489*400000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195228793 400000000 39541743605187 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5887825647/10000000000 : ℝ)^4513 ≤ (50400881678523/100000000000000 : ℝ)^3489 := by
    have hnat : (5887825647 : ℕ)^4513*100000000000000^3489 ≤ 50400881678523^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5887825647 10000000000 50400881678523 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-338727869/2000000000 : ℝ), (195228793/400000000 : ℝ), (5887825647/10000000000 : ℝ)] ![(1257171837521/12500000000000 : ℝ), (39541743605187/100000000000000 : ℝ), (50400881678523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-338727869/2000000000 : ℝ)|^4513 ≤ (1257171837521/12500000000000 : ℝ)^3489
        have hw : |(-338727869/2000000000 : ℝ)|=(338727869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(195228793/400000000 : ℝ)|^4513 ≤ (39541743605187/100000000000000 : ℝ)^3489
        have hw : |(195228793/400000000 : ℝ)|=(195228793/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5887825647/10000000000 : ℝ)|^4513 ≤ (50400881678523/100000000000000 : ℝ)^3489
        have hw : |(5887825647/10000000000 : ℝ)|=(5887825647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s0_5 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1037726819/2000000000 : ℝ)*x 0 + (-78225953/625000000 : ℝ)*x 1 + (1177565139/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037726819/2000000000 : ℝ)^4513 ≤ (10699485103819/25000000000000 : ℝ)^3489 := by
    have hnat : (1037726819 : ℕ)^4513*25000000000000^3489 ≤ 10699485103819^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037726819 2000000000 10699485103819 25000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78225953/625000000 : ℝ)^4513 ≤ (6801177353967/100000000000000 : ℝ)^3489 := by
    have hnat : (78225953 : ℕ)^4513*100000000000000^3489 ≤ 6801177353967^3489*625000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78225953 625000000 6801177353967 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1177565139/2000000000 : ℝ)^4513 ≤ (25200441105003/50000000000000 : ℝ)^3489 := by
    have hnat : (1177565139 : ℕ)^4513*50000000000000^3489 ≤ 25200441105003^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177565139 2000000000 25200441105003 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037726819/2000000000 : ℝ), (-78225953/625000000 : ℝ), (1177565139/2000000000 : ℝ)] ![(10699485103819/25000000000000 : ℝ), (6801177353967/100000000000000 : ℝ), (25200441105003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037726819/2000000000 : ℝ)|^4513 ≤ (10699485103819/25000000000000 : ℝ)^3489
        have hw : |(1037726819/2000000000 : ℝ)|=(1037726819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-78225953/625000000 : ℝ)|^4513 ≤ (6801177353967/100000000000000 : ℝ)^3489
        have hw : |(-78225953/625000000 : ℝ)|=(78225953/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1177565139/2000000000 : ℝ)|^4513 ≤ (25200441105003/50000000000000 : ℝ)^3489
        have hw : |(1177565139/2000000000 : ℝ)|=(1177565139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s0_6 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (648579261/1250000000 : ℝ)*x 0 + (5887825711/10000000000 : ℝ)*x 1 + (-625807617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (648579261/1250000000 : ℝ)^4513 ≤ (42797940340591/100000000000000 : ℝ)^3489 := by
    have hnat : (648579261 : ℕ)^4513*100000000000000^3489 ≤ 42797940340591^3489*1250000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648579261 1250000000 42797940340591 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5887825711/10000000000 : ℝ)^4513 ≤ (25200441193583/50000000000000 : ℝ)^3489 := by
    have hnat : (5887825711 : ℕ)^4513*50000000000000^3489 ≤ 25200441193583^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5887825711 10000000000 25200441193583 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (625807617/5000000000 : ℝ)^4513 ≤ (1700294313891/25000000000000 : ℝ)^3489 := by
    have hnat : (625807617 : ℕ)^4513*25000000000000^3489 ≤ 1700294313891^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625807617 5000000000 1700294313891 25000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(648579261/1250000000 : ℝ), (5887825711/10000000000 : ℝ), (-625807617/5000000000 : ℝ)] ![(42797940340591/100000000000000 : ℝ), (25200441193583/50000000000000 : ℝ), (1700294313891/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(648579261/1250000000 : ℝ)|^4513 ≤ (42797940340591/100000000000000 : ℝ)^3489
        have hw : |(648579261/1250000000 : ℝ)|=(648579261/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5887825711/10000000000 : ℝ)|^4513 ≤ (25200441193583/50000000000000 : ℝ)^3489
        have hw : |(5887825711/10000000000 : ℝ)|=(5887825711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-625807617/5000000000 : ℝ)|^4513 ≤ (1700294313891/25000000000000 : ℝ)^3489
        have hw : |(-625807617/5000000000 : ℝ)|=(625807617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s0_7 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2077131013/5000000000 : ℝ)*x 0 + (67900277/125000000 : ℝ)*x 1 + (3154759353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2077131013/5000000000 : ℝ)^4513 ≤ (32101416185739/100000000000000 : ℝ)^3489 := by
    have hnat : (2077131013 : ℕ)^4513*100000000000000^3489 ≤ 32101416185739^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077131013 5000000000 32101416185739 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67900277/125000000 : ℝ)^4513 ≤ (45412391802673/100000000000000 : ℝ)^3489 := by
    have hnat : (67900277 : ℕ)^4513*100000000000000^3489 ≤ 45412391802673^3489*125000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67900277 125000000 45412391802673 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154759353/10000000000 : ℝ)^4513 ≤ (22486191995543/100000000000000 : ℝ)^3489 := by
    have hnat : (3154759353 : ℕ)^4513*100000000000000^3489 ≤ 22486191995543^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154759353 10000000000 22486191995543 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2077131013/5000000000 : ℝ), (67900277/125000000 : ℝ), (3154759353/10000000000 : ℝ)] ![(32101416185739/100000000000000 : ℝ), (45412391802673/100000000000000 : ℝ), (22486191995543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2077131013/5000000000 : ℝ)|^4513 ≤ (32101416185739/100000000000000 : ℝ)^3489
        have hw : |(2077131013/5000000000 : ℝ)|=(2077131013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67900277/125000000 : ℝ)|^4513 ≤ (45412391802673/100000000000000 : ℝ)^3489
        have hw : |(67900277/125000000 : ℝ)|=(67900277/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154759353/10000000000 : ℝ)|^4513 ≤ (22486191995543/100000000000000 : ℝ)^3489
        have hw : |(3154759353/10000000000 : ℝ)|=(3154759353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1508_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (347/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (798/3125 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4511/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4511 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4511*1^1024 ≤ 0^1024*1^4511 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4511 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4511/1024 : ℝ) ≤ (1765897330664928463/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4511 ≤ (1765897330664928463/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4511*100000000000000000000^1024 ≤ 1765897330664928463^1024*5^4511 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1765897330664928463 100000000000000000000 4511 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1765897330664928463/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4511 := by
      have hnat : (1 : ℕ)^1024*1^4511 ≤ 1^4511*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101765897330664928463/100000000000000000000 : ℝ) ≤ (10039815213334379/10000000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (101765897330664928463/100000000000000000000 : ℝ)^1024 ≤ (10039815213334379/10000000000000000 : ℝ)^4511 := by
      have hnat : (101765897330664928463 : ℕ)^1024*10000000000000000^4511 ≤ 10039815213334379^4511*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101765897330664928463 100000000000000000000 10039815213334379 10000000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10039815213334379/10000000000000000 : ℝ)) (X := (101765897330664928463/100000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51765897330664928463/50000000000000000000 : ℝ) ≤ (5039815213334379/5000000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (51765897330664928463/50000000000000000000 : ℝ)^1024 ≤ (5039815213334379/5000000000000000 : ℝ)^4511 := by
      have hnat : (51765897330664928463 : ℕ)^1024*5000000000000000^4511 ≤ 5039815213334379^4511*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51765897330664928463 50000000000000000000 5039815213334379 5000000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5039815213334379/5000000000000000 : ℝ)) (X := (51765897330664928463/50000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(39815213334379/4000000000000000 : ℝ)*(0 : ℝ))^(4511/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(39815213334379/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1765897330664928463/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(39815213334379/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4511/1024 : ℝ) := by
    rw [show (1 : ℝ)+(39815213334379/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10039815213334379/10000000000000000 : ℝ) by norm_num, show 1+(1765897330664928463/100000000000000000000 : ℝ)+(0 : ℝ)=(101765897330664928463/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1765897330664928463/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(39815213334379/4000000000000000 : ℝ)*(2/5 : ℝ))^(4511/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(39815213334379/4000000000000000 : ℝ)*(2/5 : ℝ)=(5039815213334379/5000000000000000 : ℝ) by norm_num, show 1+2*(1765897330664928463/100000000000000000000 : ℝ)=(51765897330664928463/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(39815213334379/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (39815213334379/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(39815213334379/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (39815213334379/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(39815213334379/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (39815213334379/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1690084609/10000000000 : ℝ)*X 0 0+(5915914857/10000000000 : ℝ)*X 0 1+(2426801287/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5478851093/10000000000 : ℝ)*X 1 0+(-571459601/2500000000 : ℝ)*X 1 1+(4853602519/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((85607049/156250000 : ℝ)*X 2 0+(485360253/1000000000 : ℝ)*X 2 1+(-457167667/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2073112019/5000000000 : ℝ)*X 0 0+(3091244033/10000000000 : ℝ)*X 0 1+(5493339681/10000000000 : ℝ)*X 0 2+(2073112019/5000000000 : ℝ)*X 1 0+(3091244033/10000000000 : ℝ)*X 1 1+(5493339681/10000000000 : ℝ)*X 1 2+(2073112019/5000000000 : ℝ)*X 2 0+(3091244033/10000000000 : ℝ)*X 2 1+(5493339681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-338727869/2000000000 : ℝ)*X 0 0+(195228793/400000000 : ℝ)*X 0 1+(5887825647/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1037726819/2000000000 : ℝ)*X 1 0+(-78225953/625000000 : ℝ)*X 1 1+(1177565139/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((648579261/1250000000 : ℝ)*X 2 0+(5887825711/10000000000 : ℝ)*X 2 1+(-625807617/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2077131013/5000000000 : ℝ)*X 0 0+(67900277/125000000 : ℝ)*X 0 1+(3154759353/10000000000 : ℝ)*X 0 2+(2077131013/5000000000 : ℝ)*X 1 0+(67900277/125000000 : ℝ)*X 1 1+(3154759353/10000000000 : ℝ)*X 1 2+(2077131013/5000000000 : ℝ)*X 2 0+(67900277/125000000 : ℝ)*X 2 1+(3154759353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6472919326484270615859/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6224127/25000000000000 : ℝ)*(base1) + (188133957/25000000000000 : ℝ)*(base19) + (37996193/5000000000000 : ℝ)*(base23) + (86113073/100000000000000 : ℝ)*(upper3) + (107815969/100000000000000 : ℝ)*(upper5) + (13576535823569/2000000000000 : ℝ)*(major0) + (13576535823569/2000000000000 : ℝ)*(major1) + (13576535823569/2000000000000 : ℝ)*(major2) + (941345225895631/100000000000000 : ℝ)*(sp0) + (941347193621421/100000000000000 : ℝ)*(sp1) + (941347186233389/100000000000000 : ℝ)*(sp2) + (208152163722041/50000000000000 : ℝ)*(sp3) + (4392253/160000000000 : ℝ)*(sp4) + (293994267/25000000000000 : ℝ)*(sp7) + (208152764158829/50000000000000 : ℝ)*(f.failure) + (941347946157249/100000000000000 : ℝ)*(f.sum) + (1327019741349/4000000000000000000000000000 : ℝ)*base66 + (6677513645349/8000000000000000000000000000 : ℝ)*base68 + (46717621141349/8000000000000000000000000000 : ℝ)*base70 + (25392862117349/8000000000000000000000000000 : ℝ)*base72 + (8143203829349/4000000000000000000000000000 : ℝ)*base74 + (48122208581349/8000000000000000000000000000 : ℝ)*base76 + (39870596125349/8000000000000000000000000000 : ℝ)*base78 + (6751563869349/8000000000000000000000000000 : ℝ)*base80 + (10622923945349/4000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (5537789/5000000000000000000000 : ℝ)*base90 + (5537789/5000000000000000000000 : ℝ)*base92 + (5537789/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1147935973176325593289323/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (128934291/10000000000000 : ℝ)*(base19) + (649389537/50000000000000 : ℝ)*(base23) + (72491097/100000000000000 : ℝ)*(base32) + (48555129/25000000000000 : ℝ)*(upper3) + (141205399/100000000000000 : ℝ)*(upper5) + (716033851529579/100000000000000 : ℝ)*(major0) + (716033851529579/100000000000000 : ℝ)*(major1) + (716033851529579/100000000000000 : ℝ)*(major2) + (823675927/25000000000000 : ℝ)*(sp1) + (3487356883/100000000000000 : ℝ)*(sp2) + (992943931571271/100000000000000 : ℝ)*(sp4) + (496469673762327/50000000000000 : ℝ)*(sp5) + (496469572717657/50000000000000 : ℝ)*(sp6) + (439123507674123/100000000000000 : ℝ)*(sp7) + (21956179008261/5000000000000 : ℝ)*(f.failure) + (992943931571271/100000000000000 : ℝ)*(f.sum) + (57973204503559/200000000000000000000000000000 : ℝ)*base66 + (61040634096441/400000000000000000000000000000 : ℝ)*base67 + (2038077966303559/400000000000000000000000000000 : ℝ)*base70 + (2371547732703559/400000000000000000000000000000 : ℝ)*base72 + (717998044896441/200000000000000000000000000000 : ℝ)*base73 + (4667053024303559/400000000000000000000000000000 : ℝ)*base76 + (210316431103559/400000000000000000000000000000 : ℝ)*base78 + (1790209233503559/400000000000000000000000000000 : ℝ)*base80 + (195158108496441/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2669099/500000000000000000000 : ℝ)*base89 + (2669099/500000000000000000000 : ℝ)*base91 + (2669099/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1508_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (347/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (798/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1508_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1508_s1_0 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1844870351/10000000000 : ℝ)*x 0 + (1393295977/2500000000 : ℝ)*x 1 + (127421687/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1844870351/10000000000 : ℝ)^4513 ≤ (11233920651571/100000000000000 : ℝ)^3489 := by
    have hnat : (1844870351 : ℕ)^4513*100000000000000^3489 ≤ 11233920651571^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844870351 10000000000 11233920651571 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1393295977/2500000000 : ℝ)^4513 ≤ (46944668802407/100000000000000 : ℝ)^3489 := by
    have hnat : (1393295977 : ℕ)^4513*100000000000000^3489 ≤ 46944668802407^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393295977 2500000000 46944668802407 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127421687/250000000 : ℝ)^4513 ≤ (41821410539947/100000000000000 : ℝ)^3489 := by
    have hnat : (127421687 : ℕ)^4513*100000000000000^3489 ≤ 41821410539947^3489*250000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127421687 250000000 41821410539947 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1844870351/10000000000 : ℝ), (1393295977/2500000000 : ℝ), (127421687/250000000 : ℝ)] ![(11233920651571/100000000000000 : ℝ), (46944668802407/100000000000000 : ℝ), (41821410539947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1844870351/10000000000 : ℝ)|^4513 ≤ (11233920651571/100000000000000 : ℝ)^3489
        have hw : |(-1844870351/10000000000 : ℝ)|=(1844870351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1393295977/2500000000 : ℝ)|^4513 ≤ (46944668802407/100000000000000 : ℝ)^3489
        have hw : |(1393295977/2500000000 : ℝ)|=(1393295977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(127421687/250000000 : ℝ)|^4513 ≤ (41821410539947/100000000000000 : ℝ)^3489
        have hw : |(127421687/250000000 : ℝ)|=(127421687/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s1_1 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5387352637/10000000000 : ℝ)*x 0 + (-1047904019/5000000000 : ℝ)*x 1 + (5096866311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387352637/10000000000 : ℝ)^4513 ≤ (44929929817737/100000000000000 : ℝ)^3489 := by
    have hnat : (5387352637 : ℕ)^4513*100000000000000^3489 ≤ 44929929817737^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387352637 10000000000 44929929817737 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047904019/5000000000 : ℝ)^4513 ≤ (13248672032739/100000000000000 : ℝ)^3489 := by
    have hnat : (1047904019 : ℕ)^4513*100000000000000^3489 ≤ 13248672032739^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047904019 5000000000 13248672032739 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5096866311/10000000000 : ℝ)^4513 ≤ (8364279626547/20000000000000 : ℝ)^3489 := by
    have hnat : (5096866311 : ℕ)^4513*20000000000000^3489 ≤ 8364279626547^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5096866311 10000000000 8364279626547 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387352637/10000000000 : ℝ), (-1047904019/5000000000 : ℝ), (5096866311/10000000000 : ℝ)] ![(44929929817737/100000000000000 : ℝ), (13248672032739/100000000000000 : ℝ), (8364279626547/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387352637/10000000000 : ℝ)|^4513 ≤ (44929929817737/100000000000000 : ℝ)^3489
        have hw : |(5387352637/10000000000 : ℝ)|=(5387352637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1047904019/5000000000 : ℝ)|^4513 ≤ (13248672032739/100000000000000 : ℝ)^3489
        have hw : |(-1047904019/5000000000 : ℝ)|=(1047904019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5096866311/10000000000 : ℝ)|^4513 ≤ (8364279626547/20000000000000 : ℝ)^3489
        have hw : |(5096866311/10000000000 : ℝ)|=(5096866311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s1_2 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5387352011/10000000000 : ℝ)*x 0 + (2548433483/5000000000 : ℝ)*x 1 + (-2095808013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387352011/10000000000 : ℝ)^4513 ≤ (44929923064701/100000000000000 : ℝ)^3489 := by
    have hnat : (5387352011 : ℕ)^4513*100000000000000^3489 ≤ 44929923064701^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387352011 10000000000 44929923064701 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2548433483/5000000000 : ℝ)^4513 ≤ (20910702542297/50000000000000 : ℝ)^3489 := by
    have hnat : (2548433483 : ℕ)^4513*50000000000000^3489 ≤ 20910702542297^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548433483 5000000000 20910702542297 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2095808013/10000000000 : ℝ)^4513 ≤ (6624335914159/50000000000000 : ℝ)^3489 := by
    have hnat : (2095808013 : ℕ)^4513*50000000000000^3489 ≤ 6624335914159^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095808013 10000000000 6624335914159 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387352011/10000000000 : ℝ), (2548433483/5000000000 : ℝ), (-2095808013/10000000000 : ℝ)] ![(44929923064701/100000000000000 : ℝ), (20910702542297/50000000000000 : ℝ), (6624335914159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387352011/10000000000 : ℝ)|^4513 ≤ (44929923064701/100000000000000 : ℝ)^3489
        have hw : |(5387352011/10000000000 : ℝ)|=(5387352011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2548433483/5000000000 : ℝ)|^4513 ≤ (20910702542297/50000000000000 : ℝ)^3489
        have hw : |(2548433483/5000000000 : ℝ)|=(2548433483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2095808013/10000000000 : ℝ)|^4513 ≤ (6624335914159/50000000000000 : ℝ)^3489
        have hw : |(-2095808013/10000000000 : ℝ)|=(2095808013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s1_3 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4251071341/10000000000 : ℝ)*x 0 + (3741443337/10000000000 : ℝ)*x 1 + (4818489783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4251071341/10000000000 : ℝ)^4513 ≤ (16536171407047/50000000000000 : ℝ)^3489 := by
    have hnat : (4251071341 : ℕ)^4513*50000000000000^3489 ≤ 16536171407047^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251071341 10000000000 16536171407047 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3741443337/10000000000 : ℝ)^4513 ≤ (5607364607473/20000000000000 : ℝ)^3489 := by
    have hnat : (3741443337 : ℕ)^4513*20000000000000^3489 ≤ 5607364607473^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3741443337 10000000000 5607364607473 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4818489783/10000000000 : ℝ)^4513 ≤ (38890834134457/100000000000000 : ℝ)^3489 := by
    have hnat : (4818489783 : ℕ)^4513*100000000000000^3489 ≤ 38890834134457^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4818489783 10000000000 38890834134457 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4251071341/10000000000 : ℝ), (3741443337/10000000000 : ℝ), (4818489783/10000000000 : ℝ)] ![(16536171407047/50000000000000 : ℝ), (5607364607473/20000000000000 : ℝ), (38890834134457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4251071341/10000000000 : ℝ)|^4513 ≤ (16536171407047/50000000000000 : ℝ)^3489
        have hw : |(4251071341/10000000000 : ℝ)|=(4251071341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3741443337/10000000000 : ℝ)|^4513 ≤ (5607364607473/20000000000000 : ℝ)^3489
        have hw : |(3741443337/10000000000 : ℝ)|=(3741443337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4818489783/10000000000 : ℝ)|^4513 ≤ (38890834134457/100000000000000 : ℝ)^3489
        have hw : |(4818489783/10000000000 : ℝ)|=(4818489783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s1_4 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1845180063/10000000000 : ℝ)*x 0 + (5102223919/10000000000 : ℝ)*x 1 + (5567740609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1845180063/10000000000 : ℝ)^4513 ≤ (1404545017383/12500000000000 : ℝ)^3489 := by
    have hnat : (1845180063 : ℕ)^4513*12500000000000^3489 ≤ 1404545017383^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845180063 10000000000 1404545017383 12500000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5102223919/10000000000 : ℝ)^4513 ≤ (523478375141/1250000000000 : ℝ)^3489 := by
    have hnat : (5102223919 : ℕ)^4513*1250000000000^3489 ≤ 523478375141^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5102223919 10000000000 523478375141 1250000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5567740609/10000000000 : ℝ)^4513 ≤ (5860671228283/12500000000000 : ℝ)^3489 := by
    have hnat : (5567740609 : ℕ)^4513*12500000000000^3489 ≤ 5860671228283^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5567740609 10000000000 5860671228283 12500000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1845180063/10000000000 : ℝ), (5102223919/10000000000 : ℝ), (5567740609/10000000000 : ℝ)] ![(1404545017383/12500000000000 : ℝ), (523478375141/1250000000000 : ℝ), (5860671228283/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1845180063/10000000000 : ℝ)|^4513 ≤ (1404545017383/12500000000000 : ℝ)^3489
        have hw : |(-1845180063/10000000000 : ℝ)|=(1845180063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5102223919/10000000000 : ℝ)|^4513 ≤ (523478375141/1250000000000 : ℝ)^3489
        have hw : |(5102223919/10000000000 : ℝ)|=(5102223919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5567740609/10000000000 : ℝ)|^4513 ≤ (5860671228283/12500000000000 : ℝ)^3489
        have hw : |(5567740609/10000000000 : ℝ)|=(5567740609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s1_5 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328872097/625000000 : ℝ)*x 0 + (-1624933789/10000000000 : ℝ)*x 1 + (5567740773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328872097/625000000 : ℝ)^4513 ≤ (10895455335567/25000000000000 : ℝ)^3489 := by
    have hnat : (328872097 : ℕ)^4513*25000000000000^3489 ≤ 10895455335567^3489*625000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328872097 625000000 10895455335567 25000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1624933789/10000000000 : ℝ)^4513 ≤ (595800439007/6250000000000 : ℝ)^3489 := by
    have hnat : (1624933789 : ℕ)^4513*6250000000000^3489 ≤ 595800439007^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1624933789 10000000000 595800439007 6250000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5567740773/10000000000 : ℝ)^4513 ≤ (23442685806307/50000000000000 : ℝ)^3489 := by
    have hnat : (5567740773 : ℕ)^4513*50000000000000^3489 ≤ 23442685806307^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5567740773 10000000000 23442685806307 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328872097/625000000 : ℝ), (-1624933789/10000000000 : ℝ), (5567740773/10000000000 : ℝ)] ![(10895455335567/25000000000000 : ℝ), (595800439007/6250000000000 : ℝ), (23442685806307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328872097/625000000 : ℝ)|^4513 ≤ (10895455335567/25000000000000 : ℝ)^3489
        have hw : |(328872097/625000000 : ℝ)|=(328872097/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1624933789/10000000000 : ℝ)|^4513 ≤ (595800439007/6250000000000 : ℝ)^3489
        have hw : |(-1624933789/10000000000 : ℝ)|=(1624933789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5567740773/10000000000 : ℝ)|^4513 ≤ (23442685806307/50000000000000 : ℝ)^3489
        have hw : |(5567740773/10000000000 : ℝ)|=(5567740773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s1_6 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2630976683/5000000000 : ℝ)*x 0 + (1391935211/2500000000 : ℝ)*x 1 + (-1624933951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2630976683/5000000000 : ℝ)^4513 ≤ (10895454837399/25000000000000 : ℝ)^3489 := by
    have hnat : (2630976683 : ℕ)^4513*25000000000000^3489 ≤ 10895454837399^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630976683 5000000000 10895454837399 25000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1391935211/2500000000 : ℝ)^4513 ≤ (46885372385973/100000000000000 : ℝ)^3489 := by
    have hnat : (1391935211 : ℕ)^4513*100000000000000^3489 ≤ 46885372385973^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1391935211 2500000000 46885372385973 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1624933951/10000000000 : ℝ)^4513 ≤ (9532808253431/100000000000000 : ℝ)^3489 := by
    have hnat : (1624933951 : ℕ)^4513*100000000000000^3489 ≤ 9532808253431^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1624933951 10000000000 9532808253431 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2630976683/5000000000 : ℝ), (1391935211/2500000000 : ℝ), (-1624933951/10000000000 : ℝ)] ![(10895454837399/25000000000000 : ℝ), (46885372385973/100000000000000 : ℝ), (9532808253431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2630976683/5000000000 : ℝ)|^4513 ≤ (10895454837399/25000000000000 : ℝ)^3489
        have hw : |(2630976683/5000000000 : ℝ)|=(2630976683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1391935211/2500000000 : ℝ)|^4513 ≤ (46885372385973/100000000000000 : ℝ)^3489
        have hw : |(1391935211/2500000000 : ℝ)|=(1391935211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1624933951/10000000000 : ℝ)|^4513 ≤ (9532808253431/100000000000000 : ℝ)^3489
        have hw : |(-1624933951/10000000000 : ℝ)|=(1624933951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s1_7 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4251771303/10000000000 : ℝ)*x 0 + (4806377321/10000000000 : ℝ)*x 1 + (150150077/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4251771303/10000000000 : ℝ)^4513 ≤ (4134923344749/12500000000000 : ℝ)^3489 := by
    have hnat : (4251771303 : ℕ)^4513*12500000000000^3489 ≤ 4134923344749^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251771303 10000000000 4134923344749 12500000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4806377321/10000000000 : ℝ)^4513 ≤ (38764426653107/100000000000000 : ℝ)^3489 := by
    have hnat : (4806377321 : ℕ)^4513*100000000000000^3489 ≤ 38764426653107^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4806377321 10000000000 38764426653107 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150150077/400000000 : ℝ)^4513 ≤ (28156186573901/100000000000000 : ℝ)^3489 := by
    have hnat : (150150077 : ℕ)^4513*100000000000000^3489 ≤ 28156186573901^3489*400000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150150077 400000000 28156186573901 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4251771303/10000000000 : ℝ), (4806377321/10000000000 : ℝ), (150150077/400000000 : ℝ)] ![(4134923344749/12500000000000 : ℝ), (38764426653107/100000000000000 : ℝ), (28156186573901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4251771303/10000000000 : ℝ)|^4513 ≤ (4134923344749/12500000000000 : ℝ)^3489
        have hw : |(4251771303/10000000000 : ℝ)|=(4251771303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4806377321/10000000000 : ℝ)|^4513 ≤ (38764426653107/100000000000000 : ℝ)^3489
        have hw : |(4806377321/10000000000 : ℝ)|=(4806377321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(150150077/400000000 : ℝ)|^4513 ≤ (28156186573901/100000000000000 : ℝ)^3489
        have hw : |(150150077/400000000 : ℝ)|=(150150077/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1508_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (798/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (347/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (4151/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2297/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (798/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (347/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (798/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (347/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (798/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (347/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (798/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (347/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (798/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (347/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (798/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (347/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (347/12500 : ℝ) ^ (4511/1024 : ℝ) ≤ (6947156877103/50000000000000000000 : ℝ) := by
    have hpowers : (347/12500 : ℝ)^4511 ≤ (6947156877103/50000000000000000000 : ℝ)^1024 := by
      have hnat : (347 : ℕ)^4511*50000000000000000000^1024 ≤ 6947156877103^1024*12500^4511 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        347 12500 6947156877103 50000000000000000000 4511 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (347/12500 : ℝ)) (X := (6947156877103/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (798/3125 : ℝ) ^ (4511/1024 : ℝ) ≤ (244537959648242641/100000000000000000000 : ℝ) := by
    have hpowers : (798/3125 : ℝ)^4511 ≤ (244537959648242641/100000000000000000000 : ℝ)^1024 := by
      have hnat : (798 : ℕ)^4511*100000000000000000000^1024 ≤ 244537959648242641^1024*3125^4511 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        798 3125 244537959648242641 100000000000000000000 4511 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (798/3125 : ℝ)) (X := (244537959648242641/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000006947156877103/25000000000000000000 : ℝ) ≤ (80000005046429/80000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (25000006947156877103/25000000000000000000 : ℝ)^1024 ≤ (80000005046429/80000000000000 : ℝ)^4511 := by
      have hnat : (25000006947156877103 : ℕ)^1024*80000000000000^4511 ≤ 80000005046429^4511*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000006947156877103 25000000000000000000 80000005046429 80000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80000005046429/80000000000000 : ℝ)) (X := (25000006947156877103/25000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100244551853961996847/100000000000000000000 : ℝ) ≤ (10005546103833533/10000000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (100244551853961996847/100000000000000000000 : ℝ)^1024 ≤ (10005546103833533/10000000000000000 : ℝ)^4511 := by
      have hnat : (100244551853961996847 : ℕ)^1024*10000000000000000^4511 ≤ 10005546103833533^4511*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100244551853961996847 100000000000000000000 10005546103833533 10000000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005546103833533/10000000000000000 : ℝ)) (X := (100244551853961996847/100000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50244537959648242641/50000000000000000000 : ℝ) ≤ (10011091576863441/10000000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (50244537959648242641/50000000000000000000 : ℝ)^1024 ≤ (10011091576863441/10000000000000000 : ℝ)^4511 := by
      have hnat : (50244537959648242641 : ℕ)^1024*10000000000000000^4511 ≤ 10011091576863441^4511*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50244537959648242641 50000000000000000000 10011091576863441 10000000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011091576863441/10000000000000000 : ℝ)) (X := (50244537959648242641/50000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6947156877103/50000000000000000000 : ℝ) ≤ ((28446153236353556973/28450000000000000000 : ℝ)+2*(1386368257477/569000000000000 : ℝ)*(347/12500 : ℝ))^(4511/1024 : ℝ) := by
    rw [show (28446153236353556973/28450000000000000000 : ℝ)+2*(1386368257477/569000000000000 : ℝ)*(347/12500 : ℝ)=(80000005046429/80000000000000 : ℝ) by norm_num, show 1+2*(6947156877103/50000000000000000000 : ℝ)=(25000006947156877103/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(244537959648242641/100000000000000000000 : ℝ)+(6947156877103/50000000000000000000 : ℝ) ≤ ((28446153236353556973/28450000000000000000 : ℝ)+(1386368257477/569000000000000 : ℝ)*((798/3125 : ℝ)+(347/12500 : ℝ)))^(4511/1024 : ℝ) := by
    rw [show (28446153236353556973/28450000000000000000 : ℝ)+(1386368257477/569000000000000 : ℝ)*((798/3125 : ℝ)+(347/12500 : ℝ))=(10005546103833533/10000000000000000 : ℝ) by norm_num, show 1+(244537959648242641/100000000000000000000 : ℝ)+(6947156877103/50000000000000000000 : ℝ)=(100244551853961996847/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(244537959648242641/100000000000000000000 : ℝ) ≤ ((28446153236353556973/28450000000000000000 : ℝ)+2*(1386368257477/569000000000000 : ℝ)*(798/3125 : ℝ))^(4511/1024 : ℝ) := by
    rw [show (28446153236353556973/28450000000000000000 : ℝ)+2*(1386368257477/569000000000000 : ℝ)*(798/3125 : ℝ)=(10011091576863441/10000000000000000 : ℝ) by norm_num, show 1+2*(244537959648242641/100000000000000000000 : ℝ)=(50244537959648242641/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28446153236353556973/28450000000000000000 : ℝ)*(X 1 0+X 2 0)+(1386368257477/569000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (347/12500 : ℝ)) (hi := (798/3125 : ℝ)) (c := (28446153236353556973/28450000000000000000 : ℝ)) (alpha := (1386368257477/569000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28446153236353556973/28450000000000000000 : ℝ)*(X 0 1+X 2 1)+(1386368257477/569000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (347/12500 : ℝ)) (hi := (798/3125 : ℝ)) (c := (28446153236353556973/28450000000000000000 : ℝ)) (alpha := (1386368257477/569000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28446153236353556973/28450000000000000000 : ℝ)*(X 0 2+X 1 2)+(1386368257477/569000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (347/12500 : ℝ)) (hi := (798/3125 : ℝ)) (c := (28446153236353556973/28450000000000000000 : ℝ)) (alpha := (1386368257477/569000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1844870351/10000000000 : ℝ)*X 0 0+(1393295977/2500000000 : ℝ)*X 0 1+(127421687/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5387352637/10000000000 : ℝ)*X 1 0+(-1047904019/5000000000 : ℝ)*X 1 1+(5096866311/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5387352011/10000000000 : ℝ)*X 2 0+(2548433483/5000000000 : ℝ)*X 2 1+(-2095808013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4251071341/10000000000 : ℝ)*X 0 0+(3741443337/10000000000 : ℝ)*X 0 1+(4818489783/10000000000 : ℝ)*X 0 2+(4251071341/10000000000 : ℝ)*X 1 0+(3741443337/10000000000 : ℝ)*X 1 1+(4818489783/10000000000 : ℝ)*X 1 2+(4251071341/10000000000 : ℝ)*X 2 0+(3741443337/10000000000 : ℝ)*X 2 1+(4818489783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1845180063/10000000000 : ℝ)*X 0 0+(5102223919/10000000000 : ℝ)*X 0 1+(5567740609/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((328872097/625000000 : ℝ)*X 1 0+(-1624933789/10000000000 : ℝ)*X 1 1+(5567740773/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2630976683/5000000000 : ℝ)*X 2 0+(1391935211/2500000000 : ℝ)*X 2 1+(-1624933951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4251771303/10000000000 : ℝ)*X 0 0+(4806377321/10000000000 : ℝ)*X 0 1+(150150077/400000000 : ℝ)*X 0 2+(4251771303/10000000000 : ℝ)*X 1 0+(4806377321/10000000000 : ℝ)*X 1 1+(150150077/400000000 : ℝ)*X 1 2+(4251771303/10000000000 : ℝ)*X 2 0+(4806377321/10000000000 : ℝ)*X 2 1+(150150077/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1391656320792883127446434129/177812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8644659/6250000000000 : ℝ)*(base1) + (746951521/50000000000000 : ℝ)*(base19) + (249990067/20000000000000 : ℝ)*(base23) + (37340011/25000000000000 : ℝ)*(upper3) + (111787403/100000000000000 : ℝ)*(upper5) + (378491194859591/25000000000000 : ℝ)*(major0) + (378491194859591/25000000000000 : ℝ)*(major1) + (378491194859591/25000000000000 : ℝ)*(major2) + (1049725704938163/50000000000000 : ℝ)*(sp0) + (2099455452159273/100000000000000 : ℝ)*(sp1) + (104972784805599/5000000000000 : ℝ)*(sp2) + (37138745521283/4000000000000 : ℝ)*(sp3) + (5674500533/100000000000000 : ℝ)*(sp4) + (1787791591/50000000000000 : ℝ)*(sp7) + (4642361759649/500000000000 : ℝ)*(f.failure) + (419891389212463/20000000000000 : ℝ)*(f.sum) + (8312837630643/7112500000000000000000000000 : ℝ)*base66 + (4750879071635671957/711250000000000000000000000000000 : ℝ)*base68 + (4743750653860671957/711250000000000000000000000000000 : ℝ)*base70 + (4173472871898171957/711250000000000000000000000000000 : ℝ)*base72 + (20972957695861/14225000000000000000000000000 : ℝ)*base74 + (5150890656353171957/711250000000000000000000000000000 : ℝ)*base76 + (383051475413078043/711250000000000000000000000000000 : ℝ)*base77 + (8530918083891921957/711250000000000000000000000000000 : ℝ)*base80 + (50979258216561/14225000000000000000000000000 : ℝ)*base82 + (135409/50000000000000000000 : ℝ)*base90 + (135409/50000000000000000000 : ℝ)*base92 + (135409/50000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6110700455452554428960362941/1422500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106079547/12500000000000 : ℝ)*(base19) + (420929151/50000000000000 : ℝ)*(base23) + (33486459/25000000000000 : ℝ)*(upper3) + (14714177/50000000000000 : ℝ)*(lower4) + (120627/390625000000 : ℝ)*(upper5) + (1549077444989687/100000000000000 : ℝ)*(major0) + (1549077444989687/100000000000000 : ℝ)*(major1) + (1549077444989687/100000000000000 : ℝ)*(major2) + (5891622237/100000000000000 : ℝ)*(sp1) + (1611680297/25000000000000 : ℝ)*(sp2) + (214814877689691/10000000000000 : ℝ)*(sp4) + (2148142036638297/100000000000000 : ℝ)*(sp5) + (107407074415871/5000000000000 : ℝ)*(sp6) + (950005969890883/100000000000000 : ℝ)*(sp7) + (950005969890883/100000000000000 : ℝ)*(f.failure) + (214814877689691/10000000000000 : ℝ)*(f.sum) + (38766571840851/28450000000000000000000000000 : ℝ)*base66 + (19689472826351887451/2845000000000000000000000000000000 : ℝ)*base67 + (3596550431311887451/2845000000000000000000000000000000 : ℝ)*base69 + (10461869727346887451/2845000000000000000000000000000000 : ℝ)*base71 + (20336001980899/28450000000000000000000000000 : ℝ)*base73 + (14548881217501887451/2845000000000000000000000000000000 : ℝ)*base75 + (14372678207971887451/2845000000000000000000000000000000 : ℝ)*base77 + (15419162541041887451/2845000000000000000000000000000000 : ℝ)*base79 + (40154041128251/28450000000000000000000000000 : ℝ)*base82 + (61722803/10000000000000000000000 : ℝ)*base90 + (61722803/10000000000000000000000 : ℝ)*base92 + (61722803/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1508_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (798/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (347/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4151/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2297/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1508_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1508_s2_0 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1869853073/10000000000 : ℝ)*x 0 + (2729604847/5000000000 : ℝ)*x 1 + (1038933201/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1869853073/10000000000 : ℝ)^4513 ≤ (11431085307477/100000000000000 : ℝ)^3489 := by
    have hnat : (1869853073 : ℕ)^4513*100000000000000^3489 ≤ 11431085307477^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869853073 10000000000 11431085307477 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2729604847/5000000000 : ℝ)^4513 ≤ (45706607277327/100000000000000 : ℝ)^3489 := by
    have hnat : (2729604847 : ℕ)^4513*100000000000000^3489 ≤ 45706607277327^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729604847 5000000000 45706607277327 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038933201/2000000000 : ℝ)^4513 ≤ (42862307390999/100000000000000 : ℝ)^3489 := by
    have hnat : (1038933201 : ℕ)^4513*100000000000000^3489 ≤ 42862307390999^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038933201 2000000000 42862307390999 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1869853073/10000000000 : ℝ), (2729604847/5000000000 : ℝ), (1038933201/2000000000 : ℝ)] ![(11431085307477/100000000000000 : ℝ), (45706607277327/100000000000000 : ℝ), (42862307390999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1869853073/10000000000 : ℝ)|^4513 ≤ (11431085307477/100000000000000 : ℝ)^3489
        have hw : |(-1869853073/10000000000 : ℝ)|=(1869853073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2729604847/5000000000 : ℝ)|^4513 ≤ (45706607277327/100000000000000 : ℝ)^3489
        have hw : |(2729604847/5000000000 : ℝ)|=(2729604847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1038933201/2000000000 : ℝ)|^4513 ≤ (42862307390999/100000000000000 : ℝ)^3489
        have hw : |(1038933201/2000000000 : ℝ)|=(1038933201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s2_1 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071685703/2000000000 : ℝ)*x 0 + (-80242711/400000000 : ℝ)*x 1 + (1038933191/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071685703/2000000000 : ℝ)^4513 ≤ (44618154199331/100000000000000 : ℝ)^3489 := by
    have hnat : (1071685703 : ℕ)^4513*100000000000000^3489 ≤ 44618154199331^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071685703 2000000000 44618154199331 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80242711/400000000 : ℝ)^4513 ≤ (6259769461803/50000000000000 : ℝ)^3489 := by
    have hnat : (80242711 : ℕ)^4513*50000000000000^3489 ≤ 6259769461803^3489*400000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80242711 400000000 6259769461803 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038933191/2000000000 : ℝ)^4513 ≤ (21431153428677/50000000000000 : ℝ)^3489 := by
    have hnat : (1038933191 : ℕ)^4513*50000000000000^3489 ≤ 21431153428677^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038933191 2000000000 21431153428677 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071685703/2000000000 : ℝ), (-80242711/400000000 : ℝ), (1038933191/2000000000 : ℝ)] ![(44618154199331/100000000000000 : ℝ), (6259769461803/50000000000000 : ℝ), (21431153428677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071685703/2000000000 : ℝ)|^4513 ≤ (44618154199331/100000000000000 : ℝ)^3489
        have hw : |(1071685703/2000000000 : ℝ)|=(1071685703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-80242711/400000000 : ℝ)|^4513 ≤ (6259769461803/50000000000000 : ℝ)^3489
        have hw : |(-80242711/400000000 : ℝ)|=(80242711/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1038933191/2000000000 : ℝ)|^4513 ≤ (21431153428677/50000000000000 : ℝ)^3489
        have hw : |(1038933191/2000000000 : ℝ)|=(1038933191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s2_2 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358428237/10000000000 : ℝ)*x 0 + (2597333057/5000000000 : ℝ)*x 1 + (-2006067937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358428237/10000000000 : ℝ)^4513 ≤ (22309075602557/50000000000000 : ℝ)^3489 := by
    have hnat : (5358428237 : ℕ)^4513*50000000000000^3489 ≤ 22309075602557^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358428237 10000000000 22309075602557 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2597333057/5000000000 : ℝ)^4513 ≤ (8572461710869/20000000000000 : ℝ)^3489 := by
    have hnat : (2597333057 : ℕ)^4513*20000000000000^3489 ≤ 8572461710869^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597333057 5000000000 8572461710869 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006067937/10000000000 : ℝ)^4513 ≤ (3129885057837/25000000000000 : ℝ)^3489 := by
    have hnat : (2006067937 : ℕ)^4513*25000000000000^3489 ≤ 3129885057837^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006067937 10000000000 3129885057837 25000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358428237/10000000000 : ℝ), (2597333057/5000000000 : ℝ), (-2006067937/10000000000 : ℝ)] ![(22309075602557/50000000000000 : ℝ), (8572461710869/20000000000000 : ℝ), (3129885057837/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358428237/10000000000 : ℝ)|^4513 ≤ (22309075602557/50000000000000 : ℝ)^3489
        have hw : |(5358428237/10000000000 : ℝ)|=(5358428237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2597333057/5000000000 : ℝ)|^4513 ≤ (8572461710869/20000000000000 : ℝ)^3489
        have hw : |(2597333057/5000000000 : ℝ)|=(2597333057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2006067937/10000000000 : ℝ)|^4513 ≤ (3129885057837/25000000000000 : ℝ)^3489
        have hw : |(-2006067937/10000000000 : ℝ)|=(2006067937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s2_3 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4268992001/10000000000 : ℝ)*x 0 + (994704081/2500000000 : ℝ)*x 1 + (457699967/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4268992001/10000000000 : ℝ)^4513 ≤ (6650558260347/20000000000000 : ℝ)^3489 := by
    have hnat : (4268992001 : ℕ)^4513*20000000000000^3489 ≤ 6650558260347^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268992001 10000000000 6650558260347 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994704081/2500000000 : ℝ)^4513 ≤ (15179383342123/50000000000000 : ℝ)^3489 := by
    have hnat : (994704081 : ℕ)^4513*50000000000000^3489 ≤ 15179383342123^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994704081 2500000000 15179383342123 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (457699967/1000000000 : ℝ)^4513 ≤ (18194220999039/50000000000000 : ℝ)^3489 := by
    have hnat : (457699967 : ℕ)^4513*50000000000000^3489 ≤ 18194220999039^3489*1000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457699967 1000000000 18194220999039 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4268992001/10000000000 : ℝ), (994704081/2500000000 : ℝ), (457699967/1000000000 : ℝ)] ![(6650558260347/20000000000000 : ℝ), (15179383342123/50000000000000 : ℝ), (18194220999039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4268992001/10000000000 : ℝ)|^4513 ≤ (6650558260347/20000000000000 : ℝ)^3489
        have hw : |(4268992001/10000000000 : ℝ)|=(4268992001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(994704081/2500000000 : ℝ)|^4513 ≤ (15179383342123/50000000000000 : ℝ)^3489
        have hw : |(994704081/2500000000 : ℝ)|=(994704081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(457699967/1000000000 : ℝ)|^4513 ≤ (18194220999039/50000000000000 : ℝ)^3489
        have hw : |(457699967/1000000000 : ℝ)|=(457699967/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s2_4 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-46747641/250000000 : ℝ)*x 0 + (5196328327/10000000000 : ℝ)*x 1 + (1091506579/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46747641/250000000 : ℝ)^4513 ≤ (1143150098767/10000000000000 : ℝ)^3489 := by
    have hnat : (46747641 : ℕ)^4513*10000000000000^3489 ≤ 1143150098767^3489*250000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46747641 250000000 1143150098767 10000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5196328327/10000000000 : ℝ)^4513 ≤ (21440025007029/50000000000000 : ℝ)^3489 := by
    have hnat : (5196328327 : ℕ)^4513*50000000000000^3489 ≤ 21440025007029^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196328327 10000000000 21440025007029 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091506579/2000000000 : ℝ)^4513 ≤ (9137689797007/20000000000000 : ℝ)^3489 := by
    have hnat : (1091506579 : ℕ)^4513*20000000000000^3489 ≤ 9137689797007^3489*2000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091506579 2000000000 9137689797007 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-46747641/250000000 : ℝ), (5196328327/10000000000 : ℝ), (1091506579/2000000000 : ℝ)] ![(1143150098767/10000000000000 : ℝ), (21440025007029/50000000000000 : ℝ), (9137689797007/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-46747641/250000000 : ℝ)|^4513 ≤ (1143150098767/10000000000000 : ℝ)^3489
        have hw : |(-46747641/250000000 : ℝ)|=(46747641/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5196328327/10000000000 : ℝ)|^4513 ≤ (21440025007029/50000000000000 : ℝ)^3489
        have hw : |(5196328327/10000000000 : ℝ)|=(5196328327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091506579/2000000000 : ℝ)|^4513 ≤ (9137689797007/20000000000000 : ℝ)^3489
        have hw : |(1091506579/2000000000 : ℝ)|=(1091506579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s2_5 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644502569/5000000000 : ℝ)*x 0 + (-87160041/500000000 : ℝ)*x 1 + (1364383473/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644502569/5000000000 : ℝ)^4513 ≤ (10967962779169/25000000000000 : ℝ)^3489 := by
    have hnat : (2644502569 : ℕ)^4513*25000000000000^3489 ≤ 10967962779169^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644502569 5000000000 10967962779169 25000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87160041/500000000 : ℝ)^4513 ≤ (10439689086037/100000000000000 : ℝ)^3489 := by
    have hnat : (87160041 : ℕ)^4513*100000000000000^3489 ≤ 10439689086037^3489*500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87160041 500000000 10439689086037 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364383473/2500000000 : ℝ)^4513 ≤ (45688459781201/100000000000000 : ℝ)^3489 := by
    have hnat : (1364383473 : ℕ)^4513*100000000000000^3489 ≤ 45688459781201^3489*2500000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364383473 2500000000 45688459781201 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644502569/5000000000 : ℝ), (-87160041/500000000 : ℝ), (1364383473/2500000000 : ℝ)] ![(10967962779169/25000000000000 : ℝ), (10439689086037/100000000000000 : ℝ), (45688459781201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644502569/5000000000 : ℝ)|^4513 ≤ (10967962779169/25000000000000 : ℝ)^3489
        have hw : |(2644502569/5000000000 : ℝ)|=(2644502569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-87160041/500000000 : ℝ)|^4513 ≤ (10439689086037/100000000000000 : ℝ)^3489
        have hw : |(-87160041/500000000 : ℝ)|=(87160041/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1364383473/2500000000 : ℝ)|^4513 ≤ (45688459781201/100000000000000 : ℝ)^3489
        have hw : |(1364383473/2500000000 : ℝ)|=(1364383473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s2_6 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289005533/10000000000 : ℝ)*x 0 + (5457533201/10000000000 : ℝ)*x 1 + (-1743201239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289005533/10000000000 : ℝ)^4513 ≤ (21935927677399/50000000000000 : ℝ)^3489 := by
    have hnat : (5289005533 : ℕ)^4513*50000000000000^3489 ≤ 21935927677399^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289005533 10000000000 21935927677399 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457533201/10000000000 : ℝ)^4513 ≤ (22844226149301/50000000000000 : ℝ)^3489 := by
    have hnat : (5457533201 : ℕ)^4513*50000000000000^3489 ≤ 22844226149301^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457533201 10000000000 22844226149301 50000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1743201239/10000000000 : ℝ)^4513 ≤ (10439692331813/100000000000000 : ℝ)^3489 := by
    have hnat : (1743201239 : ℕ)^4513*100000000000000^3489 ≤ 10439692331813^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1743201239 10000000000 10439692331813 100000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289005533/10000000000 : ℝ), (5457533201/10000000000 : ℝ), (-1743201239/10000000000 : ℝ)] ![(21935927677399/50000000000000 : ℝ), (22844226149301/50000000000000 : ℝ), (10439692331813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289005533/10000000000 : ℝ)|^4513 ≤ (21935927677399/50000000000000 : ℝ)^3489
        have hw : |(5289005533/10000000000 : ℝ)|=(5289005533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457533201/10000000000 : ℝ)|^4513 ≤ (22844226149301/50000000000000 : ℝ)^3489
        have hw : |(5457533201/10000000000 : ℝ)|=(5457533201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1743201239/10000000000 : ℝ)|^4513 ≤ (10439692331813/100000000000000 : ℝ)^3489
        have hw : |(-1743201239/10000000000 : ℝ)|=(1743201239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1508_s2_7 (p : ℝ) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2134556457/5000000000 : ℝ)*x 0 + (4573243981/10000000000 : ℝ)*x 1 + (497825647/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134556457/5000000000 : ℝ)^4513 ≤ (6650801913439/20000000000000 : ℝ)^3489 := by
    have hnat : (2134556457 : ℕ)^4513*20000000000000^3489 ≤ 6650801913439^3489*5000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134556457 5000000000 6650801913439 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4573243981/10000000000 : ℝ)^4513 ≤ (7269964897789/20000000000000 : ℝ)^3489 := by
    have hnat : (4573243981 : ℕ)^4513*20000000000000^3489 ≤ 7269964897789^3489*10000000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4573243981 10000000000 7269964897789 20000000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497825647/1250000000 : ℝ)^4513 ≤ (1899760370979/6250000000000 : ℝ)^3489 := by
    have hnat : (497825647 : ℕ)^4513*6250000000000^3489 ≤ 1899760370979^3489*1250000000^4513 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497825647 1250000000 1899760370979 6250000000000 4513 3489 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4513/1024 : ℝ)) 4513 3489 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2134556457/5000000000 : ℝ), (4573243981/10000000000 : ℝ), (497825647/1250000000 : ℝ)] ![(6650801913439/20000000000000 : ℝ), (7269964897789/20000000000000 : ℝ), (1899760370979/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2134556457/5000000000 : ℝ)|^4513 ≤ (6650801913439/20000000000000 : ℝ)^3489
        have hw : |(2134556457/5000000000 : ℝ)|=(2134556457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4573243981/10000000000 : ℝ)|^4513 ≤ (7269964897789/20000000000000 : ℝ)^3489
        have hw : |(4573243981/10000000000 : ℝ)|=(4573243981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(497825647/1250000000 : ℝ)|^4513 ≤ (1899760370979/6250000000000 : ℝ)^3489
        have hw : |(497825647/1250000000 : ℝ)|=(497825647/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1508_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2297/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4151/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10413/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4003/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2297/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4151/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2297/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4151/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2297/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4151/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2297/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4151/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2297/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4151/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2297/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4151/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4151/50000 : ℝ) ^ (4511/1024 : ℝ) ≤ (1732624237715169/100000000000000000000 : ℝ) := by
    have hpowers : (4151/50000 : ℝ)^4511 ≤ (1732624237715169/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4151 : ℕ)^4511*100000000000000000000^1024 ≤ 1732624237715169^1024*50000^4511 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4151 50000 1732624237715169 100000000000000000000 4511 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4151/50000 : ℝ)) (X := (1732624237715169/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2297/12500 : ℝ) ^ (4511/1024 : ℝ) ≤ (57388436796484413/100000000000000000000 : ℝ) := by
    have hpowers : (2297/12500 : ℝ)^4511 ≤ (57388436796484413/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2297 : ℕ)^4511*100000000000000000000^1024 ≤ 57388436796484413^1024*12500^4511 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2297 12500 57388436796484413 100000000000000000000 4511 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2297/12500 : ℝ)) (X := (57388436796484413/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001732624237715169/50000000000000000000 : ℝ) ≤ (5000039330158671/5000000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (50001732624237715169/50000000000000000000 : ℝ)^1024 ≤ (5000039330158671/5000000000000000 : ℝ)^4511 := by
      have hnat : (50001732624237715169 : ℕ)^1024*5000000000000000^4511 ≤ 5000039330158671^4511*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001732624237715169 50000000000000000000 5000039330158671 5000000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000039330158671/5000000000000000 : ℝ)) (X := (50001732624237715169/50000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50029560530517099791/50000000000000000000 : ℝ) ≤ (500067087273093/500000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (50029560530517099791/50000000000000000000 : ℝ)^1024 ≤ (500067087273093/500000000000000 : ℝ)^4511 := by
      have hnat : (50029560530517099791 : ℕ)^1024*500000000000000^4511 ≤ 500067087273093^4511*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029560530517099791 50000000000000000000 500067087273093 500000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500067087273093/500000000000000 : ℝ)) (X := (50029560530517099791/50000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50057388436796484413/50000000000000000000 : ℝ) ≤ (5001302415303189/5000000000000000 : ℝ) ^ (4511/1024 : ℝ) := by
    have hpowers : (50057388436796484413/50000000000000000000 : ℝ)^1024 ≤ (5001302415303189/5000000000000000 : ℝ)^4511 := by
      have hnat : (50057388436796484413 : ℕ)^1024*5000000000000000^4511 ≤ 5001302415303189^4511*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50057388436796484413 50000000000000000000 5001302415303189 5000000000000000 1024 4511 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001302415303189/5000000000000000 : ℝ)) (X := (50057388436796484413/50000000000000000000 : ℝ)) (by norm_num) 4511 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1732624237715169/100000000000000000000 : ℝ) ≤ ((8393318346524777203/8395000000000000000 : ℝ)+2*(210514190753/167900000000000 : ℝ)*(4151/50000 : ℝ))^(4511/1024 : ℝ) := by
    rw [show (8393318346524777203/8395000000000000000 : ℝ)+2*(210514190753/167900000000000 : ℝ)*(4151/50000 : ℝ)=(5000039330158671/5000000000000000 : ℝ) by norm_num, show 1+2*(1732624237715169/100000000000000000000 : ℝ)=(50001732624237715169/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(57388436796484413/100000000000000000000 : ℝ)+(1732624237715169/100000000000000000000 : ℝ) ≤ ((8393318346524777203/8395000000000000000 : ℝ)+(210514190753/167900000000000 : ℝ)*((2297/12500 : ℝ)+(4151/50000 : ℝ)))^(4511/1024 : ℝ) := by
    rw [show (8393318346524777203/8395000000000000000 : ℝ)+(210514190753/167900000000000 : ℝ)*((2297/12500 : ℝ)+(4151/50000 : ℝ))=(500067087273093/500000000000000 : ℝ) by norm_num, show 1+(57388436796484413/100000000000000000000 : ℝ)+(1732624237715169/100000000000000000000 : ℝ)=(50029560530517099791/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(57388436796484413/100000000000000000000 : ℝ) ≤ ((8393318346524777203/8395000000000000000 : ℝ)+2*(210514190753/167900000000000 : ℝ)*(2297/12500 : ℝ))^(4511/1024 : ℝ) := by
    rw [show (8393318346524777203/8395000000000000000 : ℝ)+2*(210514190753/167900000000000 : ℝ)*(2297/12500 : ℝ)=(5001302415303189/5000000000000000 : ℝ) by norm_num, show 1+2*(57388436796484413/100000000000000000000 : ℝ)=(50057388436796484413/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8393318346524777203/8395000000000000000 : ℝ)*(X 1 0+X 2 0)+(210514190753/167900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (4151/50000 : ℝ)) (hi := (2297/12500 : ℝ)) (c := (8393318346524777203/8395000000000000000 : ℝ)) (alpha := (210514190753/167900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8393318346524777203/8395000000000000000 : ℝ)*(X 0 1+X 2 1)+(210514190753/167900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (4151/50000 : ℝ)) (hi := (2297/12500 : ℝ)) (c := (8393318346524777203/8395000000000000000 : ℝ)) (alpha := (210514190753/167900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8393318346524777203/8395000000000000000 : ℝ)*(X 0 2+X 1 2)+(210514190753/167900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4511/1024 : ℝ)) (lo := (4151/50000 : ℝ)) (hi := (2297/12500 : ℝ)) (c := (8393318346524777203/8395000000000000000 : ℝ)) (alpha := (210514190753/167900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1869853073/10000000000 : ℝ)*X 0 0+(2729604847/5000000000 : ℝ)*X 0 1+(1038933201/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071685703/2000000000 : ℝ)*X 1 0+(-80242711/400000000 : ℝ)*X 1 1+(1038933191/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5358428237/10000000000 : ℝ)*X 2 0+(2597333057/5000000000 : ℝ)*X 2 1+(-2006067937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4268992001/10000000000 : ℝ)*X 0 0+(994704081/2500000000 : ℝ)*X 0 1+(457699967/1000000000 : ℝ)*X 0 2+(4268992001/10000000000 : ℝ)*X 1 0+(994704081/2500000000 : ℝ)*X 1 1+(457699967/1000000000 : ℝ)*X 1 2+(4268992001/10000000000 : ℝ)*X 2 0+(994704081/2500000000 : ℝ)*X 2 1+(457699967/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-46747641/250000000 : ℝ)*X 0 0+(5196328327/10000000000 : ℝ)*X 0 1+(1091506579/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644502569/5000000000 : ℝ)*X 1 0+(-87160041/500000000 : ℝ)*X 1 1+(1364383473/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289005533/10000000000 : ℝ)*X 2 0+(5457533201/10000000000 : ℝ)*X 2 1+(-1743201239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2134556457/5000000000 : ℝ)*X 0 0+(4573243981/10000000000 : ℝ)*X 0 1+(497825647/1250000000 : ℝ)*X 0 2+(2134556457/5000000000 : ℝ)*X 1 0+(4573243981/10000000000 : ℝ)*X 1 1+(497825647/1250000000 : ℝ)*X 1 2+(2134556457/5000000000 : ℝ)*X 2 0+(4573243981/10000000000 : ℝ)*X 2 1+(497825647/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1508_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8503358275035873174686997/4562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (455089641/100000000000000 : ℝ)*(base19) + (311179067/100000000000000 : ℝ)*(base23) + (5092729/12500000000000 : ℝ)*(upper3) + (4635301/12500000000000 : ℝ)*(lower4) + (1362959716458441/50000000000000 : ℝ)*(major0) + (1362959716458441/50000000000000 : ℝ)*(major1) + (1362959716458441/50000000000000 : ℝ)*(major2) + (3780102432145557/100000000000000 : ℝ)*(sp0) + (1890054013697837/50000000000000 : ℝ)*(sp1) + (3780106859220597/100000000000000 : ℝ)*(sp2) + (1671729405687721/100000000000000 : ℝ)*(sp3) + (3025169879/50000000000000 : ℝ)*(sp4) + (328021413/25000000000000 : ℝ)*(sp6) + (57220983/6250000000000 : ℝ)*(sp7) + (1671730321223449/100000000000000 : ℝ)*(f.failure) + (945027120621329/25000000000000 : ℝ)*(f.sum) + (16752267374997/4197500000000000000000000000 : ℝ)*base66 + (2580651378516370523/419750000000000000000000000000000 : ℝ)*base67 + (4859539526825620523/419750000000000000000000000000000 : ℝ)*base69 + (2149236514683120523/419750000000000000000000000000000 : ℝ)*base71 + (2189926815693/1049375000000000000000000000 : ℝ)*base74 + (2479116509694370523/419750000000000000000000000000000 : ℝ)*base75 + (795347205256870523/419750000000000000000000000000000 : ℝ)*base77 + (596573917682129477/419750000000000000000000000000000 : ℝ)*base80 + (14786614346651/8395000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (20911209/10000000000000000000000 : ℝ)*base90 + (20911209/10000000000000000000000 : ℝ)*base92 + (20911209/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5021116541423718685583658099/419750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8122331/3125000000000 : ℝ)*(base19) + (309915479/20000000000000 : ℝ)*(base23) + (349211669/100000000000000 : ℝ)*(upper3) + (447215509/100000000000000 : ℝ)*(lower4) + (690186555501403/25000000000000 : ℝ)*(major0) + (690186555501403/25000000000000 : ℝ)*(major1) + (2760746222005613/100000000000000 : ℝ)*(major2) + (1145407671/20000000000000 : ℝ)*(sp1) + (8889380813/50000000000000 : ℝ)*(sp2) + (241465739/10000000000000 : ℝ)*(sp3) + (382840342614513/10000000000000 : ℝ)*(sp4) + (3828397439192183/100000000000000 : ℝ)*(sp5) + (957096024451527/25000000000000 : ℝ)*(sp6) + (1693086204470039/100000000000000 : ℝ)*(sp7) + (423272154781857/25000000000000 : ℝ)*(f.failure) + (382840342614513/10000000000000 : ℝ)*(f.sum) + (11781212512803/3358000000000000000000000000 : ℝ)*base66 + (3017709880212596691/209875000000000000000000000000000 : ℝ)*base68 + (833737371429240439/839500000000000000000000000000000 : ℝ)*base69 + (2523482165649346691/209875000000000000000000000000000 : ℝ)*base72 + (7120750418887/3358000000000000000000000000 : ℝ)*base74 + (6288288795644740439/839500000000000000000000000000000 : ℝ)*base75 + (2030073998422884191/209875000000000000000000000000000 : ℝ)*base78 + (1279267746171759191/209875000000000000000000000000000 : ℝ)*base80 + (5034404290607/4197500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (7537/2500000000000000000000 : ℝ)*base90 + (7537/2500000000000000000000 : ℝ)*base92 + (25007537/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1508_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2297/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4151/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10413/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4003/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1508_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1508_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10413/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4003/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1508_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1508_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1508_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4511/1024 : ℝ) ≤ p) (hpb : p ≤ (4513/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163059759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10413/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4003/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1508_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
