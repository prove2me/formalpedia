-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1487_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:14:55.076116+00:00
-- url     : https://prove2.me/submissions/d72f7cc0-5edd-4167-b2be-518938df5c38

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
theorem support_rectangle_w1487_s6_0 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1905591557/10000000000 : ℝ)*x 0 + (1359126757/2500000000 : ℝ)*x 1 + (208650753/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1905591557/10000000000 : ℝ)^4471 ≤ (2329047440443/20000000000000 : ℝ)^3447 := by
    have hnat : (1905591557 : ℕ)^4471*20000000000000^3447 ≤ 2329047440443^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1905591557 10000000000 2329047440443 20000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359126757/2500000000 : ℝ)^4471 ≤ (45361924847583/100000000000000 : ℝ)^3447 := by
    have hnat : (1359126757 : ℕ)^4471*100000000000000^3447 ≤ 45361924847583^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359126757 2500000000 45361924847583 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208650753/400000000 : ℝ)^4471 ≤ (5374104742209/12500000000000 : ℝ)^3447 := by
    have hnat : (208650753 : ℕ)^4471*12500000000000^3447 ≤ 5374104742209^3447*400000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208650753 400000000 5374104742209 12500000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1905591557/10000000000 : ℝ), (1359126757/2500000000 : ℝ), (208650753/400000000 : ℝ)] ![(2329047440443/20000000000000 : ℝ), (45361924847583/100000000000000 : ℝ), (5374104742209/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1905591557/10000000000 : ℝ)|^4471 ≤ (2329047440443/20000000000000 : ℝ)^3447
        have hw : |(-1905591557/10000000000 : ℝ)|=(1905591557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359126757/2500000000 : ℝ)|^4471 ≤ (45361924847583/100000000000000 : ℝ)^3447
        have hw : |(1359126757/2500000000 : ℝ)|=(1359126757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208650753/400000000 : ℝ)|^4471 ≤ (5374104742209/12500000000000 : ℝ)^3447
        have hw : |(208650753/400000000 : ℝ)|=(208650753/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s6_1 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338236061/2500000000 : ℝ)*x 0 + (-31538213/156250000 : ℝ)*x 1 + (163008401/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338236061/2500000000 : ℝ)^4471 ≤ (44459623634089/100000000000000 : ℝ)^3447 := by
    have hnat : (1338236061 : ℕ)^4471*100000000000000^3447 ≤ 44459623634089^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338236061 2500000000 44459623634089 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31538213/156250000 : ℝ)^4471 ≤ (12547538335049/100000000000000 : ℝ)^3447 := by
    have hnat : (31538213 : ℕ)^4471*100000000000000^3447 ≤ 12547538335049^3447*156250000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31538213 156250000 12547538335049 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163008401/312500000 : ℝ)^4471 ≤ (21496419006253/50000000000000 : ℝ)^3447 := by
    have hnat : (163008401 : ℕ)^4471*50000000000000^3447 ≤ 21496419006253^3447*312500000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163008401 312500000 21496419006253 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338236061/2500000000 : ℝ), (-31538213/156250000 : ℝ), (163008401/312500000 : ℝ)] ![(44459623634089/100000000000000 : ℝ), (12547538335049/100000000000000 : ℝ), (21496419006253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338236061/2500000000 : ℝ)|^4471 ≤ (44459623634089/100000000000000 : ℝ)^3447
        have hw : |(1338236061/2500000000 : ℝ)|=(1338236061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-31538213/156250000 : ℝ)|^4471 ≤ (12547538335049/100000000000000 : ℝ)^3447
        have hw : |(-31538213/156250000 : ℝ)|=(31538213/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163008401/312500000 : ℝ)|^4471 ≤ (21496419006253/50000000000000 : ℝ)^3447
        have hw : |(163008401/312500000 : ℝ)|=(163008401/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s6_2 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352944231/10000000000 : ℝ)*x 0 + (130406721/250000000 : ℝ)*x 1 + (-50461141/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352944231/10000000000 : ℝ)^4471 ≤ (1111490587351/2500000000000 : ℝ)^3447 := by
    have hnat : (5352944231 : ℕ)^4471*2500000000000^3447 ≤ 1111490587351^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352944231 10000000000 1111490587351 2500000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130406721/250000000 : ℝ)^4471 ≤ (4299283809803/10000000000000 : ℝ)^3447 := by
    have hnat : (130406721 : ℕ)^4471*10000000000000^3447 ≤ 4299283809803^3447*250000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130406721 250000000 4299283809803 10000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50461141/250000000 : ℝ)^4471 ≤ (6273769199777/50000000000000 : ℝ)^3447 := by
    have hnat : (50461141 : ℕ)^4471*50000000000000^3447 ≤ 6273769199777^3447*250000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50461141 250000000 6273769199777 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352944231/10000000000 : ℝ), (130406721/250000000 : ℝ), (-50461141/250000000 : ℝ)] ![(1111490587351/2500000000000 : ℝ), (4299283809803/10000000000000 : ℝ), (6273769199777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352944231/10000000000 : ℝ)|^4471 ≤ (1111490587351/2500000000000 : ℝ)^3447
        have hw : |(5352944231/10000000000 : ℝ)|=(5352944231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130406721/250000000 : ℝ)|^4471 ≤ (4299283809803/10000000000000 : ℝ)^3447
        have hw : |(130406721/250000000 : ℝ)|=(130406721/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-50461141/250000000 : ℝ)|^4471 ≤ (6273769199777/50000000000000 : ℝ)^3447
        have hw : |(-50461141/250000000 : ℝ)|=(50461141/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s6_3 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2140779073/5000000000 : ℝ)*x 0 + (4042338883/10000000000 : ℝ)*x 1 + (4532962793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140779073/5000000000 : ℝ)^4471 ≤ (16639177022967/50000000000000 : ℝ)^3447 := by
    have hnat : (2140779073 : ℕ)^4471*50000000000000^3447 ≤ 16639177022967^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140779073 5000000000 16639177022967 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4042338883/10000000000 : ℝ)^4471 ≤ (24709566201/80000000000 : ℝ)^3447 := by
    have hnat : (4042338883 : ℕ)^4471*80000000000^3447 ≤ 24709566201^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4042338883 10000000000 24709566201 80000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4532962793/10000000000 : ℝ)^4471 ≤ (35834688187157/100000000000000 : ℝ)^3447 := by
    have hnat : (4532962793 : ℕ)^4471*100000000000000^3447 ≤ 35834688187157^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532962793 10000000000 35834688187157 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2140779073/5000000000 : ℝ), (4042338883/10000000000 : ℝ), (4532962793/10000000000 : ℝ)] ![(16639177022967/50000000000000 : ℝ), (24709566201/80000000000 : ℝ), (35834688187157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2140779073/5000000000 : ℝ)|^4471 ≤ (16639177022967/50000000000000 : ℝ)^3447
        have hw : |(2140779073/5000000000 : ℝ)|=(2140779073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4042338883/10000000000 : ℝ)|^4471 ≤ (24709566201/80000000000 : ℝ)^3447
        have hw : |(4042338883/10000000000 : ℝ)|=(4042338883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4532962793/10000000000 : ℝ)|^4471 ≤ (35834688187157/100000000000000 : ℝ)^3447
        have hw : |(4532962793/10000000000 : ℝ)|=(4532962793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s6_4 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2382027/12500000 : ℝ)*x 0 + (2608698503/5000000000 : ℝ)*x 1 + (1358842637/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2382027/12500000 : ℝ)^4471 ≤ (5822737669427/50000000000000 : ℝ)^3447 := by
    have hnat : (2382027 : ℕ)^4471*50000000000000^3447 ≤ 5822737669427^3447*12500000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2382027 12500000 5822737669427 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608698503/5000000000 : ℝ)^4471 ≤ (21502449593113/50000000000000 : ℝ)^3447 := by
    have hnat : (2608698503 : ℕ)^4471*50000000000000^3447 ≤ 21502449593113^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608698503 5000000000 21502449593113 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358842637/2500000000 : ℝ)^4471 ≤ (5668703183451/12500000000000 : ℝ)^3447 := by
    have hnat : (1358842637 : ℕ)^4471*12500000000000^3447 ≤ 5668703183451^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358842637 2500000000 5668703183451 12500000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2382027/12500000 : ℝ), (2608698503/5000000000 : ℝ), (1358842637/2500000000 : ℝ)] ![(5822737669427/50000000000000 : ℝ), (21502449593113/50000000000000 : ℝ), (5668703183451/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2382027/12500000 : ℝ)|^4471 ≤ (5822737669427/50000000000000 : ℝ)^3447
        have hw : |(-2382027/12500000 : ℝ)|=(2382027/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608698503/5000000000 : ℝ)|^4471 ≤ (21502449593113/50000000000000 : ℝ)^3447
        have hw : |(2608698503/5000000000 : ℝ)|=(2608698503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358842637/2500000000 : ℝ)|^4471 ≤ (5668703183451/12500000000000 : ℝ)^3447
        have hw : |(1358842637/2500000000 : ℝ)|=(1358842637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s6_5 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323839523/2500000000 : ℝ)*x 0 + (-71973757/400000000 : ℝ)*x 1 + (2717685271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323839523/2500000000 : ℝ)^4471 ≤ (43840242138469/100000000000000 : ℝ)^3447 := by
    have hnat : (1323839523 : ℕ)^4471*100000000000000^3447 ≤ 43840242138469^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323839523 2500000000 43840242138469 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71973757/400000000 : ℝ)^4471 ≤ (1351266554713/12500000000000 : ℝ)^3447 := by
    have hnat : (71973757 : ℕ)^4471*12500000000000^3447 ≤ 1351266554713^3447*400000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71973757 400000000 1351266554713 12500000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717685271/5000000000 : ℝ)^4471 ≤ (11337406350669/25000000000000 : ℝ)^3447 := by
    have hnat : (2717685271 : ℕ)^4471*25000000000000^3447 ≤ 11337406350669^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717685271 5000000000 11337406350669 25000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323839523/2500000000 : ℝ), (-71973757/400000000 : ℝ), (2717685271/5000000000 : ℝ)] ![(43840242138469/100000000000000 : ℝ), (1351266554713/12500000000000 : ℝ), (11337406350669/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323839523/2500000000 : ℝ)|^4471 ≤ (43840242138469/100000000000000 : ℝ)^3447
        have hw : |(1323839523/2500000000 : ℝ)|=(1323839523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-71973757/400000000 : ℝ)|^4471 ≤ (1351266554713/12500000000000 : ℝ)^3447
        have hw : |(-71973757/400000000 : ℝ)|=(71973757/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717685271/5000000000 : ℝ)|^4471 ≤ (11337406350669/25000000000000 : ℝ)^3447
        have hw : |(2717685271/5000000000 : ℝ)|=(2717685271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s6_6 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059071619/2000000000 : ℝ)*x 0 + (1087074109/2000000000 : ℝ)*x 1 + (-1799343917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059071619/2000000000 : ℝ)^4471 ≤ (10960060542671/25000000000000 : ℝ)^3447 := by
    have hnat : (1059071619 : ℕ)^4471*25000000000000^3447 ≤ 10960060542671^3447*2000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059071619 2000000000 10960060542671 25000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087074109/2000000000 : ℝ)^4471 ≤ (22674812717571/50000000000000 : ℝ)^3447 := by
    have hnat : (1087074109 : ℕ)^4471*50000000000000^3447 ≤ 22674812717571^3447*2000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087074109 2000000000 22674812717571 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1799343917/10000000000 : ℝ)^4471 ≤ (10810132375363/100000000000000 : ℝ)^3447 := by
    have hnat : (1799343917 : ℕ)^4471*100000000000000^3447 ≤ 10810132375363^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799343917 10000000000 10810132375363 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059071619/2000000000 : ℝ), (1087074109/2000000000 : ℝ), (-1799343917/10000000000 : ℝ)] ![(10960060542671/25000000000000 : ℝ), (22674812717571/50000000000000 : ℝ), (10810132375363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059071619/2000000000 : ℝ)|^4471 ≤ (10960060542671/25000000000000 : ℝ)^3447
        have hw : |(1059071619/2000000000 : ℝ)|=(1059071619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087074109/2000000000 : ℝ)|^4471 ≤ (22674812717571/50000000000000 : ℝ)^3447
        have hw : |(1087074109/2000000000 : ℝ)|=(1087074109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1799343917/10000000000 : ℝ)|^4471 ≤ (10810132375363/100000000000000 : ℝ)^3447
        have hw : |(-1799343917/10000000000 : ℝ)|=(1799343917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s6_7 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4281625067/10000000000 : ℝ)*x 0 + (2265224773/5000000000 : ℝ)*x 1 + (808974121/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4281625067/10000000000 : ℝ)^4471 ≤ (16639514354401/50000000000000 : ℝ)^3447 := by
    have hnat : (4281625067 : ℕ)^4471*50000000000000^3447 ≤ 16639514354401^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4281625067 10000000000 16639514354401 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2265224773/5000000000 : ℝ)^4471 ≤ (8952229994113/25000000000000 : ℝ)^3447 := by
    have hnat : (2265224773 : ℕ)^4471*25000000000000^3447 ≤ 8952229994113^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265224773 5000000000 8952229994113 25000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (808974121/2000000000 : ℝ)^4471 ≤ (15456025653657/50000000000000 : ℝ)^3447 := by
    have hnat : (808974121 : ℕ)^4471*50000000000000^3447 ≤ 15456025653657^3447*2000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808974121 2000000000 15456025653657 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4281625067/10000000000 : ℝ), (2265224773/5000000000 : ℝ), (808974121/2000000000 : ℝ)] ![(16639514354401/50000000000000 : ℝ), (8952229994113/25000000000000 : ℝ), (15456025653657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4281625067/10000000000 : ℝ)|^4471 ≤ (16639514354401/50000000000000 : ℝ)^3447
        have hw : |(4281625067/10000000000 : ℝ)|=(4281625067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2265224773/5000000000 : ℝ)|^4471 ≤ (8952229994113/25000000000000 : ℝ)^3447
        have hw : |(2265224773/5000000000 : ℝ)|=(2265224773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(808974121/2000000000 : ℝ)|^4471 ≤ (15456025653657/50000000000000 : ℝ)^3447
        have hw : |(808974121/2000000000 : ℝ)|=(808974121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1487_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80692417/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2163/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15477/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5407/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5407/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5407/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5407/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5407/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5407/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5407/50000 : ℝ) ^ (4469/1024 : ℝ) ≤ (608229454194459/10000000000000000000 : ℝ) := by
    have hpowers : (5407/50000 : ℝ)^4469 ≤ (608229454194459/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5407 : ℕ)^4469*10000000000000000000^1024 ≤ 608229454194459^1024*50000^4469 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5407 50000 608229454194459 10000000000000000000 4469 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5407/50000 : ℝ)) (X := (608229454194459/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15479/100000 : ℝ) ^ (4469/1024 : ℝ) ≤ (2909572090927021/10000000000000000000 : ℝ) := by
    have hpowers : (15479/100000 : ℝ)^4469 ≤ (2909572090927021/10000000000000000000 : ℝ)^1024 := by
      have hnat : (15479 : ℕ)^4469*10000000000000000000^1024 ≤ 2909572090927021^1024*100000^4469 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15479 100000 2909572090927021 10000000000000000000 4469 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15479/100000 : ℝ)) (X := (2909572090927021/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000608229454194459/5000000000000000000 : ℝ) ≤ (10000278719069643/10000000000000000 : ℝ) ^ (4469/1024 : ℝ) := by
    have hpowers : (5000608229454194459/5000000000000000000 : ℝ)^1024 ≤ (10000278719069643/10000000000000000 : ℝ)^4469 := by
      have hnat : (5000608229454194459 : ℕ)^1024*10000000000000000^4469 ≤ 10000278719069643^4469*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000608229454194459 5000000000000000000 10000278719069643 10000000000000000 1024 4469 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000278719069643/10000000000000000 : ℝ)) (X := (5000608229454194459/5000000000000000000 : ℝ)) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (250087945038628037/250000000000000000 : ℝ) ≤ (10000805938792969/10000000000000000 : ℝ) ^ (4469/1024 : ℝ) := by
    have hpowers : (250087945038628037/250000000000000000 : ℝ)^1024 ≤ (10000805938792969/10000000000000000 : ℝ)^4469 := by
      have hnat : (250087945038628037 : ℕ)^1024*10000000000000000^4469 ≤ 10000805938792969^4469*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250087945038628037 250000000000000000 10000805938792969 10000000000000000 1024 4469 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000805938792969/10000000000000000 : ℝ)) (X := (250087945038628037/250000000000000000 : ℝ)) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002909572090927021/5000000000000000000 : ℝ) ≤ (2000266631703259/2000000000000000 : ℝ) ^ (4469/1024 : ℝ) := by
    have hpowers : (5002909572090927021/5000000000000000000 : ℝ)^1024 ≤ (2000266631703259/2000000000000000 : ℝ)^4469 := by
      have hnat : (5002909572090927021 : ℕ)^1024*2000000000000000^4469 ≤ 2000266631703259^4469*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002909572090927021 5000000000000000000 2000266631703259 2000000000000000 1024 4469 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000266631703259/2000000000000000 : ℝ)) (X := (5002909572090927021/5000000000000000000 : ℝ)) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(608229454194459/10000000000000000000 : ℝ) ≤ ((46639897516283789867/46650000000000000000 : ℝ)+2*(263609861663/233250000000000 : ℝ)*(5407/50000 : ℝ))^(4469/1024 : ℝ) := by
    rw [show (46639897516283789867/46650000000000000000 : ℝ)+2*(263609861663/233250000000000 : ℝ)*(5407/50000 : ℝ)=(10000278719069643/10000000000000000 : ℝ) by norm_num, show 1+2*(608229454194459/10000000000000000000 : ℝ)=(5000608229454194459/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2909572090927021/10000000000000000000 : ℝ)+(608229454194459/10000000000000000000 : ℝ) ≤ ((46639897516283789867/46650000000000000000 : ℝ)+(263609861663/233250000000000 : ℝ)*((15479/100000 : ℝ)+(5407/50000 : ℝ)))^(4469/1024 : ℝ) := by
    rw [show (46639897516283789867/46650000000000000000 : ℝ)+(263609861663/233250000000000 : ℝ)*((15479/100000 : ℝ)+(5407/50000 : ℝ))=(10000805938792969/10000000000000000 : ℝ) by norm_num, show 1+(2909572090927021/10000000000000000000 : ℝ)+(608229454194459/10000000000000000000 : ℝ)=(250087945038628037/250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2909572090927021/10000000000000000000 : ℝ) ≤ ((46639897516283789867/46650000000000000000 : ℝ)+2*(263609861663/233250000000000 : ℝ)*(15479/100000 : ℝ))^(4469/1024 : ℝ) := by
    rw [show (46639897516283789867/46650000000000000000 : ℝ)+2*(263609861663/233250000000000 : ℝ)*(15479/100000 : ℝ)=(2000266631703259/2000000000000000 : ℝ) by norm_num, show 1+2*(2909572090927021/10000000000000000000 : ℝ)=(5002909572090927021/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46639897516283789867/46650000000000000000 : ℝ)*(X 1 0+X 2 0)+(263609861663/233250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4469/1024 : ℝ)) (lo := (5407/50000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (46639897516283789867/46650000000000000000 : ℝ)) (alpha := (263609861663/233250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46639897516283789867/46650000000000000000 : ℝ)*(X 0 1+X 2 1)+(263609861663/233250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4469/1024 : ℝ)) (lo := (5407/50000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (46639897516283789867/46650000000000000000 : ℝ)) (alpha := (263609861663/233250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46639897516283789867/46650000000000000000 : ℝ)*(X 0 2+X 1 2)+(263609861663/233250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4469/1024 : ℝ)) (lo := (5407/50000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (46639897516283789867/46650000000000000000 : ℝ)) (alpha := (263609861663/233250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1905591557/10000000000 : ℝ)*X 0 0+(1359126757/2500000000 : ℝ)*X 0 1+(208650753/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338236061/2500000000 : ℝ)*X 1 0+(-31538213/156250000 : ℝ)*X 1 1+(163008401/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352944231/10000000000 : ℝ)*X 2 0+(130406721/250000000 : ℝ)*X 2 1+(-50461141/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2140779073/5000000000 : ℝ)*X 0 0+(4042338883/10000000000 : ℝ)*X 0 1+(4532962793/10000000000 : ℝ)*X 0 2+(2140779073/5000000000 : ℝ)*X 1 0+(4042338883/10000000000 : ℝ)*X 1 1+(4532962793/10000000000 : ℝ)*X 1 2+(2140779073/5000000000 : ℝ)*X 2 0+(4042338883/10000000000 : ℝ)*X 2 1+(4532962793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2382027/12500000 : ℝ)*X 0 0+(2608698503/5000000000 : ℝ)*X 0 1+(1358842637/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323839523/2500000000 : ℝ)*X 1 0+(-71973757/400000000 : ℝ)*X 1 1+(2717685271/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1059071619/2000000000 : ℝ)*X 2 0+(1087074109/2000000000 : ℝ)*X 2 1+(-1799343917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4281625067/10000000000 : ℝ)*X 0 0+(2265224773/5000000000 : ℝ)*X 0 1+(808974121/2000000000 : ℝ)*X 0 2+(4281625067/10000000000 : ℝ)*X 1 0+(2265224773/5000000000 : ℝ)*X 1 1+(808974121/2000000000 : ℝ)*X 1 2+(4281625067/10000000000 : ℝ)*X 2 0+(2265224773/5000000000 : ℝ)*X 2 1+(808974121/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4591596318488242338507573641/388750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1046496717/50000000000000 : ℝ)*(base19) + (1934760563/100000000000000 : ℝ)*(base23) + (78798391/100000000000000 : ℝ)*(lower2) + (300972369/100000000000000 : ℝ)*(upper3) + (45927437/25000000000000 : ℝ)*(upper5) + (3289427746660123/100000000000000 : ℝ)*(major0) + (3289427746660123/100000000000000 : ℝ)*(major1) + (3289427746660123/100000000000000 : ℝ)*(major2) + (4540572146627609/100000000000000 : ℝ)*(sp0) + (1418938174741/31250000000 : ℝ)*(sp1) + (567575289675509/12500000000000 : ℝ)*(sp2) + (254779381795719/12500000000000 : ℝ)*(sp3) + (16052768513/50000000000000 : ℝ)*(sp4) + (3948270961/25000000000000 : ℝ)*(sp7) + (509562711862399/25000000000000 : ℝ)*(f.failure) + (908120850432927/20000000000000 : ℝ)*(f.sum) + (32075238786823/23325000000000000000000000000 : ℝ)*base65 + (21404170961425323/5000000000000000000000000000000 : ℝ)*base68 + (56374773866425323/5000000000000000000000000000000 : ℝ)*base70 + (18082451421425323/5000000000000000000000000000000 : ℝ)*base72 + (52297597104451/11662500000000000000000000000 : ℝ)*base74 + (48839532498574677/5000000000000000000000000000000 : ℝ)*base75 + (24371130581425323/5000000000000000000000000000000 : ℝ)*base78 + (32208352321425323/5000000000000000000000000000000 : ℝ)*base80 + (73944986551801/11662500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (9228383/1250000000000000000000 : ℝ)*base89 + (9228383/1250000000000000000000 : ℝ)*base91 + (9228383/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1832962167161524303642613481/388750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (774237373/100000000000000 : ℝ)*(base19) + (851050333/100000000000000 : ℝ)*(base23) + (63117581/25000000000000 : ℝ)*(lower1) + (2454693/2500000000000 : ℝ)*(upper3) + (2036373/6250000000000 : ℝ)*(lower4) + (24338059/25000000000000 : ℝ)*(upper5) + (1661773207787643/50000000000000 : ℝ)*(major0) + (1661773207787643/50000000000000 : ℝ)*(major1) + (1661773207787643/50000000000000 : ℝ)*(major2) + (1166416859/100000000000000 : ℝ)*(sp2) + (4587700639924409/100000000000000 : ℝ)*(sp4) + (1146924966421759/25000000000000 : ℝ)*(sp5) + (4587698622457217/100000000000000 : ℝ)*(sp6) + (1029696017029483/50000000000000 : ℝ)*(sp7) + (1029696017029483/50000000000000 : ℝ)*(f.failure) + (4587700639924409/100000000000000 : ℝ)*(f.sum) + (20693449393431/3887500000000000000000000000 : ℝ)*base65 + (44355459953599157/2500000000000000000000000000000 : ℝ)*base67 + (23841919226400843/2500000000000000000000000000000 : ℝ)*base70 + (216029092093599157/2500000000000000000000000000000 : ℝ)*base71 + (1697023952003/1943750000000000000000000000 : ℝ)*base73 + (214943887676400843/2500000000000000000000000000000 : ℝ)*base76 + (8808949736400843/2500000000000000000000000000000 : ℝ)*base78 + (13829358473900843/2500000000000000000000000000000 : ℝ)*base80 + (14071112895637/7775000000000000000000000000 : ℝ)*base81 + (6469589/2500000000000000000000 : ℝ)*base90 + (6469589/2500000000000000000000 : ℝ)*base92 + (6469589/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1487_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80692417/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2163/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1487_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1487_s7_0 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-95279749/500000000 : ℝ)*x 0 + (84945251/156250000 : ℝ)*x 1 + (2608138693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (95279749/500000000 : ℝ)^4471 ≤ (11645264334659/100000000000000 : ℝ)^3447 := by
    have hnat : (95279749 : ℕ)^4471*100000000000000^3447 ≤ 11645264334659^3447*500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95279749 500000000 11645264334659 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84945251/156250000 : ℝ)^4471 ≤ (45361806187731/100000000000000 : ℝ)^3447 := by
    have hnat : (84945251 : ℕ)^4471*100000000000000^3447 ≤ 45361806187731^3447*156250000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84945251 156250000 45361806187731 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608138693/5000000000 : ℝ)^4471 ≤ (8598585891877/20000000000000 : ℝ)^3447 := by
    have hnat : (2608138693 : ℕ)^4471*20000000000000^3447 ≤ 8598585891877^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608138693 5000000000 8598585891877 20000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-95279749/500000000 : ℝ), (84945251/156250000 : ℝ), (2608138693/5000000000 : ℝ)] ![(11645264334659/100000000000000 : ℝ), (45361806187731/100000000000000 : ℝ), (8598585891877/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-95279749/500000000 : ℝ)|^4471 ≤ (11645264334659/100000000000000 : ℝ)^3447
        have hw : |(-95279749/500000000 : ℝ)|=(95279749/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84945251/156250000 : ℝ)|^4471 ≤ (45361806187731/100000000000000 : ℝ)^3447
        have hw : |(84945251/156250000 : ℝ)|=(84945251/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608138693/5000000000 : ℝ)|^4471 ≤ (8598585891877/20000000000000 : ℝ)^3447
        have hw : |(2608138693/5000000000 : ℝ)|=(2608138693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s7_1 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676470549/5000000000 : ℝ)*x 0 + (-2018438777/10000000000 : ℝ)*x 1 + (5216277173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676470549/5000000000 : ℝ)^4471 ≤ (177838358969/400000000000 : ℝ)^3447 := by
    have hnat : (2676470549 : ℕ)^4471*400000000000^3447 ≤ 177838358969^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676470549 5000000000 177838358969 400000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2018438777/10000000000 : ℝ)^4471 ≤ (1568435382771/12500000000000 : ℝ)^3447 := by
    have hnat : (2018438777 : ℕ)^4471*12500000000000^3447 ≤ 1568435382771^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018438777 10000000000 1568435382771 12500000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216277173/10000000000 : ℝ)^4471 ≤ (42992927182299/100000000000000 : ℝ)^3447 := by
    have hnat : (5216277173 : ℕ)^4471*100000000000000^3447 ≤ 42992927182299^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216277173 10000000000 42992927182299 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676470549/5000000000 : ℝ), (-2018438777/10000000000 : ℝ), (5216277173/10000000000 : ℝ)] ![(177838358969/400000000000 : ℝ), (1568435382771/12500000000000 : ℝ), (42992927182299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676470549/5000000000 : ℝ)|^4471 ≤ (177838358969/400000000000 : ℝ)^3447
        have hw : |(2676470549/5000000000 : ℝ)|=(2676470549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2018438777/10000000000 : ℝ)|^4471 ≤ (1568435382771/12500000000000 : ℝ)^3447
        have hw : |(-2018438777/10000000000 : ℝ)|=(2018438777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216277173/10000000000 : ℝ)|^4471 ≤ (42992927182299/100000000000000 : ℝ)^3447
        have hw : |(5216277173/10000000000 : ℝ)|=(5216277173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s7_2 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352941089/10000000000 : ℝ)*x 0 + (5216277311/10000000000 : ℝ)*x 1 + (-403687721/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352941089/10000000000 : ℝ)^4471 ≤ (44459589645293/100000000000000 : ℝ)^3447 := by
    have hnat : (5352941089 : ℕ)^4471*100000000000000^3447 ≤ 44459589645293^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352941089 10000000000 44459589645293 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216277311/10000000000 : ℝ)^4471 ≤ (21496464328797/50000000000000 : ℝ)^3447 := by
    have hnat : (5216277311 : ℕ)^4471*50000000000000^3447 ≤ 21496464328797^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216277311 10000000000 21496464328797 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403687721/2000000000 : ℝ)^4471 ≤ (3136870418827/25000000000000 : ℝ)^3447 := by
    have hnat : (403687721 : ℕ)^4471*25000000000000^3447 ≤ 3136870418827^3447*2000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403687721 2000000000 3136870418827 25000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352941089/10000000000 : ℝ), (5216277311/10000000000 : ℝ), (-403687721/2000000000 : ℝ)] ![(44459589645293/100000000000000 : ℝ), (21496464328797/50000000000000 : ℝ), (3136870418827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352941089/10000000000 : ℝ)|^4471 ≤ (44459589645293/100000000000000 : ℝ)^3447
        have hw : |(5352941089/10000000000 : ℝ)|=(5352941089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216277311/10000000000 : ℝ)|^4471 ≤ (21496464328797/50000000000000 : ℝ)^3447
        have hw : |(5216277311/10000000000 : ℝ)|=(5216277311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-403687721/2000000000 : ℝ)|^4471 ≤ (3136870418827/25000000000000 : ℝ)^3447
        have hw : |(-403687721/2000000000 : ℝ)|=(403687721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s7_3 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2140779621/5000000000 : ℝ)*x 0 + (2021180131/5000000000 : ℝ)*x 1 + (1133235263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140779621/5000000000 : ℝ)^4471 ≤ (33278365095213/100000000000000 : ℝ)^3447 := by
    have hnat : (2140779621 : ℕ)^4471*100000000000000^3447 ≤ 33278365095213^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140779621 5000000000 33278365095213 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2021180131/5000000000 : ℝ)^4471 ≤ (3088716963299/10000000000000 : ℝ)^3447 := by
    have hnat : (2021180131 : ℕ)^4471*10000000000000^3447 ≤ 3088716963299^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021180131 5000000000 3088716963299 10000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133235263/2500000000 : ℝ)^4471 ≤ (447930815743/1250000000000 : ℝ)^3447 := by
    have hnat : (1133235263 : ℕ)^4471*1250000000000^3447 ≤ 447930815743^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133235263 2500000000 447930815743 1250000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2140779621/5000000000 : ℝ), (2021180131/5000000000 : ℝ), (1133235263/2500000000 : ℝ)] ![(33278365095213/100000000000000 : ℝ), (3088716963299/10000000000000 : ℝ), (447930815743/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2140779621/5000000000 : ℝ)|^4471 ≤ (33278365095213/100000000000000 : ℝ)^3447
        have hw : |(2140779621/5000000000 : ℝ)|=(2140779621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2021180131/5000000000 : ℝ)|^4471 ≤ (3088716963299/10000000000000 : ℝ)^3447
        have hw : |(2021180131/5000000000 : ℝ)|=(2021180131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1133235263/2500000000 : ℝ)|^4471 ≤ (447930815743/1250000000000 : ℝ)^3447
        have hw : |(1133235263/2500000000 : ℝ)|=(1133235263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s7_4 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1905624901/10000000000 : ℝ)*x 0 + (652175671/1250000000 : ℝ)*x 1 + (5435359869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1905624901/10000000000 : ℝ)^4471 ≤ (5822750752193/50000000000000 : ℝ)^3447 := by
    have hnat : (1905624901 : ℕ)^4471*50000000000000^3447 ≤ 5822750752193^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1905624901 10000000000 5822750752193 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652175671/1250000000 : ℝ)^4471 ≤ (5375623573283/12500000000000 : ℝ)^3447 := by
    have hnat : (652175671 : ℕ)^4471*12500000000000^3447 ≤ 5375623573283^3447*1250000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652175671 1250000000 5375623573283 12500000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435359869/10000000000 : ℝ)^4471 ≤ (11337377474849/25000000000000 : ℝ)^3447 := by
    have hnat : (5435359869 : ℕ)^4471*25000000000000^3447 ≤ 11337377474849^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435359869 10000000000 11337377474849 25000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1905624901/10000000000 : ℝ), (652175671/1250000000 : ℝ), (5435359869/10000000000 : ℝ)] ![(5822750752193/50000000000000 : ℝ), (5375623573283/12500000000000 : ℝ), (11337377474849/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1905624901/10000000000 : ℝ)|^4471 ≤ (5822750752193/50000000000000 : ℝ)^3447
        have hw : |(-1905624901/10000000000 : ℝ)|=(1905624901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652175671/1250000000 : ℝ)|^4471 ≤ (5375623573283/12500000000000 : ℝ)^3447
        have hw : |(652175671/1250000000 : ℝ)|=(652175671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435359869/10000000000 : ℝ)|^4471 ≤ (11337377474849/25000000000000 : ℝ)^3447
        have hw : |(5435359869/10000000000 : ℝ)|=(5435359869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_s7_5 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4281626031/10000000000 : ℝ)*x 0 + (113260707/250000000 : ℝ)*x 1 + (4044891617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4281626031/10000000000 : ℝ)^4471 ≤ (16639519213687/50000000000000 : ℝ)^3447 := by
    have hnat : (4281626031 : ℕ)^4471*50000000000000^3447 ≤ 16639519213687^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4281626031 10000000000 16639519213687 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113260707/250000000 : ℝ)^4471 ≤ (17904350977603/50000000000000 : ℝ)^3447 := by
    have hnat : (113260707 : ℕ)^4471*50000000000000^3447 ≤ 17904350977603^3447*250000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113260707 250000000 17904350977603 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4044891617/10000000000 : ℝ)^4471 ≤ (6182451918109/20000000000000 : ℝ)^3447 := by
    have hnat : (4044891617 : ℕ)^4471*20000000000000^3447 ≤ 6182451918109^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4044891617 10000000000 6182451918109 20000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4281626031/10000000000 : ℝ), (113260707/250000000 : ℝ), (4044891617/10000000000 : ℝ)] ![(16639519213687/50000000000000 : ℝ), (17904350977603/50000000000000 : ℝ), (6182451918109/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4281626031/10000000000 : ℝ)|^4471 ≤ (16639519213687/50000000000000 : ℝ)^3447
        have hw : |(4281626031/10000000000 : ℝ)|=(4281626031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(113260707/250000000 : ℝ)|^4471 ≤ (17904350977603/50000000000000 : ℝ)^3447
        have hw : |(113260707/250000000 : ℝ)|=(113260707/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4044891617/10000000000 : ℝ)|^4471 ≤ (6182451918109/20000000000000 : ℝ)^3447
        have hw : |(4044891617/10000000000 : ℝ)|=(4044891617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1487_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80692417/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2163/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (338/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15477/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15477/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2163/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15477/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2163/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15477/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2163/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15477/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2163/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15477/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2163/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15477/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2163/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2163/20000 : ℝ) ^ (4469/1024 : ℝ) ≤ (6084749584558733/100000000000000000000 : ℝ) := by
    have hpowers : (2163/20000 : ℝ)^4469 ≤ (6084749584558733/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2163 : ℕ)^4469*100000000000000000000^1024 ≤ 6084749584558733^1024*20000^4469 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2163 20000 6084749584558733 100000000000000000000 4469 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2163/20000 : ℝ)) (X := (6084749584558733/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15477/100000 : ℝ) ^ (4469/1024 : ℝ) ≤ (29079317571642119/100000000000000000000 : ℝ) := by
    have hpowers : (15477/100000 : ℝ)^4469 ≤ (29079317571642119/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15477 : ℕ)^4469*100000000000000000000^1024 ≤ 29079317571642119^1024*100000^4469 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15477 100000 29079317571642119 100000000000000000000 4469 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15477/100000 : ℝ)) (X := (29079317571642119/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006084749584558733/50000000000000000000 : ℝ) ≤ (312508713486433/312500000000000 : ℝ) ^ (4469/1024 : ℝ) := by
    have hpowers : (50006084749584558733/50000000000000000000 : ℝ)^1024 ≤ (312508713486433/312500000000000 : ℝ)^4469 := by
      have hnat : (50006084749584558733 : ℕ)^1024*312500000000000^4469 ≤ 312508713486433^4469*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006084749584558733 50000000000000000000 312508713486433 312500000000000 1024 4469 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312508713486433/312500000000000 : ℝ)) (X := (50006084749584558733/50000000000000000000 : ℝ)) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008791016789050213/25000000000000000000 : ℝ) ≤ (10000805619276683/10000000000000000 : ℝ) ^ (4469/1024 : ℝ) := by
    have hpowers : (25008791016789050213/25000000000000000000 : ℝ)^1024 ≤ (10000805619276683/10000000000000000 : ℝ)^4469 := by
      have hnat : (25008791016789050213 : ℕ)^1024*10000000000000000^4469 ≤ 10000805619276683^4469*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008791016789050213 25000000000000000000 10000805619276683 10000000000000000 1024 4469 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000805619276683/10000000000000000 : ℝ)) (X := (25008791016789050213/25000000000000000000 : ℝ)) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029079317571642119/50000000000000000000 : ℝ) ≤ (1000133240698751/1000000000000000 : ℝ) ^ (4469/1024 : ℝ) := by
    have hpowers : (50029079317571642119/50000000000000000000 : ℝ)^1024 ≤ (1000133240698751/1000000000000000 : ℝ)^4469 := by
      have hnat : (50029079317571642119 : ℕ)^1024*1000000000000000^4469 ≤ 1000133240698751^4469*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029079317571642119 50000000000000000000 1000133240698751 1000000000000000 1024 4469 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000133240698751/1000000000000000 : ℝ)) (X := (50029079317571642119/50000000000000000000 : ℝ)) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6084749584558733/100000000000000000000 : ℝ) ≤ ((369919884877578037/370000000000000000 : ℝ)+2*(25085129087/22200000000000 : ℝ)*(2163/20000 : ℝ))^(4469/1024 : ℝ) := by
    rw [show (369919884877578037/370000000000000000 : ℝ)+2*(25085129087/22200000000000 : ℝ)*(2163/20000 : ℝ)=(312508713486433/312500000000000 : ℝ) by norm_num, show 1+2*(6084749584558733/100000000000000000000 : ℝ)=(50006084749584558733/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29079317571642119/100000000000000000000 : ℝ)+(6084749584558733/100000000000000000000 : ℝ) ≤ ((369919884877578037/370000000000000000 : ℝ)+(25085129087/22200000000000 : ℝ)*((15477/100000 : ℝ)+(2163/20000 : ℝ)))^(4469/1024 : ℝ) := by
    rw [show (369919884877578037/370000000000000000 : ℝ)+(25085129087/22200000000000 : ℝ)*((15477/100000 : ℝ)+(2163/20000 : ℝ))=(10000805619276683/10000000000000000 : ℝ) by norm_num, show 1+(29079317571642119/100000000000000000000 : ℝ)+(6084749584558733/100000000000000000000 : ℝ)=(25008791016789050213/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29079317571642119/100000000000000000000 : ℝ) ≤ ((369919884877578037/370000000000000000 : ℝ)+2*(25085129087/22200000000000 : ℝ)*(15477/100000 : ℝ))^(4469/1024 : ℝ) := by
    rw [show (369919884877578037/370000000000000000 : ℝ)+2*(25085129087/22200000000000 : ℝ)*(15477/100000 : ℝ)=(1000133240698751/1000000000000000 : ℝ) by norm_num, show 1+2*(29079317571642119/100000000000000000000 : ℝ)=(50029079317571642119/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (369919884877578037/370000000000000000 : ℝ)*(X 1 0+X 2 0)+(25085129087/22200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4469/1024 : ℝ)) (lo := (2163/20000 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (369919884877578037/370000000000000000 : ℝ)) (alpha := (25085129087/22200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (369919884877578037/370000000000000000 : ℝ)*(X 0 1+X 2 1)+(25085129087/22200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4469/1024 : ℝ)) (lo := (2163/20000 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (369919884877578037/370000000000000000 : ℝ)) (alpha := (25085129087/22200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (369919884877578037/370000000000000000 : ℝ)*(X 0 2+X 1 2)+(25085129087/22200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4469/1024 : ℝ)) (lo := (2163/20000 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (369919884877578037/370000000000000000 : ℝ)) (alpha := (25085129087/22200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-95279749/500000000 : ℝ)*X 0 0+(84945251/156250000 : ℝ)*X 0 1+(2608138693/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676470549/5000000000 : ℝ)*X 1 0+(-2018438777/10000000000 : ℝ)*X 1 1+(5216277173/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352941089/10000000000 : ℝ)*X 2 0+(5216277311/10000000000 : ℝ)*X 2 1+(-403687721/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2140779621/5000000000 : ℝ)*X 0 0+(2021180131/5000000000 : ℝ)*X 0 1+(1133235263/2500000000 : ℝ)*X 0 2+(2140779621/5000000000 : ℝ)*X 1 0+(2021180131/5000000000 : ℝ)*X 1 1+(1133235263/2500000000 : ℝ)*X 1 2+(2140779621/5000000000 : ℝ)*X 2 0+(2021180131/5000000000 : ℝ)*X 2 1+(1133235263/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1905624901/10000000000 : ℝ)*X 0 0+(652175671/1250000000 : ℝ)*X 0 1+(5435359869/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4281626031/10000000000 : ℝ)*X 0 0+(113260707/250000000 : ℝ)*X 0 1+(4044891617/10000000000 : ℝ)*X 0 2+(4281626031/10000000000 : ℝ)*X 1 0+(113260707/250000000 : ℝ)*X 1 1+(4044891617/10000000000 : ℝ)*X 1 2+(4281626031/10000000000 : ℝ)*X 2 0+(113260707/250000000 : ℝ)*X 2 1+(4044891617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (459736628835783413169/185000000000000000000000000 : ℝ) := by norm_num
    linear_combination (185498431/20000000000000 : ℝ)*(base19) + (114849667/12500000000000 : ℝ)*(base23) + (70927/12500000000000 : ℝ)*(lower2) + (4177229/50000000000000 : ℝ)*(upper3) + (41994013/25000000000000 : ℝ)*(upper5) + (1644845175574421/50000000000000 : ℝ)*(major0) + (1644845175574421/50000000000000 : ℝ)*(major1) + (1644845175574421/50000000000000 : ℝ)*(major2) + (2270475798389711/50000000000000 : ℝ)*(sp0) + (4540966125086331/100000000000000 : ℝ)*(sp1) + (90819322675623/2000000000000 : ℝ)*(sp2) + (2038407722024819/100000000000000 : ℝ)*(sp3) + (1931974883/12500000000000 : ℝ)*(sp4) + (1168971789/20000000000000 : ℝ)*(sp5) + (509603391720941/25000000000000 : ℝ)*(f.failure) + (2270483526289243/50000000000000 : ℝ)*(f.sum) + (455957621083/138750000000000000000000000 : ℝ)*base65 + (184253853908124731/55500000000000000000000000000000 : ℝ)*base67 + (147956349068375269/55500000000000000000000000000000 : ℝ)*base70 + (252202485803375269/55500000000000000000000000000000 : ℝ)*base72 + (1094338269311/277500000000000000000000000 : ℝ)*base73 + (82506915029124731/55500000000000000000000000000000 : ℝ)*base75 + (183423606419375269/55500000000000000000000000000000 : ℝ)*base78 + (330645255413124731/55500000000000000000000000000000 : ℝ)*base79 + (143793123731/277500000000000000000000000 : ℝ)*base81 + (6195603/1250000000000000000000 : ℝ)*base90 + (6195603/1250000000000000000000 : ℝ)*base92 + (6195603/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1487_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80692417/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2163/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (338/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1487_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1487_box_0 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-168738587/1000000000 : ℝ)*x 0 + (1351384921/2500000000 : ℝ)*x 1 + (540554019/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168738587/1000000000 : ℝ)^4471 ≤ (9945876386791/100000000000000 : ℝ)^3447 := by
    have hnat : (168738587 : ℕ)^4471*100000000000000^3447 ≤ 9945876386791^3447*1000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168738587 1000000000 9945876386791 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351384921/2500000000 : ℝ)^4471 ≤ (5628382383427/12500000000000 : ℝ)^3447 := by
    have hnat : (1351384921 : ℕ)^4471*12500000000000^3447 ≤ 5628382383427^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351384921 2500000000 5628382383427 12500000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540554019/1000000000 : ℝ)^4471 ≤ (5628383066801/12500000000000 : ℝ)^3447 := by
    have hnat : (540554019 : ℕ)^4471*12500000000000^3447 ≤ 5628383066801^3447*1000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540554019 1000000000 5628383066801 12500000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-168738587/1000000000 : ℝ), (1351384921/2500000000 : ℝ), (540554019/1000000000 : ℝ)] ![(9945876386791/100000000000000 : ℝ), (5628382383427/12500000000000 : ℝ), (5628383066801/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-168738587/1000000000 : ℝ)|^4471 ≤ (9945876386791/100000000000000 : ℝ)^3447
        have hw : |(-168738587/1000000000 : ℝ)|=(168738587/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351384921/2500000000 : ℝ)|^4471 ≤ (5628382383427/12500000000000 : ℝ)^3447
        have hw : |(1351384921/2500000000 : ℝ)|=(1351384921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540554019/1000000000 : ℝ)|^4471 ≤ (5628383066801/12500000000000 : ℝ)^3447
        have hw : |(540554019/1000000000 : ℝ)|=(540554019/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_box_1 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270375947/10000000000 : ℝ)*x 0 + (-1874675971/10000000000 : ℝ)*x 1 + (1081107981/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270375947/10000000000 : ℝ)^4471 ≤ (1361630037301/3125000000000 : ℝ)^3447 := by
    have hnat : (5270375947 : ℕ)^4471*3125000000000^3447 ≤ 1361630037301^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270375947 10000000000 1361630037301 3125000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1874675971/10000000000 : ℝ)^4471 ≤ (1140077734251/10000000000000 : ℝ)^3447 := by
    have hnat : (1874675971 : ℕ)^4471*10000000000000^3447 ≤ 1140077734251^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1874675971 10000000000 1140077734251 10000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081107981/2000000000 : ℝ)^4471 ≤ (22513530727587/50000000000000 : ℝ)^3447 := by
    have hnat : (1081107981 : ℕ)^4471*50000000000000^3447 ≤ 22513530727587^3447*2000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081107981 2000000000 22513530727587 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270375947/10000000000 : ℝ), (-1874675971/10000000000 : ℝ), (1081107981/2000000000 : ℝ)] ![(1361630037301/3125000000000 : ℝ), (1140077734251/10000000000000 : ℝ), (22513530727587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270375947/10000000000 : ℝ)|^4471 ≤ (1361630037301/3125000000000 : ℝ)^3447
        have hw : |(5270375947/10000000000 : ℝ)|=(5270375947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1874675971/10000000000 : ℝ)|^4471 ≤ (1140077734251/10000000000000 : ℝ)^3447
        have hw : |(-1874675971/10000000000 : ℝ)|=(1874675971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081107981/2000000000 : ℝ)|^4471 ≤ (22513530727587/50000000000000 : ℝ)^3447
        have hw : |(1081107981/2000000000 : ℝ)|=(1081107981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_box_2 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270376209/10000000000 : ℝ)*x 0 + (5405539699/10000000000 : ℝ)*x 1 + (-374935179/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270376209/10000000000 : ℝ)^4471 ≤ (2723260250197/6250000000000 : ℝ)^3447 := by
    have hnat : (5270376209 : ℕ)^4471*6250000000000^3447 ≤ 2723260250197^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270376209 10000000000 2723260250197 6250000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405539699/10000000000 : ℝ)^4471 ≤ (45027059229481/100000000000000 : ℝ)^3447 := by
    have hnat : (5405539699 : ℕ)^4471*100000000000000^3447 ≤ 45027059229481^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405539699 10000000000 45027059229481 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (374935179/2000000000 : ℝ)^4471 ≤ (2280155348603/20000000000000 : ℝ)^3447 := by
    have hnat : (374935179 : ℕ)^4471*20000000000000^3447 ≤ 2280155348603^3447*2000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374935179 2000000000 2280155348603 20000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270376209/10000000000 : ℝ), (5405539699/10000000000 : ℝ), (-374935179/2000000000 : ℝ)] ![(2723260250197/6250000000000 : ℝ), (45027059229481/100000000000000 : ℝ), (2280155348603/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270376209/10000000000 : ℝ)|^4471 ≤ (2723260250197/6250000000000 : ℝ)^3447
        have hw : |(5270376209/10000000000 : ℝ)|=(5270376209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405539699/10000000000 : ℝ)|^4471 ≤ (45027059229481/100000000000000 : ℝ)^3447
        have hw : |(5405539699/10000000000 : ℝ)|=(5405539699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-374935179/2000000000 : ℝ)|^4471 ≤ (2280155348603/20000000000000 : ℝ)^3447
        have hw : |(-374935179/2000000000 : ℝ)|=(374935179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_box_3 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1121451627/2500000000 : ℝ)*x 0 + (1046645939/2500000000 : ℝ)*x 1 + (2093292081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1121451627/2500000000 : ℝ)^4471 ≤ (17675953017087/50000000000000 : ℝ)^3447 := by
    have hnat : (1121451627 : ℕ)^4471*50000000000000^3447 ≤ 17675953017087^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121451627 2500000000 17675953017087 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046645939/2500000000 : ℝ)^4471 ≤ (32324044940843/100000000000000 : ℝ)^3447 := by
    have hnat : (1046645939 : ℕ)^4471*100000000000000^3447 ≤ 32324044940843^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046645939 2500000000 32324044940843 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2093292081/5000000000 : ℝ)^4471 ≤ (32324049006731/100000000000000 : ℝ)^3447 := by
    have hnat : (2093292081 : ℕ)^4471*100000000000000^3447 ≤ 32324049006731^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093292081 5000000000 32324049006731 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1121451627/2500000000 : ℝ), (1046645939/2500000000 : ℝ), (2093292081/5000000000 : ℝ)] ![(17675953017087/50000000000000 : ℝ), (32324044940843/100000000000000 : ℝ), (32324049006731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1121451627/2500000000 : ℝ)|^4471 ≤ (17675953017087/50000000000000 : ℝ)^3447
        have hw : |(1121451627/2500000000 : ℝ)|=(1121451627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1046645939/2500000000 : ℝ)|^4471 ≤ (32324044940843/100000000000000 : ℝ)^3447
        have hw : |(1046645939/2500000000 : ℝ)|=(1046645939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2093292081/5000000000 : ℝ)|^4471 ≤ (32324049006731/100000000000000 : ℝ)^3447
        have hw : |(2093292081/5000000000 : ℝ)|=(2093292081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_box_4 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-85170357/400000000 : ℝ)*x 0 + (5242724737/10000000000 : ℝ)*x 1 + (524272523/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85170357/400000000 : ℝ)^4471 ≤ (13448237376481/100000000000000 : ℝ)^3447 := by
    have hnat : (85170357 : ℕ)^4471*100000000000000^3447 ≤ 13448237376481^3447*400000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85170357 400000000 13448237376481 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242724737/10000000000 : ℝ)^4471 ≤ (8655175733219/20000000000000 : ℝ)^3447 := by
    have hnat : (5242724737 : ℕ)^4471*20000000000000^3447 ≤ 8655175733219^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242724737 10000000000 8655175733219 20000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524272523/1000000000 : ℝ)^4471 ≤ (5409485493057/12500000000000 : ℝ)^3447 := by
    have hnat : (524272523 : ℕ)^4471*12500000000000^3447 ≤ 5409485493057^3447*1000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524272523 1000000000 5409485493057 12500000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85170357/400000000 : ℝ), (5242724737/10000000000 : ℝ), (524272523/1000000000 : ℝ)] ![(13448237376481/100000000000000 : ℝ), (8655175733219/20000000000000 : ℝ), (5409485493057/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85170357/400000000 : ℝ)|^4471 ≤ (13448237376481/100000000000000 : ℝ)^3447
        have hw : |(-85170357/400000000 : ℝ)|=(85170357/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242724737/10000000000 : ℝ)|^4471 ≤ (8655175733219/20000000000000 : ℝ)^3447
        have hw : |(5242724737/10000000000 : ℝ)|=(5242724737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524272523/1000000000 : ℝ)|^4471 ≤ (5409485493057/12500000000000 : ℝ)^3447
        have hw : |(524272523/1000000000 : ℝ)|=(524272523/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_box_5 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538395243/1000000000 : ℝ)*x 0 + (-970718373/5000000000 : ℝ)*x 1 + (5242725191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538395243/1000000000 : ℝ)^4471 ≤ (1399811302987/3125000000000 : ℝ)^3447 := by
    have hnat : (538395243 : ℕ)^4471*3125000000000^3447 ≤ 1399811302987^3447*1000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538395243 1000000000 1399811302987 3125000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (970718373/5000000000 : ℝ)^4471 ≤ (477206190721/4000000000000 : ℝ)^3447 := by
    have hnat : (970718373 : ℕ)^4471*4000000000000^3447 ≤ 477206190721^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970718373 5000000000 477206190721 4000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242725191/10000000000 : ℝ)^4471 ≤ (21637941763449/50000000000000 : ℝ)^3447 := by
    have hnat : (5242725191 : ℕ)^4471*50000000000000^3447 ≤ 21637941763449^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242725191 10000000000 21637941763449 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538395243/1000000000 : ℝ), (-970718373/5000000000 : ℝ), (5242725191/10000000000 : ℝ)] ![(1399811302987/3125000000000 : ℝ), (477206190721/4000000000000 : ℝ), (21637941763449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538395243/1000000000 : ℝ)|^4471 ≤ (1399811302987/3125000000000 : ℝ)^3447
        have hw : |(538395243/1000000000 : ℝ)|=(538395243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-970718373/5000000000 : ℝ)|^4471 ≤ (477206190721/4000000000000 : ℝ)^3447
        have hw : |(-970718373/5000000000 : ℝ)|=(970718373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242725191/10000000000 : ℝ)|^4471 ≤ (21637941763449/50000000000000 : ℝ)^3447
        have hw : |(5242725191/10000000000 : ℝ)|=(5242725191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_box_6 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5383952233/10000000000 : ℝ)*x 0 + (1048545021/2000000000 : ℝ)*x 1 + (-1941437127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383952233/10000000000 : ℝ)^4471 ≤ (44793959569659/100000000000000 : ℝ)^3447 := by
    have hnat : (5383952233 : ℕ)^4471*100000000000000^3447 ≤ 44793959569659^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383952233 10000000000 44793959569659 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048545021/2000000000 : ℝ)^4471 ≤ (43275882606129/100000000000000 : ℝ)^3447 := by
    have hnat : (1048545021 : ℕ)^4471*100000000000000^3447 ≤ 43275882606129^3447*2000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048545021 2000000000 43275882606129 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1941437127/10000000000 : ℝ)^4471 ≤ (11930157804791/100000000000000 : ℝ)^3447 := by
    have hnat : (1941437127 : ℕ)^4471*100000000000000^3447 ≤ 11930157804791^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941437127 10000000000 11930157804791 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383952233/10000000000 : ℝ), (1048545021/2000000000 : ℝ), (-1941437127/10000000000 : ℝ)] ![(44793959569659/100000000000000 : ℝ), (43275882606129/100000000000000 : ℝ), (11930157804791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383952233/10000000000 : ℝ)|^4471 ≤ (44793959569659/100000000000000 : ℝ)^3447
        have hw : |(5383952233/10000000000 : ℝ)|=(5383952233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048545021/2000000000 : ℝ)|^4471 ≤ (43275882606129/100000000000000 : ℝ)^3447
        have hw : |(1048545021/2000000000 : ℝ)|=(1048545021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1941437127/10000000000 : ℝ)|^4471 ≤ (11930157804791/100000000000000 : ℝ)^3447
        have hw : |(-1941437127/10000000000 : ℝ)|=(1941437127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_box_7 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2037508077/5000000000 : ℝ)*x 0 + (137245047/312500000 : ℝ)*x 1 + (4391841441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037508077/5000000000 : ℝ)^4471 ≤ (6242240320827/20000000000000 : ℝ)^3447 := by
    have hnat : (2037508077 : ℕ)^4471*20000000000000^3447 ≤ 6242240320827^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037508077 5000000000 6242240320827 20000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137245047/312500000 : ℝ)^4471 ≤ (34394399509229/100000000000000 : ℝ)^3447 := by
    have hnat : (137245047 : ℕ)^4471*100000000000000^3447 ≤ 34394399509229^3447*312500000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137245047 312500000 34394399509229 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4391841441/10000000000 : ℝ)^4471 ≤ (34394398869281/100000000000000 : ℝ)^3447 := by
    have hnat : (4391841441 : ℕ)^4471*100000000000000^3447 ≤ 34394398869281^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4391841441 10000000000 34394398869281 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2037508077/5000000000 : ℝ), (137245047/312500000 : ℝ), (4391841441/10000000000 : ℝ)] ![(6242240320827/20000000000000 : ℝ), (34394399509229/100000000000000 : ℝ), (34394398869281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2037508077/5000000000 : ℝ)|^4471 ≤ (6242240320827/20000000000000 : ℝ)^3447
        have hw : |(2037508077/5000000000 : ℝ)|=(2037508077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137245047/312500000 : ℝ)|^4471 ≤ (34394399509229/100000000000000 : ℝ)^3447
        have hw : |(137245047/312500000 : ℝ)|=(137245047/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4391841441/10000000000 : ℝ)|^4471 ≤ (34394398869281/100000000000000 : ℝ)^3447
        have hw : |(4391841441/10000000000 : ℝ)|=(4391841441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_box_8 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2036021933/10000000000 : ℝ)*x 0 + (2564471467/5000000000 : ℝ)*x 1 + (5426065383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2036021933/10000000000 : ℝ)^4471 ≤ (12689441657639/100000000000000 : ℝ)^3447 := by
    have hnat : (2036021933 : ℕ)^4471*100000000000000^3447 ≤ 12689441657639^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036021933 10000000000 12689441657639 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564471467/5000000000 : ℝ)^4471 ≤ (42061607833147/100000000000000 : ℝ)^3447 := by
    have hnat : (2564471467 : ℕ)^4471*100000000000000^3447 ≤ 42061607833147^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564471467 5000000000 42061607833147 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426065383/10000000000 : ℝ)^4471 ≤ (22624475247613/50000000000000 : ℝ)^3447 := by
    have hnat : (5426065383 : ℕ)^4471*50000000000000^3447 ≤ 22624475247613^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426065383 10000000000 22624475247613 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2036021933/10000000000 : ℝ), (2564471467/5000000000 : ℝ), (5426065383/10000000000 : ℝ)] ![(12689441657639/100000000000000 : ℝ), (42061607833147/100000000000000 : ℝ), (22624475247613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2036021933/10000000000 : ℝ)|^4471 ≤ (12689441657639/100000000000000 : ℝ)^3447
        have hw : |(-2036021933/10000000000 : ℝ)|=(2036021933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564471467/5000000000 : ℝ)|^4471 ≤ (42061607833147/100000000000000 : ℝ)^3447
        have hw : |(2564471467/5000000000 : ℝ)|=(2564471467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426065383/10000000000 : ℝ)|^4471 ≤ (22624475247613/50000000000000 : ℝ)^3447
        have hw : |(5426065383/10000000000 : ℝ)|=(5426065383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_box_9 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525605059/1000000000 : ℝ)*x 0 + (-1866006923/10000000000 : ℝ)*x 1 + (2713032693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525605059/1000000000 : ℝ)^4471 ≤ (21709303645123/50000000000000 : ℝ)^3447 := by
    have hnat : (525605059 : ℕ)^4471*50000000000000^3447 ≤ 21709303645123^3447*1000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525605059 1000000000 21709303645123 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1866006923/10000000000 : ℝ)^4471 ≤ (11332442166821/100000000000000 : ℝ)^3447 := by
    have hnat : (1866006923 : ℕ)^4471*100000000000000^3447 ≤ 11332442166821^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866006923 10000000000 11332442166821 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713032693/5000000000 : ℝ)^4471 ≤ (11312237631919/25000000000000 : ℝ)^3447 := by
    have hnat : (2713032693 : ℕ)^4471*25000000000000^3447 ≤ 11312237631919^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713032693 5000000000 11312237631919 25000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525605059/1000000000 : ℝ), (-1866006923/10000000000 : ℝ), (2713032693/5000000000 : ℝ)] ![(21709303645123/50000000000000 : ℝ), (11332442166821/100000000000000 : ℝ), (11312237631919/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525605059/1000000000 : ℝ)|^4471 ≤ (21709303645123/50000000000000 : ℝ)^3447
        have hw : |(525605059/1000000000 : ℝ)|=(525605059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1866006923/10000000000 : ℝ)|^4471 ≤ (11332442166821/100000000000000 : ℝ)^3447
        have hw : |(-1866006923/10000000000 : ℝ)|=(1866006923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713032693/5000000000 : ℝ)|^4471 ≤ (11312237631919/25000000000000 : ℝ)^3447
        have hw : |(2713032693/5000000000 : ℝ)|=(2713032693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_box_10 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256050843/10000000000 : ℝ)*x 0 + (2713032593/5000000000 : ℝ)*x 1 + (-933003427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256050843/10000000000 : ℝ)^4471 ≤ (5427326250133/12500000000000 : ℝ)^3447 := by
    have hnat : (5256050843 : ℕ)^4471*12500000000000^3447 ≤ 5427326250133^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256050843 10000000000 5427326250133 12500000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713032593/5000000000 : ℝ)^4471 ≤ (72398317383/160000000000 : ℝ)^3447 := by
    have hnat : (2713032593 : ℕ)^4471*160000000000^3447 ≤ 72398317383^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713032593 5000000000 72398317383 160000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (933003427/5000000000 : ℝ)^4471 ≤ (2833110405823/25000000000000 : ℝ)^3447 := by
    have hnat : (933003427 : ℕ)^4471*25000000000000^3447 ≤ 2833110405823^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933003427 5000000000 2833110405823 25000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256050843/10000000000 : ℝ), (2713032593/5000000000 : ℝ), (-933003427/5000000000 : ℝ)] ![(5427326250133/12500000000000 : ℝ), (72398317383/160000000000 : ℝ), (2833110405823/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256050843/10000000000 : ℝ)|^4471 ≤ (5427326250133/12500000000000 : ℝ)^3447
        have hw : |(5256050843/10000000000 : ℝ)|=(5256050843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713032593/5000000000 : ℝ)|^4471 ≤ (72398317383/160000000000 : ℝ)^3447
        have hw : |(2713032593/5000000000 : ℝ)|=(2713032593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-933003427/5000000000 : ℝ)|^4471 ≤ (2833110405823/25000000000000 : ℝ)^3447
        have hw : |(-933003427/5000000000 : ℝ)|=(933003427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_box_11 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4536438633/10000000000 : ℝ)*x 0 + (1040168999/2500000000 : ℝ)*x 1 + (520084577/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4536438633/10000000000 : ℝ)^4471 ≤ (8967583203883/25000000000000 : ℝ)^3447 := by
    have hnat : (4536438633 : ℕ)^4471*25000000000000^3447 ≤ 8967583203883^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4536438633 10000000000 8967583203883 25000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040168999/2500000000 : ℝ)^4471 ≤ (6412966097667/20000000000000 : ℝ)^3447 := by
    have hnat : (1040168999 : ℕ)^4471*20000000000000^3447 ≤ 6412966097667^3447*2500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040168999 2500000000 6412966097667 20000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520084577/1250000000 : ℝ)^4471 ≤ (32064836685887/100000000000000 : ℝ)^3447 := by
    have hnat : (520084577 : ℕ)^4471*100000000000000^3447 ≤ 32064836685887^3447*1250000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520084577 1250000000 32064836685887 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4536438633/10000000000 : ℝ), (1040168999/2500000000 : ℝ), (520084577/1250000000 : ℝ)] ![(8967583203883/25000000000000 : ℝ), (6412966097667/20000000000000 : ℝ), (32064836685887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4536438633/10000000000 : ℝ)|^4471 ≤ (8967583203883/25000000000000 : ℝ)^3447
        have hw : |(4536438633/10000000000 : ℝ)|=(4536438633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1040168999/2500000000 : ℝ)|^4471 ≤ (6412966097667/20000000000000 : ℝ)^3447
        have hw : |(1040168999/2500000000 : ℝ)|=(1040168999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(520084577/1250000000 : ℝ)|^4471 ≤ (32064836685887/100000000000000 : ℝ)^3447
        have hw : |(520084577/1250000000 : ℝ)|=(520084577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_box_12 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1780713149/10000000000 : ℝ)*x 0 + (5515574571/10000000000 : ℝ)*x 1 + (2613861779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1780713149/10000000000 : ℝ)^4471 ≤ (10665174803983/100000000000000 : ℝ)^3447 := by
    have hnat : (1780713149 : ℕ)^4471*100000000000000^3447 ≤ 10665174803983^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1780713149 10000000000 10665174803983 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5515574571/10000000000 : ℝ)^4471 ≤ (23109745033937/50000000000000 : ℝ)^3447 := by
    have hnat : (5515574571 : ℕ)^4471*50000000000000^3447 ≤ 23109745033937^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515574571 10000000000 23109745033937 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613861779/5000000000 : ℝ)^4471 ≤ (43115335110849/100000000000000 : ℝ)^3447 := by
    have hnat : (2613861779 : ℕ)^4471*100000000000000^3447 ≤ 43115335110849^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613861779 5000000000 43115335110849 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1780713149/10000000000 : ℝ), (5515574571/10000000000 : ℝ), (2613861779/5000000000 : ℝ)] ![(10665174803983/100000000000000 : ℝ), (23109745033937/50000000000000 : ℝ), (43115335110849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1780713149/10000000000 : ℝ)|^4471 ≤ (10665174803983/100000000000000 : ℝ)^3447
        have hw : |(-1780713149/10000000000 : ℝ)|=(1780713149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5515574571/10000000000 : ℝ)|^4471 ≤ (23109745033937/50000000000000 : ℝ)^3447
        have hw : |(5515574571/10000000000 : ℝ)|=(5515574571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613861779/5000000000 : ℝ)|^4471 ≤ (43115335110849/100000000000000 : ℝ)^3447
        have hw : |(2613861779/5000000000 : ℝ)|=(2613861779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_box_13 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (337151/625000 : ℝ)*x 0 + (-973702929/5000000000 : ℝ)*x 1 + (2613861763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337151/625000 : ℝ)^4471 ≤ (44906911848983/100000000000000 : ℝ)^3447 := by
    have hnat : (337151 : ℕ)^4471*100000000000000^3447 ≤ 44906911848983^3447*625000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337151 625000 44906911848983 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (973702929/5000000000 : ℝ)^4471 ≤ (11977753358663/100000000000000 : ℝ)^3447 := by
    have hnat : (973702929 : ℕ)^4471*100000000000000^3447 ≤ 11977753358663^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973702929 5000000000 11977753358663 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613861763/5000000000 : ℝ)^4471 ≤ (43115334768529/100000000000000 : ℝ)^3447 := by
    have hnat : (2613861763 : ℕ)^4471*100000000000000^3447 ≤ 43115334768529^3447*5000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613861763 5000000000 43115334768529 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337151/625000 : ℝ), (-973702929/5000000000 : ℝ), (2613861763/5000000000 : ℝ)] ![(44906911848983/100000000000000 : ℝ), (11977753358663/100000000000000 : ℝ), (43115334768529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337151/625000 : ℝ)|^4471 ≤ (44906911848983/100000000000000 : ℝ)^3447
        have hw : |(337151/625000 : ℝ)|=(337151/625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-973702929/5000000000 : ℝ)|^4471 ≤ (11977753358663/100000000000000 : ℝ)^3447
        have hw : |(-973702929/5000000000 : ℝ)|=(973702929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613861763/5000000000 : ℝ)|^4471 ≤ (43115334768529/100000000000000 : ℝ)^3447
        have hw : |(2613861763/5000000000 : ℝ)|=(2613861763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_box_14 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1078883211/2000000000 : ℝ)*x 0 + (653465457/1250000000 : ℝ)*x 1 + (-194740561/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078883211/2000000000 : ℝ)^4471 ≤ (22453456221429/50000000000000 : ℝ)^3447 := by
    have hnat : (1078883211 : ℕ)^4471*50000000000000^3447 ≤ 22453456221429^3447*2000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078883211 2000000000 22453456221429 50000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653465457/1250000000 : ℝ)^4471 ≤ (8623067231841/20000000000000 : ℝ)^3447 := by
    have hnat : (653465457 : ℕ)^4471*20000000000000^3447 ≤ 8623067231841^3447*1250000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653465457 1250000000 8623067231841 20000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194740561/1000000000 : ℝ)^4471 ≤ (11977751380173/100000000000000 : ℝ)^3447 := by
    have hnat : (194740561 : ℕ)^4471*100000000000000^3447 ≤ 11977751380173^3447*1000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194740561 1000000000 11977751380173 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078883211/2000000000 : ℝ), (653465457/1250000000 : ℝ), (-194740561/1000000000 : ℝ)] ![(22453456221429/50000000000000 : ℝ), (8623067231841/20000000000000 : ℝ), (11977751380173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078883211/2000000000 : ℝ)|^4471 ≤ (22453456221429/50000000000000 : ℝ)^3447
        have hw : |(1078883211/2000000000 : ℝ)|=(1078883211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(653465457/1250000000 : ℝ)|^4471 ≤ (8623067231841/20000000000000 : ℝ)^3447
        have hw : |(653465457/1250000000 : ℝ)|=(653465457/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-194740561/1000000000 : ℝ)|^4471 ≤ (11977751380173/100000000000000 : ℝ)^3447
        have hw : |(-194740561/1000000000 : ℝ)|=(194740561/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1487_box_15 (p : ℝ) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (31533651/78125000 : ℝ)*x 0 + (4410731819/10000000000 : ℝ)*x 1 + (220536541/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31533651/78125000 : ℝ)^4471 ≤ (30827193869539/100000000000000 : ℝ)^3447 := by
    have hnat : (31533651 : ℕ)^4471*100000000000000^3447 ≤ 30827193869539^3447*78125000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31533651 78125000 30827193869539 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4410731819/10000000000 : ℝ)^4471 ≤ (864660203549/2500000000000 : ℝ)^3447 := by
    have hnat : (4410731819 : ℕ)^4471*2500000000000^3447 ≤ 864660203549^3447*10000000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4410731819 10000000000 864660203549 2500000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220536541/500000000 : ℝ)^4471 ≤ (34586397981259/100000000000000 : ℝ)^3447 := by
    have hnat : (220536541 : ℕ)^4471*100000000000000^3447 ≤ 34586397981259^3447*500000000^4471 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220536541 500000000 34586397981259 100000000000000 4471 3447 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4471/1024 : ℝ)) 4471 3447 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(31533651/78125000 : ℝ), (4410731819/10000000000 : ℝ), (220536541/500000000 : ℝ)] ![(30827193869539/100000000000000 : ℝ), (864660203549/2500000000000 : ℝ), (34586397981259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(31533651/78125000 : ℝ)|^4471 ≤ (30827193869539/100000000000000 : ℝ)^3447
        have hw : |(31533651/78125000 : ℝ)|=(31533651/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4410731819/10000000000 : ℝ)|^4471 ≤ (864660203549/2500000000000 : ℝ)^3447
        have hw : |(4410731819/10000000000 : ℝ)|=(4410731819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(220536541/500000000 : ℝ)|^4471 ≤ (34586397981259/100000000000000 : ℝ)^3447
        have hw : |(220536541/500000000 : ℝ)|=(220536541/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1487_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80692417/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (338/3125 : ℝ)*pair X i i ≤ pair X i h) :
    -(63709/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5851/10000 : ℝ) ∧ (40023/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (1073/1250 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15477/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (338/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15477/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (338/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15477/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (338/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15477/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (338/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15477/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (338/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15477/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (338/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (338/3125 : ℝ) ^ (4469/1024 : ℝ) ≤ (760900673873737/12500000000000000000 : ℝ) := by
    have hpowers : (338/3125 : ℝ)^4469 ≤ (760900673873737/12500000000000000000 : ℝ)^1024 := by
      have hnat : (338 : ℕ)^4469*12500000000000000000^1024 ≤ 760900673873737^1024*3125^4469 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        338 3125 760900673873737 12500000000000000000 4469 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (338/3125 : ℝ)) (X := (760900673873737/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15477/100000 : ℝ) ^ (4469/1024 : ℝ) ≤ (29079317571642119/100000000000000000000 : ℝ) := by
    have hpowers : (15477/100000 : ℝ)^4469 ≤ (29079317571642119/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15477 : ℕ)^4469*100000000000000000000^1024 ≤ 29079317571642119^1024*100000^4469 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15477 100000 29079317571642119 100000000000000000000 4469 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15477/100000 : ℝ)) (X := (29079317571642119/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250760900673873737/6250000000000000000 : ℝ) ≤ (1250034868012133/1250000000000000 : ℝ) ^ (4469/1024 : ℝ) := by
    have hpowers : (6250760900673873737/6250000000000000000 : ℝ)^1024 ≤ (1250034868012133/1250000000000000 : ℝ)^4469 := by
      have hnat : (6250760900673873737 : ℕ)^1024*1250000000000000^4469 ≤ 1250034868012133^4469*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250760900673873737 6250000000000000000 1250034868012133 1250000000000000 1024 4469 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250034868012133/1250000000000000 : ℝ)) (X := (6250760900673873737/6250000000000000000 : ℝ)) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007033304592526403/20000000000000000000 : ℝ) ≤ (10000805675532317/10000000000000000 : ℝ) ^ (4469/1024 : ℝ) := by
    have hpowers : (20007033304592526403/20000000000000000000 : ℝ)^1024 ≤ (10000805675532317/10000000000000000 : ℝ)^4469 := by
      have hnat : (20007033304592526403 : ℕ)^1024*10000000000000000^4469 ≤ 10000805675532317^4469*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007033304592526403 20000000000000000000 10000805675532317 10000000000000000 1024 4469 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000805675532317/10000000000000000 : ℝ)) (X := (20007033304592526403/20000000000000000000 : ℝ)) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029079317571642119/50000000000000000000 : ℝ) ≤ (1000133240696757/1000000000000000 : ℝ) ^ (4469/1024 : ℝ) := by
    have hpowers : (50029079317571642119/50000000000000000000 : ℝ)^1024 ≤ (1000133240696757/1000000000000000 : ℝ)^4469 := by
      have hnat : (50029079317571642119 : ℕ)^1024*1000000000000000^4469 ≤ 1000133240696757^4469*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029079317571642119 50000000000000000000 1000133240696757 1000000000000000 1024 4469 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000133240696757/1000000000000000 : ℝ)) (X := (50029079317571642119/50000000000000000000 : ℝ)) (by norm_num) 4469 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(760900673873737/12500000000000000000 : ℝ) ≤ ((5824988238003627801/5826250000000000000 : ℝ)+2*(526731435253/466100000000000 : ℝ)*(338/3125 : ℝ))^(4469/1024 : ℝ) := by
    rw [show (5824988238003627801/5826250000000000000 : ℝ)+2*(526731435253/466100000000000 : ℝ)*(338/3125 : ℝ)=(1250034868012133/1250000000000000 : ℝ) by norm_num, show 1+2*(760900673873737/12500000000000000000 : ℝ)=(6250760900673873737/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29079317571642119/100000000000000000000 : ℝ)+(760900673873737/12500000000000000000 : ℝ) ≤ ((5824988238003627801/5826250000000000000 : ℝ)+(526731435253/466100000000000 : ℝ)*((15477/100000 : ℝ)+(338/3125 : ℝ)))^(4469/1024 : ℝ) := by
    rw [show (5824988238003627801/5826250000000000000 : ℝ)+(526731435253/466100000000000 : ℝ)*((15477/100000 : ℝ)+(338/3125 : ℝ))=(10000805675532317/10000000000000000 : ℝ) by norm_num, show 1+(29079317571642119/100000000000000000000 : ℝ)+(760900673873737/12500000000000000000 : ℝ)=(20007033304592526403/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29079317571642119/100000000000000000000 : ℝ) ≤ ((5824988238003627801/5826250000000000000 : ℝ)+2*(526731435253/466100000000000 : ℝ)*(15477/100000 : ℝ))^(4469/1024 : ℝ) := by
    rw [show (5824988238003627801/5826250000000000000 : ℝ)+2*(526731435253/466100000000000 : ℝ)*(15477/100000 : ℝ)=(1000133240696757/1000000000000000 : ℝ) by norm_num, show 1+2*(29079317571642119/100000000000000000000 : ℝ)=(50029079317571642119/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5824988238003627801/5826250000000000000 : ℝ)*(X 1 0+X 2 0)+(526731435253/466100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4469/1024 : ℝ)) (lo := (338/3125 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (5824988238003627801/5826250000000000000 : ℝ)) (alpha := (526731435253/466100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5824988238003627801/5826250000000000000 : ℝ)*(X 0 1+X 2 1)+(526731435253/466100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4469/1024 : ℝ)) (lo := (338/3125 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (5824988238003627801/5826250000000000000 : ℝ)) (alpha := (526731435253/466100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5824988238003627801/5826250000000000000 : ℝ)*(X 0 2+X 1 2)+(526731435253/466100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4469/1024 : ℝ)) (lo := (338/3125 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (5824988238003627801/5826250000000000000 : ℝ)) (alpha := (526731435253/466100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-168738587/1000000000 : ℝ)*X 0 0+(1351384921/2500000000 : ℝ)*X 0 1+(540554019/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270375947/10000000000 : ℝ)*X 1 0+(-1874675971/10000000000 : ℝ)*X 1 1+(1081107981/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270376209/10000000000 : ℝ)*X 2 0+(5405539699/10000000000 : ℝ)*X 2 1+(-374935179/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1121451627/2500000000 : ℝ)*X 0 0+(1046645939/2500000000 : ℝ)*X 0 1+(2093292081/5000000000 : ℝ)*X 0 2+(1121451627/2500000000 : ℝ)*X 1 0+(1046645939/2500000000 : ℝ)*X 1 1+(2093292081/5000000000 : ℝ)*X 1 2+(1121451627/2500000000 : ℝ)*X 2 0+(1046645939/2500000000 : ℝ)*X 2 1+(2093292081/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-85170357/400000000 : ℝ)*X 0 0+(5242724737/10000000000 : ℝ)*X 0 1+(524272523/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((538395243/1000000000 : ℝ)*X 1 0+(-970718373/5000000000 : ℝ)*X 1 1+(5242725191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5383952233/10000000000 : ℝ)*X 2 0+(1048545021/2000000000 : ℝ)*X 2 1+(-1941437127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2037508077/5000000000 : ℝ)*X 0 0+(137245047/312500000 : ℝ)*X 0 1+(4391841441/10000000000 : ℝ)*X 0 2+(2037508077/5000000000 : ℝ)*X 1 0+(137245047/312500000 : ℝ)*X 1 1+(4391841441/10000000000 : ℝ)*X 1 2+(2037508077/5000000000 : ℝ)*X 2 0+(137245047/312500000 : ℝ)*X 2 1+(4391841441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2036021933/10000000000 : ℝ)*X 0 0+(2564471467/5000000000 : ℝ)*X 0 1+(5426065383/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((525605059/1000000000 : ℝ)*X 1 0+(-1866006923/10000000000 : ℝ)*X 1 1+(2713032693/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5256050843/10000000000 : ℝ)*X 2 0+(2713032593/5000000000 : ℝ)*X 2 1+(-933003427/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4536438633/10000000000 : ℝ)*X 0 0+(1040168999/2500000000 : ℝ)*X 0 1+(520084577/1250000000 : ℝ)*X 0 2+(4536438633/10000000000 : ℝ)*X 1 0+(1040168999/2500000000 : ℝ)*X 1 1+(520084577/1250000000 : ℝ)*X 1 2+(4536438633/10000000000 : ℝ)*X 2 0+(1040168999/2500000000 : ℝ)*X 2 1+(520084577/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1780713149/10000000000 : ℝ)*X 0 0+(5515574571/10000000000 : ℝ)*X 0 1+(2613861779/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((337151/625000 : ℝ)*X 1 0+(-973702929/5000000000 : ℝ)*X 1 1+(2613861763/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1078883211/2000000000 : ℝ)*X 2 0+(653465457/1250000000 : ℝ)*X 2 1+(-194740561/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((31533651/78125000 : ℝ)*X 0 0+(4410731819/10000000000 : ℝ)*X 0 1+(220536541/500000000 : ℝ)*X 0 2+(31533651/78125000 : ℝ)*X 1 0+(4410731819/10000000000 : ℝ)*X 1 1+(220536541/500000000 : ℝ)*X 1 2+(31533651/78125000 : ℝ)*X 2 0+(4410731819/10000000000 : ℝ)*X 2 1+(220536541/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1487_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63709/100000 : ℝ) ≤ (-92793020857713350885710689765537/145656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55147343/50000000000000 : ℝ)*(upper1) + (39100817/25000000000000 : ℝ)*(lower4) + (20727597/50000000000000 : ℝ)*(upper5) + (2186253900211021/100000000000000 : ℝ)*(major0) + (2186253900211021/100000000000000 : ℝ)*(major1) + (2186253900211021/100000000000000 : ℝ)*(major2) + (525199917/25000000000000 : ℝ)*(sp2) + (237982481/12500000000000 : ℝ)*(sp3) + (1519527986835919/50000000000000 : ℝ)*(sp4) + (189936897044949/6250000000000 : ℝ)*(sp5) + (3039057705980281/100000000000000 : ℝ)*(sp6) + (338670427307619/25000000000000 : ℝ)*(sp7) + (3833108111/100000000000000 : ℝ)*(sp12) + (34727030383/50000000000000 : ℝ)*(sp13) + (338670903272581/25000000000000 : ℝ)*(f.failure) + (3039059806779949/100000000000000 : ℝ)*(f.sum) + (5745968277309/11652500000000000000000000000 : ℝ)*base65 + (66657242484401/7375000000000000000000000000000 : ℝ)*base68 + (10767748823890599/7375000000000000000000000000000 : ℝ)*base69 + (88478645681359401/7375000000000000000000000000000 : ℝ)*base72 + (32599086260813/23305000000000000000000000000 : ℝ)*base73 + (69611589868359401/7375000000000000000000000000000 : ℝ)*base76 + (33602325048234401/7375000000000000000000000000000 : ℝ)*base78 + (15741279061234401/7375000000000000000000000000000 : ℝ)*base80 + (3009208609239/2913125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (8218277/1250000000000000000000 : ℝ)*base89 + (8218277/1250000000000000000000 : ℝ)*base91 + (8218277/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (5851/10000 : ℝ) ≤ (42613873560597749653893152344227/72828125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18618487/20000000000000 : ℝ)*(lower3) + (8245499/100000000000000 : ℝ)*(upper4) + (15462391/50000000000000 : ℝ)*(upper5) + (565199735340847/25000000000000 : ℝ)*(major0) + (565199735340847/25000000000000 : ℝ)*(major1) + (565199735340847/25000000000000 : ℝ)*(major2) + (1550608270166243/50000000000000 : ℝ)*(sp0) + (3101216015439719/100000000000000 : ℝ)*(sp1) + (775298145638981/25000000000000 : ℝ)*(sp2) + (700436511043479/50000000000000 : ℝ)*(sp3) + (1541728179/50000000000000 : ℝ)*(sp5) + (1450023219/100000000000000 : ℝ)*(sp7) + (3314542519/12500000000000 : ℝ)*(sp10) + (255856359/10000000000000 : ℝ)*(sp12) + (700437236055089/50000000000000 : ℝ)*(f.failure) + (775304774724019/25000000000000 : ℝ)*(f.sum) + (16926466526983/2913125000000000000000000000 : ℝ)*base65 + (41026740960846993/1843750000000000000000000000000 : ℝ)*base67 + (18499870947628243/1843750000000000000000000000000 : ℝ)*base69 + (28169329529128243/1843750000000000000000000000000 : ℝ)*base71 + (311622521072029/23305000000000000000000000000 : ℝ)*base73 + (4685508595534493/1843750000000000000000000000000 : ℝ)*base75 + (23823847850346993/1843750000000000000000000000000 : ℝ)*base77 + (29866649735659493/1843750000000000000000000000000 : ℝ)*base79 + (40120113799871/23305000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (23439887/2500000000000000000000 : ℝ)*base90 + (23439887/2500000000000000000000 : ℝ)*base92 + (23439887/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (40023/50000 : ℝ) ≤ (233191682525808664407841899098439/291312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2406649/50000000000000 : ℝ)*(upper0) + (29049141/100000000000000 : ℝ)*(lower1) + (32837151/25000000000000 : ℝ)*(lower3) + (3266087/50000000000000 : ℝ)*(upper4) + (2457545394388913/100000000000000 : ℝ)*(major0) + (2457545394388913/100000000000000 : ℝ)*(major1) + (2457545394388913/100000000000000 : ℝ)*(major2) + (71066727/1562500000000 : ℝ)*(sp0) + (27440176161/50000000000000 : ℝ)*(sp1) + (23904357517/100000000000000 : ℝ)*(sp3) + (3365617525379701/100000000000000 : ℝ)*(sp8) + (841391798324477/25000000000000 : ℝ)*(sp9) + (3365622073650229/100000000000000 : ℝ)*(sp10) + (761380966064387/50000000000000 : ℝ)*(sp11) + (380696459121573/25000000000000 : ℝ)*(f.failure) + (3365622073650229/100000000000000 : ℝ)*(f.sum) + (26695493153391/5826250000000000000000000000 : ℝ)*base65 + (14501932899652947/7375000000000000000000000000000 : ℝ)*base67 + (23432756505472053/7375000000000000000000000000000 : ℝ)*base70 + (513512451597053/7375000000000000000000000000000 : ℝ)*base72 + (118287515361939/23305000000000000000000000000 : ℝ)*base73 + (46973100831097053/7375000000000000000000000000000 : ℝ)*base76 + (1096346849972053/7375000000000000000000000000000 : ℝ)*base78 + (16454746553152947/7375000000000000000000000000000 : ℝ)*base79 + (34900769922471/23305000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (9711941/1250000000000000000000 : ℝ)*base89 + (9711941/1250000000000000000000 : ℝ)*base91 + (9711941/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-1073/1250 : ℝ) ≤ (-12502705721485794202769678019003/14565625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (154309877/100000000000000 : ℝ)*(lower2) + (86063143/50000000000000 : ℝ)*(upper3) + (13324779/50000000000000 : ℝ)*(upper5) + (31200192522553/1250000000000 : ℝ)*(major0) + (31200192522553/1250000000000 : ℝ)*(major1) + (31200192522553/1250000000000 : ℝ)*(major2) + (152627747/25000000000000 : ℝ)*(sp0) + (129385005671/100000000000000 : ℝ)*(sp5) + (86077329/50000000000000 : ℝ)*(sp6) + (4115664731/10000000000000 : ℝ)*(sp7) + (1737009638354539/50000000000000 : ℝ)*(sp12) + (868472625553599/25000000000000 : ℝ)*(sp13) + (54281558047897/1562500000000 : ℝ)*(sp14) + (386645529098679/25000000000000 : ℝ)*(sp15) + (773311636521013/50000000000000 : ℝ)*(f.failure) + (1737009943610033/50000000000000 : ℝ)*(f.sum) + (16258085842089/2330500000000000000000000000 : ℝ)*base65 + (121707613439009/46093750000000000000000000000 : ℝ)*base68 + (23442146659779/11523437500000000000000000000 : ℝ)*base69 + (656006319295259/46093750000000000000000000000 : ℝ)*base72 + (5668792792817/2330500000000000000000000000 : ℝ)*base73 + (1883698470840411/184375000000000000000000000000 : ℝ)*base76 + (33455384307759/46093750000000000000000000000 : ℝ)*base78 + (310437431464009/46093750000000000000000000000 : ℝ)*base80 + (49854437971/14565625000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (10258421/2500000000000000000000 : ℝ)*base89 + (10258421/2500000000000000000000 : ℝ)*base91 + (10258421/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1487_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80692417/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (338/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63709/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5851/10000 : ℝ) else (40023/50000 : ℝ) ≤ X j i ∧ X j i ≤ (1073/1250 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1487_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1487_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80692417/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63709/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5851/10000 : ℝ) else (40023/50000 : ℝ) ≤ X j i ∧ X j i ≤ (1073/1250 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1487_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1487_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1487_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4469/1024 : ℝ) ≤ p) (hpb : p ≤ (4471/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80692417/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63709/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5851/10000 : ℝ) else (40023/50000 : ℝ) ≤ X j i ∧ X j i ≤ (1073/1250 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1487_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
