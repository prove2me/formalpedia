-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_w1019_box
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:09:39.923955+00:00
-- url     : https://prove2.me/submissions/de5f3e90-9dbf-49d1-a479-032e8f6f31ff

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
theorem support_rectangle_w1019_box_0 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1048010677/5000000000 : ℝ)*x 0 + (2688995689/5000000000 : ℝ)*x 1 + (5377991073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048010677/5000000000 : ℝ)^2053 ≤ (3117943368663/25000000000000 : ℝ)^1541 := by
    have hnat : (1048010677 : ℕ)^2053*25000000000000^1541 ≤ 3117943368663^1541*5000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048010677 5000000000 3117943368663 25000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688995689/5000000000 : ℝ)^2053 ≤ (43764114909293/100000000000000 : ℝ)^1541 := by
    have hnat : (2688995689 : ℕ)^2053*100000000000000^1541 ≤ 43764114909293^1541*5000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688995689 5000000000 43764114909293 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377991073/10000000000 : ℝ)^2053 ≤ (43764111602673/100000000000000 : ℝ)^1541 := by
    have hnat : (5377991073 : ℕ)^2053*100000000000000^1541 ≤ 43764111602673^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377991073 10000000000 43764111602673 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1048010677/5000000000 : ℝ), (2688995689/5000000000 : ℝ), (5377991073/10000000000 : ℝ)] ![(3117943368663/25000000000000 : ℝ), (43764114909293/100000000000000 : ℝ), (43764111602673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1048010677/5000000000 : ℝ)|^2053 ≤ (3117943368663/25000000000000 : ℝ)^1541
        have hw : |(-1048010677/5000000000 : ℝ)|=(1048010677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688995689/5000000000 : ℝ)|^2053 ≤ (43764114909293/100000000000000 : ℝ)^1541
        have hw : |(2688995689/5000000000 : ℝ)|=(2688995689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377991073/10000000000 : ℝ)|^2053 ≤ (43764111602673/100000000000000 : ℝ)^1541
        have hw : |(5377991073/10000000000 : ℝ)|=(5377991073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_box_1 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2647322019/5000000000 : ℝ)*x 0 + (-2208719251/10000000000 : ℝ)*x 1 + (672248909/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647322019/5000000000 : ℝ)^2053 ≤ (5357856204871/12500000000000 : ℝ)^1541 := by
    have hnat : (2647322019 : ℕ)^2053*12500000000000^1541 ≤ 5357856204871^1541*5000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647322019 5000000000 5357856204871 12500000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2208719251/10000000000 : ℝ)^2053 ≤ (13373036582601/100000000000000 : ℝ)^1541 := by
    have hnat : (2208719251 : ℕ)^2053*100000000000000^1541 ≤ 13373036582601^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208719251 10000000000 13373036582601 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672248909/1250000000 : ℝ)^2053 ≤ (43764113760107/100000000000000 : ℝ)^1541 := by
    have hnat : (672248909 : ℕ)^2053*100000000000000^1541 ≤ 43764113760107^1541*1250000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672248909 1250000000 43764113760107 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647322019/5000000000 : ℝ), (-2208719251/10000000000 : ℝ), (672248909/1250000000 : ℝ)] ![(5357856204871/12500000000000 : ℝ), (13373036582601/100000000000000 : ℝ), (43764113760107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647322019/5000000000 : ℝ)|^2053 ≤ (5357856204871/12500000000000 : ℝ)^1541
        have hw : |(2647322019/5000000000 : ℝ)|=(2647322019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2208719251/10000000000 : ℝ)|^2053 ≤ (13373036582601/100000000000000 : ℝ)^1541
        have hw : |(-2208719251/10000000000 : ℝ)|=(2208719251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672248909/1250000000 : ℝ)|^2053 ≤ (43764113760107/100000000000000 : ℝ)^1541
        have hw : |(672248909/1250000000 : ℝ)|=(672248909/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_box_2 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1058928823/2000000000 : ℝ)*x 0 + (672248899/1250000000 : ℝ)*x 1 + (-276089907/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058928823/2000000000 : ℝ)^2053 ≤ (42862850469433/100000000000000 : ℝ)^1541 := by
    have hnat : (1058928823 : ℕ)^2053*100000000000000^1541 ≤ 42862850469433^1541*2000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058928823 2000000000 42862850469433 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (672248899/1250000000 : ℝ)^2053 ≤ (43764112892797/100000000000000 : ℝ)^1541 := by
    have hnat : (672248899 : ℕ)^2053*100000000000000^1541 ≤ 43764112892797^1541*1250000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672248899 1250000000 43764112892797 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276089907/1250000000 : ℝ)^2053 ≤ (3343259155733/25000000000000 : ℝ)^1541 := by
    have hnat : (276089907 : ℕ)^2053*25000000000000^1541 ≤ 3343259155733^1541*1250000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276089907 1250000000 3343259155733 25000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058928823/2000000000 : ℝ), (672248899/1250000000 : ℝ), (-276089907/1250000000 : ℝ)] ![(42862850469433/100000000000000 : ℝ), (43764112892797/100000000000000 : ℝ), (3343259155733/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058928823/2000000000 : ℝ)|^2053 ≤ (42862850469433/100000000000000 : ℝ)^1541
        have hw : |(1058928823/2000000000 : ℝ)|=(1058928823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(672248899/1250000000 : ℝ)|^2053 ≤ (43764112892797/100000000000000 : ℝ)^1541
        have hw : |(672248899/1250000000 : ℝ)|=(672248899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-276089907/1250000000 : ℝ)|^2053 ≤ (3343259155733/25000000000000 : ℝ)^1541
        have hw : |(-276089907/1250000000 : ℝ)|=(276089907/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_box_3 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2245614951/5000000000 : ℝ)*x 0 + (4330027677/10000000000 : ℝ)*x 1 + (866005489/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2245614951/5000000000 : ℝ)^2053 ≤ (4303016842251/12500000000000 : ℝ)^1541 := by
    have hnat : (2245614951 : ℕ)^2053*12500000000000^1541 ≤ 4303016842251^1541*5000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245614951 5000000000 4303016842251 12500000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4330027677/10000000000 : ℝ)^2053 ≤ (32787933795057/100000000000000 : ℝ)^1541 := by
    have hnat : (4330027677 : ℕ)^2053*100000000000000^1541 ≤ 32787933795057^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330027677 10000000000 32787933795057 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (866005489/2000000000 : ℝ)^2053 ≤ (4098491431827/12500000000000 : ℝ)^1541 := by
    have hnat : (866005489 : ℕ)^2053*12500000000000^1541 ≤ 4098491431827^1541*2000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866005489 2000000000 4098491431827 12500000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2245614951/5000000000 : ℝ), (4330027677/10000000000 : ℝ), (866005489/2000000000 : ℝ)] ![(4303016842251/12500000000000 : ℝ), (32787933795057/100000000000000 : ℝ), (4098491431827/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2245614951/5000000000 : ℝ)|^2053 ≤ (4303016842251/12500000000000 : ℝ)^1541
        have hw : |(2245614951/5000000000 : ℝ)|=(2245614951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4330027677/10000000000 : ℝ)|^2053 ≤ (32787933795057/100000000000000 : ℝ)^1541
        have hw : |(4330027677/10000000000 : ℝ)|=(4330027677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(866005489/2000000000 : ℝ)|^2053 ≤ (4098491431827/12500000000000 : ℝ)^1541
        have hw : |(866005489/2000000000 : ℝ)|=(866005489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_box_4 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-471923939/2000000000 : ℝ)*x 0 + (329959911/625000000 : ℝ)*x 1 + (5279358401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (471923939/2000000000 : ℝ)^2053 ≤ (3650964923771/25000000000000 : ℝ)^1541 := by
    have hnat : (471923939 : ℕ)^2053*25000000000000^1541 ≤ 3650964923771^1541*2000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471923939 2000000000 3650964923771 25000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329959911/625000000 : ℝ)^2053 ≤ (2668629442941/6250000000000 : ℝ)^1541 := by
    have hnat : (329959911 : ℕ)^2053*6250000000000^1541 ≤ 2668629442941^1541*625000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329959911 625000000 2668629442941 6250000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279358401/10000000000 : ℝ)^2053 ≤ (5337258650181/12500000000000 : ℝ)^1541 := by
    have hnat : (5279358401 : ℕ)^2053*12500000000000^1541 ≤ 5337258650181^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279358401 10000000000 5337258650181 12500000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-471923939/2000000000 : ℝ), (329959911/625000000 : ℝ), (5279358401/10000000000 : ℝ)] ![(3650964923771/25000000000000 : ℝ), (2668629442941/6250000000000 : ℝ), (5337258650181/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-471923939/2000000000 : ℝ)|^2053 ≤ (3650964923771/25000000000000 : ℝ)^1541
        have hw : |(-471923939/2000000000 : ℝ)|=(471923939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329959911/625000000 : ℝ)|^2053 ≤ (2668629442941/6250000000000 : ℝ)^1541
        have hw : |(329959911/625000000 : ℝ)|=(329959911/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279358401/10000000000 : ℝ)|^2053 ≤ (5337258650181/12500000000000 : ℝ)^1541
        have hw : |(5279358401/10000000000 : ℝ)|=(5279358401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_box_5 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (670565487/1250000000 : ℝ)*x 0 + (-280891213/1250000000 : ℝ)*x 1 + (5279358549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670565487/1250000000 : ℝ)^2053 ≤ (21809084831593/50000000000000 : ℝ)^1541 := by
    have hnat : (670565487 : ℕ)^2053*50000000000000^1541 ≤ 21809084831593^1541*1250000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670565487 1250000000 21809084831593 50000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280891213/1250000000 : ℝ)^2053 ≤ (6841879759429/50000000000000 : ℝ)^1541 := by
    have hnat : (280891213 : ℕ)^2053*50000000000000^1541 ≤ 6841879759429^1541*1250000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280891213 1250000000 6841879759429 50000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279358549/10000000000 : ℝ)^2053 ≤ (42698070796133/100000000000000 : ℝ)^1541 := by
    have hnat : (5279358549 : ℕ)^2053*100000000000000^1541 ≤ 42698070796133^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279358549 10000000000 42698070796133 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670565487/1250000000 : ℝ), (-280891213/1250000000 : ℝ), (5279358549/10000000000 : ℝ)] ![(21809084831593/50000000000000 : ℝ), (6841879759429/50000000000000 : ℝ), (42698070796133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670565487/1250000000 : ℝ)|^2053 ≤ (21809084831593/50000000000000 : ℝ)^1541
        have hw : |(670565487/1250000000 : ℝ)|=(670565487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-280891213/1250000000 : ℝ)|^2053 ≤ (6841879759429/50000000000000 : ℝ)^1541
        have hw : |(-280891213/1250000000 : ℝ)|=(280891213/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279358549/10000000000 : ℝ)|^2053 ≤ (42698070796133/100000000000000 : ℝ)^1541
        have hw : |(5279358549/10000000000 : ℝ)|=(5279358549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_box_6 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2682262077/5000000000 : ℝ)*x 0 + (2639679187/5000000000 : ℝ)*x 1 + (-2247129593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682262077/5000000000 : ℝ)^2053 ≤ (43618172457931/100000000000000 : ℝ)^1541 := by
    have hnat : (2682262077 : ℕ)^2053*100000000000000^1541 ≤ 43618172457931^1541*5000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682262077 5000000000 43618172457931 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2639679187/5000000000 : ℝ)^2053 ≤ (1707922756421/4000000000000 : ℝ)^1541 := by
    have hnat : (2639679187 : ℕ)^2053*4000000000000^1541 ≤ 1707922756421^1541*5000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639679187 5000000000 1707922756421 4000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247129593/10000000000 : ℝ)^2053 ≤ (855234913647/6250000000000 : ℝ)^1541 := by
    have hnat : (2247129593 : ℕ)^2053*6250000000000^1541 ≤ 855234913647^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247129593 10000000000 855234913647 6250000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682262077/5000000000 : ℝ), (2639679187/5000000000 : ℝ), (-2247129593/10000000000 : ℝ)] ![(43618172457931/100000000000000 : ℝ), (1707922756421/4000000000000 : ℝ), (855234913647/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682262077/5000000000 : ℝ)|^2053 ≤ (43618172457931/100000000000000 : ℝ)^1541
        have hw : |(2682262077/5000000000 : ℝ)|=(2682262077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2639679187/5000000000 : ℝ)|^2053 ≤ (1707922756421/4000000000000 : ℝ)^1541
        have hw : |(2639679187/5000000000 : ℝ)|=(2639679187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2247129593/10000000000 : ℝ)|^2053 ≤ (855234913647/6250000000000 : ℝ)^1541
        have hw : |(-2247129593/10000000000 : ℝ)|=(2247129593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_box_7 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (213652783/500000000 : ℝ)*x 0 + (2219546381/5000000000 : ℝ)*x 1 + (4439092877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213652783/500000000 : ℝ)^2053 ≤ (4026806742571/12500000000000 : ℝ)^1541 := by
    have hnat : (213652783 : ℕ)^2053*12500000000000^1541 ≤ 4026806742571^1541*500000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213652783 500000000 4026806742571 12500000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2219546381/5000000000 : ℝ)^2053 ≤ (33892772438973/100000000000000 : ℝ)^1541 := by
    have hnat : (2219546381 : ℕ)^2053*100000000000000^1541 ≤ 33892772438973^1541*5000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219546381 5000000000 33892772438973 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4439092877/10000000000 : ℝ)^2053 ≤ (16946386804367/50000000000000 : ℝ)^1541 := by
    have hnat : (4439092877 : ℕ)^2053*50000000000000^1541 ≤ 16946386804367^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4439092877 10000000000 16946386804367 50000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213652783/500000000 : ℝ), (2219546381/5000000000 : ℝ), (4439092877/10000000000 : ℝ)] ![(4026806742571/12500000000000 : ℝ), (33892772438973/100000000000000 : ℝ), (16946386804367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213652783/500000000 : ℝ)|^2053 ≤ (4026806742571/12500000000000 : ℝ)^1541
        have hw : |(213652783/500000000 : ℝ)|=(213652783/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2219546381/5000000000 : ℝ)|^2053 ≤ (33892772438973/100000000000000 : ℝ)^1541
        have hw : |(2219546381/5000000000 : ℝ)|=(2219546381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4439092877/10000000000 : ℝ)|^2053 ≤ (16946386804367/50000000000000 : ℝ)^1541
        have hw : |(4439092877/10000000000 : ℝ)|=(4439092877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_box_8 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1152326179/5000000000 : ℝ)*x 0 + (5212524831/10000000000 : ℝ)*x 1 + (336723997/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1152326179/5000000000 : ℝ)^2053 ≤ (2830478983071/20000000000000 : ℝ)^1541 := by
    have hnat : (1152326179 : ℕ)^2053*20000000000000^1541 ≤ 2830478983071^1541*5000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152326179 5000000000 2830478983071 20000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5212524831/10000000000 : ℝ)^2053 ≤ (20989731334031/50000000000000 : ℝ)^1541 := by
    have hnat : (5212524831 : ℕ)^2053*50000000000000^1541 ≤ 20989731334031^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212524831 10000000000 20989731334031 50000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336723997/625000000 : ℝ)^2053 ≤ (21934071201383/50000000000000 : ℝ)^1541 := by
    have hnat : (336723997 : ℕ)^2053*50000000000000^1541 ≤ 21934071201383^1541*625000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336723997 625000000 21934071201383 50000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1152326179/5000000000 : ℝ), (5212524831/10000000000 : ℝ), (336723997/625000000 : ℝ)] ![(2830478983071/20000000000000 : ℝ), (20989731334031/50000000000000 : ℝ), (21934071201383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1152326179/5000000000 : ℝ)|^2053 ≤ (2830478983071/20000000000000 : ℝ)^1541
        have hw : |(-1152326179/5000000000 : ℝ)|=(1152326179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5212524831/10000000000 : ℝ)|^2053 ≤ (20989731334031/50000000000000 : ℝ)^1541
        have hw : |(5212524831/10000000000 : ℝ)|=(5212524831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336723997/625000000 : ℝ)|^2053 ≤ (21934071201383/50000000000000 : ℝ)^1541
        have hw : |(336723997/625000000 : ℝ)|=(336723997/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_box_9 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5287843613/10000000000 : ℝ)*x 0 + (-2204912267/10000000000 : ℝ)*x 1 + (2693791959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287843613/10000000000 : ℝ)^2053 ≤ (21394760473631/50000000000000 : ℝ)^1541 := by
    have hnat : (5287843613 : ℕ)^2053*50000000000000^1541 ≤ 21394760473631^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287843613 10000000000 21394760473631 50000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2204912267/10000000000 : ℝ)^2053 ≤ (13342337000891/100000000000000 : ℝ)^1541 := by
    have hnat : (2204912267 : ℕ)^2053*100000000000000^1541 ≤ 13342337000891^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204912267 10000000000 13342337000891 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693791959/5000000000 : ℝ)^2053 ≤ (43868142033941/100000000000000 : ℝ)^1541 := by
    have hnat : (2693791959 : ℕ)^2053*100000000000000^1541 ≤ 43868142033941^1541*5000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693791959 5000000000 43868142033941 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287843613/10000000000 : ℝ), (-2204912267/10000000000 : ℝ), (2693791959/5000000000 : ℝ)] ![(21394760473631/50000000000000 : ℝ), (13342337000891/100000000000000 : ℝ), (43868142033941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287843613/10000000000 : ℝ)|^2053 ≤ (21394760473631/50000000000000 : ℝ)^1541
        have hw : |(5287843613/10000000000 : ℝ)|=(5287843613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2204912267/10000000000 : ℝ)|^2053 ≤ (13342337000891/100000000000000 : ℝ)^1541
        have hw : |(-2204912267/10000000000 : ℝ)|=(2204912267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693791959/5000000000 : ℝ)|^2053 ≤ (43868142033941/100000000000000 : ℝ)^1541
        have hw : |(2693791959/5000000000 : ℝ)|=(2693791959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_box_10 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2643921903/5000000000 : ℝ)*x 0 + (2693792031/5000000000 : ℝ)*x 1 + (-275613977/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643921903/5000000000 : ℝ)^2053 ≤ (42789523027929/100000000000000 : ℝ)^1541 := by
    have hnat : (2643921903 : ℕ)^2053*100000000000000^1541 ≤ 42789523027929^1541*5000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643921903 5000000000 42789523027929 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693792031/5000000000 : ℝ)^2053 ≤ (43868143596023/100000000000000 : ℝ)^1541 := by
    have hnat : (2693792031 : ℕ)^2053*100000000000000^1541 ≤ 43868143596023^1541*5000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693792031 5000000000 43868143596023 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275613977/1250000000 : ℝ)^2053 ≤ (6671166682531/50000000000000 : ℝ)^1541 := by
    have hnat : (275613977 : ℕ)^2053*50000000000000^1541 ≤ 6671166682531^1541*1250000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275613977 1250000000 6671166682531 50000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643921903/5000000000 : ℝ), (2693792031/5000000000 : ℝ), (-275613977/1250000000 : ℝ)] ![(42789523027929/100000000000000 : ℝ), (43868143596023/100000000000000 : ℝ), (6671166682531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643921903/5000000000 : ℝ)|^2053 ≤ (42789523027929/100000000000000 : ℝ)^1541
        have hw : |(2643921903/5000000000 : ℝ)|=(2643921903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693792031/5000000000 : ℝ)|^2053 ≤ (43868143596023/100000000000000 : ℝ)^1541
        have hw : |(2693792031/5000000000 : ℝ)|=(2693792031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-275613977/1250000000 : ℝ)|^2053 ≤ (6671166682531/50000000000000 : ℝ)^1541
        have hw : |(-275613977/1250000000 : ℝ)|=(275613977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_box_11 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4512176131/10000000000 : ℝ)*x 0 + (4319414189/10000000000 : ℝ)*x 1 + (1079853427/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4512176131/10000000000 : ℝ)^2053 ≤ (34638189999711/100000000000000 : ℝ)^1541 := by
    have hnat : (4512176131 : ℕ)^2053*100000000000000^1541 ≤ 34638189999711^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512176131 10000000000 34638189999711 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4319414189/10000000000 : ℝ)^2053 ≤ (16340453706473/50000000000000 : ℝ)^1541 := by
    have hnat : (4319414189 : ℕ)^2053*50000000000000^1541 ≤ 16340453706473^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319414189 10000000000 16340453706473 50000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079853427/2500000000 : ℝ)^2053 ≤ (16340451282261/50000000000000 : ℝ)^1541 := by
    have hnat : (1079853427 : ℕ)^2053*50000000000000^1541 ≤ 16340451282261^1541*2500000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079853427 2500000000 16340451282261 50000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4512176131/10000000000 : ℝ), (4319414189/10000000000 : ℝ), (1079853427/2500000000 : ℝ)] ![(34638189999711/100000000000000 : ℝ), (16340453706473/50000000000000 : ℝ), (16340451282261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4512176131/10000000000 : ℝ)|^2053 ≤ (34638189999711/100000000000000 : ℝ)^1541
        have hw : |(4512176131/10000000000 : ℝ)|=(4512176131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4319414189/10000000000 : ℝ)|^2053 ≤ (16340453706473/50000000000000 : ℝ)^1541
        have hw : |(4319414189/10000000000 : ℝ)|=(4319414189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079853427/2500000000 : ℝ)|^2053 ≤ (16340451282261/50000000000000 : ℝ)^1541
        have hw : |(1079853427/2500000000 : ℝ)|=(1079853427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_box_12 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-215138921/1000000000 : ℝ)*x 0 + (5443451797/10000000000 : ℝ)*x 1 + (2635692287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215138921/1000000000 : ℝ)^2053 ≤ (12912599423741/100000000000000 : ℝ)^1541 := by
    have hnat : (215138921 : ℕ)^2053*100000000000000^1541 ≤ 12912599423741^1541*1000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215138921 1000000000 12912599423741 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443451797/10000000000 : ℝ)^2053 ≤ (22237613500887/50000000000000 : ℝ)^1541 := by
    have hnat : (5443451797 : ℕ)^2053*50000000000000^1541 ≤ 22237613500887^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443451797 10000000000 22237613500887 50000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2635692287/5000000000 : ℝ)^2053 ≤ (10653043386901/25000000000000 : ℝ)^1541 := by
    have hnat : (2635692287 : ℕ)^2053*25000000000000^1541 ≤ 10653043386901^1541*5000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635692287 5000000000 10653043386901 25000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215138921/1000000000 : ℝ), (5443451797/10000000000 : ℝ), (2635692287/5000000000 : ℝ)] ![(12912599423741/100000000000000 : ℝ), (22237613500887/50000000000000 : ℝ), (10653043386901/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215138921/1000000000 : ℝ)|^2053 ≤ (12912599423741/100000000000000 : ℝ)^1541
        have hw : |(-215138921/1000000000 : ℝ)|=(215138921/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443451797/10000000000 : ℝ)|^2053 ≤ (22237613500887/50000000000000 : ℝ)^1541
        have hw : |(5443451797/10000000000 : ℝ)|=(5443451797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2635692287/5000000000 : ℝ)|^2053 ≤ (10653043386901/25000000000000 : ℝ)^1541
        have hw : |(2635692287/5000000000 : ℝ)|=(2635692287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_box_13 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1074034061/2000000000 : ℝ)*x 0 + (-2250176469/10000000000 : ℝ)*x 1 + (5271384551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074034061/2000000000 : ℝ)^2053 ≤ (21839672108567/50000000000000 : ℝ)^1541 := by
    have hnat : (1074034061 : ℕ)^2053*50000000000000^1541 ≤ 21839672108567^1541*2000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074034061 2000000000 21839672108567 50000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250176469/10000000000 : ℝ)^2053 ≤ (13708482471777/100000000000000 : ℝ)^1541 := by
    have hnat : (2250176469 : ℕ)^2053*100000000000000^1541 ≤ 13708482471777^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250176469 10000000000 13708482471777 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271384551/10000000000 : ℝ)^2053 ≤ (21306086649953/50000000000000 : ℝ)^1541 := by
    have hnat : (5271384551 : ℕ)^2053*50000000000000^1541 ≤ 21306086649953^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271384551 10000000000 21306086649953 50000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074034061/2000000000 : ℝ), (-2250176469/10000000000 : ℝ), (5271384551/10000000000 : ℝ)] ![(21839672108567/50000000000000 : ℝ), (13708482471777/100000000000000 : ℝ), (21306086649953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074034061/2000000000 : ℝ)|^2053 ≤ (21839672108567/50000000000000 : ℝ)^1541
        have hw : |(1074034061/2000000000 : ℝ)|=(1074034061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2250176469/10000000000 : ℝ)|^2053 ≤ (13708482471777/100000000000000 : ℝ)^1541
        have hw : |(-2250176469/10000000000 : ℝ)|=(2250176469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271384551/10000000000 : ℝ)|^2053 ≤ (21306086649953/50000000000000 : ℝ)^1541
        have hw : |(5271384551/10000000000 : ℝ)|=(5271384551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_box_14 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (42961369/80000000 : ℝ)*x 0 + (5271384887/10000000000 : ℝ)*x 1 + (-140635933/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42961369/80000000 : ℝ)^2053 ≤ (10919838275691/25000000000000 : ℝ)^1541 := by
    have hnat : (42961369 : ℕ)^2053*25000000000000^1541 ≤ 10919838275691^1541*80000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42961369 80000000 10919838275691 25000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5271384887/10000000000 : ℝ)^2053 ≤ (5326522114807/12500000000000 : ℝ)^1541 := by
    have hnat : (5271384887 : ℕ)^2053*12500000000000^1541 ≤ 5326522114807^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271384887 10000000000 5326522114807 12500000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140635933/625000000 : ℝ)^2053 ≤ (13708469964531/100000000000000 : ℝ)^1541 := by
    have hnat : (140635933 : ℕ)^2053*100000000000000^1541 ≤ 13708469964531^1541*625000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140635933 625000000 13708469964531 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42961369/80000000 : ℝ), (5271384887/10000000000 : ℝ), (-140635933/625000000 : ℝ)] ![(10919838275691/25000000000000 : ℝ), (5326522114807/12500000000000 : ℝ), (13708469964531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42961369/80000000 : ℝ)|^2053 ≤ (10919838275691/25000000000000 : ℝ)^1541
        have hw : |(42961369/80000000 : ℝ)|=(42961369/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5271384887/10000000000 : ℝ)|^2053 ≤ (5326522114807/12500000000000 : ℝ)^1541
        have hw : |(5271384887/10000000000 : ℝ)|=(5271384887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-140635933/625000000 : ℝ)|^2053 ≤ (13708469964531/100000000000000 : ℝ)^1541
        have hw : |(-140635933/625000000 : ℝ)|=(140635933/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_box_15 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1063796647/2500000000 : ℝ)*x 0 + (2223952971/5000000000 : ℝ)*x 1 + (4343658/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063796647/2500000000 : ℝ)^2053 ≤ (32035105154913/100000000000000 : ℝ)^1541 := by
    have hnat : (1063796647 : ℕ)^2053*100000000000000^1541 ≤ 32035105154913^1541*2500000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063796647 2500000000 32035105154913 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2223952971/5000000000 : ℝ)^2053 ≤ (3398244818079/10000000000000 : ℝ)^1541 := by
    have hnat : (2223952971 : ℕ)^2053*10000000000000^1541 ≤ 3398244818079^1541*5000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223952971 5000000000 3398244818079 10000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4343658/9765625 : ℝ)^2053 ≤ (33982446654009/100000000000000 : ℝ)^1541 := by
    have hnat : (4343658 : ℕ)^2053*100000000000000^1541 ≤ 33982446654009^1541*9765625^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343658 9765625 33982446654009 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1063796647/2500000000 : ℝ), (2223952971/5000000000 : ℝ), (4343658/9765625 : ℝ)] ![(32035105154913/100000000000000 : ℝ), (3398244818079/10000000000000 : ℝ), (33982446654009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1063796647/2500000000 : ℝ)|^2053 ≤ (32035105154913/100000000000000 : ℝ)^1541
        have hw : |(1063796647/2500000000 : ℝ)|=(1063796647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2223952971/5000000000 : ℝ)|^2053 ≤ (3398244818079/10000000000000 : ℝ)^1541
        have hw : |(2223952971/5000000000 : ℝ)|=(2223952971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4343658/9765625 : ℝ)|^2053 ≤ (33982446654009/100000000000000 : ℝ)^1541
        have hw : |(4343658/9765625 : ℝ)|=(4343658/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1019_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147079583/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3493/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5593/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29603/50000 : ℝ) ∧ (79423/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (20711/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3493/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5593/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3493/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5593/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3493/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5593/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3493/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5593/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3493/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5593/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3493/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5593/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5593/50000 : ℝ) ^ (8211/2048 : ℝ) ≤ (15341700111225867/100000000000000000000 : ℝ) := by
    have hpowers : (5593/50000 : ℝ)^8211 ≤ (15341700111225867/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5593 : ℕ)^8211*100000000000000000000^2048 ≤ 15341700111225867^2048*50000^8211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5593 50000 15341700111225867 100000000000000000000 8211 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5593/50000 : ℝ)) (X := (15341700111225867/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8211 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3493/25000 : ℝ) ^ (8211/2048 : ℝ) ≤ (935501711838807/2500000000000000000 : ℝ) := by
    have hpowers : (3493/25000 : ℝ)^8211 ≤ (935501711838807/2500000000000000000 : ℝ)^2048 := by
      have hnat : (3493 : ℕ)^8211*2500000000000000000^2048 ≤ 935501711838807^2048*25000^8211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3493 25000 935501711838807 2500000000000000000 8211 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3493/25000 : ℝ)) (X := (935501711838807/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8211 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015341700111225867/50000000000000000000 : ℝ) ≤ (1250095652735471/1250000000000000 : ℝ) ^ (8211/2048 : ℝ) := by
    have hpowers : (50015341700111225867/50000000000000000000 : ℝ)^2048 ≤ (1250095652735471/1250000000000000 : ℝ)^8211 := by
      have hnat : (50015341700111225867 : ℕ)^2048*1250000000000000^8211 ≤ 1250095652735471^8211*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015341700111225867 50000000000000000000 1250095652735471 1250000000000000 2048 8211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250095652735471/1250000000000000 : ℝ)) (X := (50015341700111225867/50000000000000000000 : ℝ)) (by norm_num) 8211 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052761768584778147/100000000000000000000 : ℝ) ≤ (1000131573148873/1000000000000000 : ℝ) ^ (8211/2048 : ℝ) := by
    have hpowers : (100052761768584778147/100000000000000000000 : ℝ)^2048 ≤ (1000131573148873/1000000000000000 : ℝ)^8211 := by
      have hnat : (100052761768584778147 : ℕ)^2048*1000000000000000^8211 ≤ 1000131573148873^8211*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052761768584778147 100000000000000000000 1000131573148873 1000000000000000 2048 8211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000131573148873/1000000000000000 : ℝ)) (X := (100052761768584778147/100000000000000000000 : ℝ)) (by norm_num) 8211 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250935501711838807/1250000000000000000 : ℝ) ≤ (2500466560273423/2500000000000000 : ℝ) ^ (8211/2048 : ℝ) := by
    have hpowers : (1250935501711838807/1250000000000000000 : ℝ)^2048 ≤ (2500466560273423/2500000000000000 : ℝ)^8211 := by
      have hnat : (1250935501711838807 : ℕ)^2048*2500000000000000^8211 ≤ 2500466560273423^8211*1250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250935501711838807 1250000000000000000 2500466560273423 2500000000000000 2048 8211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500466560273423/2500000000000000 : ℝ)) (X := (1250935501711838807/1250000000000000000 : ℝ)) (by norm_num) 8211 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15341700111225867/100000000000000000000 : ℝ) ≤ ((497318141201535139/497500000000000000 : ℝ)+2*(275254802481/139300000000000 : ℝ)*(5593/50000 : ℝ))^(8211/2048 : ℝ) := by
    rw [show (497318141201535139/497500000000000000 : ℝ)+2*(275254802481/139300000000000 : ℝ)*(5593/50000 : ℝ)=(1250095652735471/1250000000000000 : ℝ) by norm_num, show 1+2*(15341700111225867/100000000000000000000 : ℝ)=(50015341700111225867/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(935501711838807/2500000000000000000 : ℝ)+(15341700111225867/100000000000000000000 : ℝ) ≤ ((497318141201535139/497500000000000000 : ℝ)+(275254802481/139300000000000 : ℝ)*((3493/25000 : ℝ)+(5593/50000 : ℝ)))^(8211/2048 : ℝ) := by
    rw [show (497318141201535139/497500000000000000 : ℝ)+(275254802481/139300000000000 : ℝ)*((3493/25000 : ℝ)+(5593/50000 : ℝ))=(1000131573148873/1000000000000000 : ℝ) by norm_num, show 1+(935501711838807/2500000000000000000 : ℝ)+(15341700111225867/100000000000000000000 : ℝ)=(100052761768584778147/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(935501711838807/2500000000000000000 : ℝ) ≤ ((497318141201535139/497500000000000000 : ℝ)+2*(275254802481/139300000000000 : ℝ)*(3493/25000 : ℝ))^(8211/2048 : ℝ) := by
    rw [show (497318141201535139/497500000000000000 : ℝ)+2*(275254802481/139300000000000 : ℝ)*(3493/25000 : ℝ)=(2500466560273423/2500000000000000 : ℝ) by norm_num, show 1+2*(935501711838807/2500000000000000000 : ℝ)=(1250935501711838807/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (497318141201535139/497500000000000000 : ℝ)*(X 1 0+X 2 0)+(275254802481/139300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8211/2048 : ℝ)) (lo := (5593/50000 : ℝ)) (hi := (3493/25000 : ℝ)) (c := (497318141201535139/497500000000000000 : ℝ)) (alpha := (275254802481/139300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (497318141201535139/497500000000000000 : ℝ)*(X 0 1+X 2 1)+(275254802481/139300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8211/2048 : ℝ)) (lo := (5593/50000 : ℝ)) (hi := (3493/25000 : ℝ)) (c := (497318141201535139/497500000000000000 : ℝ)) (alpha := (275254802481/139300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (497318141201535139/497500000000000000 : ℝ)*(X 0 2+X 1 2)+(275254802481/139300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8211/2048 : ℝ)) (lo := (5593/50000 : ℝ)) (hi := (3493/25000 : ℝ)) (c := (497318141201535139/497500000000000000 : ℝ)) (alpha := (275254802481/139300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1048010677/5000000000 : ℝ)*X 0 0+(2688995689/5000000000 : ℝ)*X 0 1+(5377991073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647322019/5000000000 : ℝ)*X 1 0+(-2208719251/10000000000 : ℝ)*X 1 1+(672248909/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1058928823/2000000000 : ℝ)*X 2 0+(672248899/1250000000 : ℝ)*X 2 1+(-276089907/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2245614951/5000000000 : ℝ)*X 0 0+(4330027677/10000000000 : ℝ)*X 0 1+(866005489/2000000000 : ℝ)*X 0 2+(2245614951/5000000000 : ℝ)*X 1 0+(4330027677/10000000000 : ℝ)*X 1 1+(866005489/2000000000 : ℝ)*X 1 2+(2245614951/5000000000 : ℝ)*X 2 0+(4330027677/10000000000 : ℝ)*X 2 1+(866005489/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-471923939/2000000000 : ℝ)*X 0 0+(329959911/625000000 : ℝ)*X 0 1+(5279358401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((670565487/1250000000 : ℝ)*X 1 0+(-280891213/1250000000 : ℝ)*X 1 1+(5279358549/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2682262077/5000000000 : ℝ)*X 2 0+(2639679187/5000000000 : ℝ)*X 2 1+(-2247129593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((213652783/500000000 : ℝ)*X 0 0+(2219546381/5000000000 : ℝ)*X 0 1+(4439092877/10000000000 : ℝ)*X 0 2+(213652783/500000000 : ℝ)*X 1 0+(2219546381/5000000000 : ℝ)*X 1 1+(4439092877/10000000000 : ℝ)*X 1 2+(213652783/500000000 : ℝ)*X 2 0+(2219546381/5000000000 : ℝ)*X 2 1+(4439092877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1152326179/5000000000 : ℝ)*X 0 0+(5212524831/10000000000 : ℝ)*X 0 1+(336723997/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5287843613/10000000000 : ℝ)*X 1 0+(-2204912267/10000000000 : ℝ)*X 1 1+(2693791959/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2643921903/5000000000 : ℝ)*X 2 0+(2693792031/5000000000 : ℝ)*X 2 1+(-275613977/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4512176131/10000000000 : ℝ)*X 0 0+(4319414189/10000000000 : ℝ)*X 0 1+(1079853427/2500000000 : ℝ)*X 0 2+(4512176131/10000000000 : ℝ)*X 1 0+(4319414189/10000000000 : ℝ)*X 1 1+(1079853427/2500000000 : ℝ)*X 1 2+(4512176131/10000000000 : ℝ)*X 2 0+(4319414189/10000000000 : ℝ)*X 2 1+(1079853427/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-215138921/1000000000 : ℝ)*X 0 0+(5443451797/10000000000 : ℝ)*X 0 1+(2635692287/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1074034061/2000000000 : ℝ)*X 1 0+(-2250176469/10000000000 : ℝ)*X 1 1+(5271384551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((42961369/80000000 : ℝ)*X 2 0+(5271384887/10000000000 : ℝ)*X 2 1+(-140635933/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1063796647/2500000000 : ℝ)*X 0 0+(2223952971/5000000000 : ℝ)*X 0 1+(4343658/9765625 : ℝ)*X 0 2+(1063796647/2500000000 : ℝ)*X 1 0+(2223952971/5000000000 : ℝ)*X 1 1+(4343658/9765625 : ℝ)*X 1 2+(1063796647/2500000000 : ℝ)*X 2 0+(2223952971/5000000000 : ℝ)*X 2 1+(4343658/9765625 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-1934664222920258781833166716853/3109375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2692509/4000000000000 : ℝ)*(upper0) + (26482409/25000000000000 : ℝ)*(lower2) + (32149281/100000000000000 : ℝ)*(upper5) + (954204152110559/25000000000000 : ℝ)*(major0) + (954204152110559/25000000000000 : ℝ)*(major1) + (954204152110559/25000000000000 : ℝ)*(major2) + (165472511/6250000000000 : ℝ)*(sp2) + (1582617939/100000000000000 : ℝ)*(sp3) + (5059298250683931/100000000000000 : ℝ)*(sp4) + (5059293571459579/100000000000000 : ℝ)*(sp5) + (5059301725909277/100000000000000 : ℝ)*(sp6) + (2595067379769747/100000000000000 : ℝ)*(sp7) + (6122785521/100000000000000 : ℝ)*(sp8) + (5401004937/50000000000000 : ℝ)*(sp13) + (1297534481193843/50000000000000 : ℝ)*(f.failure) + (5059304373469453/100000000000000 : ℝ)*(f.sum) + (836250006037/995000000000000000000000000 : ℝ)*base66 + (304128171035892299/12437500000000000000000000000000 : ℝ)*base68 + (158901817937420201/12437500000000000000000000000000 : ℝ)*base69 + (26732484753357701/12437500000000000000000000000000 : ℝ)*base71 + (26158282571237/995000000000000000000000000 : ℝ)*base74 + (25117424795045201/12437500000000000000000000000000 : ℝ)*base75 + (98487537299857701/12437500000000000000000000000000 : ℝ)*base77 + (81158326125545201/12437500000000000000000000000000 : ℝ)*base79 + (2534566993073/995000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (29392531/5000000000000000000000 : ℝ)*base90 + (29392531/5000000000000000000000 : ℝ)*base92 + (29392531/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29603/50000 : ℝ) ≤ (12887145504657974274333095438319/21765625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2515811/20000000000000 : ℝ)*(upper3) + (1326699/2500000000000 : ℝ)*(upper4) + (11747511/20000000000000 : ℝ)*(lower5) + (242435825460869/6250000000000 : ℝ)*(major0) + (242435825460869/6250000000000 : ℝ)*(major1) + (242435825460869/6250000000000 : ℝ)*(major2) + (255043621915777/5000000000000 : ℝ)*(sp0) + (5100872481397423/100000000000000 : ℝ)*(sp1) + (5100870507868161/100000000000000 : ℝ)*(sp2) + (2637324536469603/100000000000000 : ℝ)*(sp3) + (2053283609/25000000000000 : ℝ)*(sp5) + (5093331849/50000000000000 : ℝ)*(sp6) + (1236877611/25000000000000 : ℝ)*(sp7) + (8256216319/100000000000000 : ℝ)*(sp8) + (1318664741990023/50000000000000 : ℝ)*(f.failure) + (5100880694531859/100000000000000 : ℝ)*(f.sum) + (218882170217/870625000000000000000000000 : ℝ)*base66 + (149832709427319463/21765625000000000000000000000000 : ℝ)*base68 + (84369831811660581/10882812500000000000000000000000 : ℝ)*base69 + (14399131284256963/21765625000000000000000000000000 : ℝ)*base72 + (4986490931147/3482500000000000000000000000 : ℝ)*base73 + (27484784974401919/10882812500000000000000000000000 : ℝ)*base76 + (6839959334088761/2720703125000000000000000000000 : ℝ)*base78 + (73338496594245669/10882812500000000000000000000000 : ℝ)*base80 + (2013136444421/6965000000000000000000000000 : ℝ)*base82 + (26999591/5000000000000000000000 : ℝ)*base90 + (26999591/5000000000000000000000 : ℝ)*base92 + (26999591/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (79423/100000 : ℝ) ≤ (13829970350236541127495309445413/17412500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2159983/100000000000000 : ℝ)*(upper1) + (7331393/50000000000000 : ℝ)*(lower3) + (298335841/100000000000000 : ℝ)*(upper4) + (293743/12500000000000 : ℝ)*(lower5) + (434729379496073/10000000000000 : ℝ)*(major0) + (434729379496073/10000000000000 : ℝ)*(major1) + (434729379496073/10000000000000 : ℝ)*(major2) + (677400583/25000000000000 : ℝ)*(sp0) + (276586112273/100000000000000 : ℝ)*(sp2) + (37717416559/20000000000000 : ℝ)*(sp3) + (2856183584408729/50000000000000 : ℝ)*(sp8) + (571236987841979/10000000000000 : ℝ)*(sp9) + (5712093292307517/100000000000000 : ℝ)*(sp10) + (2955553947869/100000000000 : ℝ)*(sp11) + (738935633737949/25000000000000 : ℝ)*(f.failure) + (571236987841979/10000000000000 : ℝ)*(f.sum) + (1413020964553/348250000000000000000000000 : ℝ)*base65 + (456058519345964029/34825000000000000000000000000000 : ℝ)*base67 + (1668246283385971/34825000000000000000000000000000 : ℝ)*base70 + (372620429444889029/34825000000000000000000000000000 : ℝ)*base71 + (11488638675221/1393000000000000000000000000 : ℝ)*base73 + (51911003993985971/34825000000000000000000000000000 : ℝ)*base76 + (195009035069614029/34825000000000000000000000000000 : ℝ)*base77 + (56507798751764029/34825000000000000000000000000000 : ℝ)*base79 + (16048740170331/1393000000000000000000000000 : ℝ)*base81 + (20195267/2500000000000000000000 : ℝ)*base89 + (20195267/2500000000000000000000 : ℝ)*base91 + (20195267/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-20711/25000 : ℝ) ≤ (-72124200037088063580950560716897/87062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2023169/2500000000000 : ℝ)*(lower0) + (161693/160000000000 : ℝ)*(lower1) + (157743861/20000000000000 : ℝ)*(lower2) + (331165073/50000000000000 : ℝ)*(upper5) + (2190767665745979/50000000000000 : ℝ)*(major0) + (2190767665745979/50000000000000 : ℝ)*(major1) + (2190767665745979/50000000000000 : ℝ)*(major2) + (3827387091/12500000000000 : ℝ)*(sp0) + (138213106891/25000000000000 : ℝ)*(sp5) + (104008504853/25000000000000 : ℝ)*(sp7) + (2905815253021307/50000000000000 : ℝ)*(sp12) + (2905554136355889/50000000000000 : ℝ)*(sp13) + (2905830562569671/50000000000000 : ℝ)*(sp14) + (372325932416387/12500000000000 : ℝ)*(sp15) + (2979023493350507/100000000000000 : ℝ)*(f.failure) + (2905830562569671/50000000000000 : ℝ)*(f.sum) + (17418857497071/3482500000000000000000000000 : ℝ)*base66 + (3139563751084082433/174125000000000000000000000000000 : ℝ)*base68 + (2149354057343332433/174125000000000000000000000000000 : ℝ)*base70 + (3134701673335582433/174125000000000000000000000000000 : ℝ)*base72 + (7864831542367/435312500000000000000000000 : ℝ)*base74 + (599265575151082433/174125000000000000000000000000000 : ℝ)*base76 + (2313437300284082433/174125000000000000000000000000000 : ℝ)*base78 + (1627990861848582433/174125000000000000000000000000000 : ℝ)*base80 + (1575332623951/3482500000000000000000000000 : ℝ)*base82 + (42398581/10000000000000000000000 : ℝ)*base89 + (42398581/10000000000000000000000 : ℝ)*base91 + (42398581/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1019_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147079583/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3493/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5593/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29603/50000 : ℝ) else (79423/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20711/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1019_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147079583/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3493/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5593/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29603/50000 : ℝ) else (79423/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20711/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_w1019_box p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
