-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1589_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:36:55.193532+00:00
-- url     : https://prove2.me/submissions/fcd7b064-4725-4010-9c75-d56c45836b08

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
theorem support_rectangle_w1589_box_0 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-62366877/400000000 : ℝ)*x 0 + (337160123/625000000 : ℝ)*x 1 + (337160127/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (62366877/400000000 : ℝ)^4675 ≤ (2314536882907/25000000000000 : ℝ)^3651 := by
    have hnat : (62366877 : ℕ)^4675*25000000000000^3651 ≤ 2314536882907^3651*400000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62366877 400000000 2314536882907 25000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337160123/625000000 : ℝ)^4675 ≤ (9074185175709/20000000000000 : ℝ)^3651 := by
    have hnat : (337160123 : ℕ)^4675*20000000000000^3651 ≤ 9074185175709^3651*625000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337160123 625000000 9074185175709 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337160127/625000000 : ℝ)^4675 ≤ (22685463283893/50000000000000 : ℝ)^3651 := by
    have hnat : (337160127 : ℕ)^4675*50000000000000^3651 ≤ 22685463283893^3651*625000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337160127 625000000 22685463283893 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-62366877/400000000 : ℝ), (337160123/625000000 : ℝ), (337160127/625000000 : ℝ)] ![(2314536882907/25000000000000 : ℝ), (9074185175709/20000000000000 : ℝ), (22685463283893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-62366877/400000000 : ℝ)|^4675 ≤ (2314536882907/25000000000000 : ℝ)^3651
        have hw : |(-62366877/400000000 : ℝ)|=(62366877/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337160123/625000000 : ℝ)|^4675 ≤ (9074185175709/20000000000000 : ℝ)^3651
        have hw : |(337160123/625000000 : ℝ)|=(337160123/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337160127/625000000 : ℝ)|^4675 ≤ (22685463283893/50000000000000 : ℝ)^3651
        have hw : |(337160127/625000000 : ℝ)|=(337160127/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_box_1 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635556053/5000000000 : ℝ)*x 0 + (-1730879457/10000000000 : ℝ)*x 1 + (1348640489/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635556053/5000000000 : ℝ)^4675 ≤ (44045735937773/100000000000000 : ℝ)^3651 := by
    have hnat : (2635556053 : ℕ)^4675*100000000000000^3651 ≤ 44045735937773^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635556053 5000000000 44045735937773 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1730879457/10000000000 : ℝ)^4675 ≤ (5291669149813/50000000000000 : ℝ)^3651 := by
    have hnat : (1730879457 : ℕ)^4675*50000000000000^3651 ≤ 5291669149813^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1730879457 10000000000 5291669149813 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348640489/2500000000 : ℝ)^4675 ≤ (708920714833/1562500000000 : ℝ)^3651 := by
    have hnat : (1348640489 : ℕ)^4675*1562500000000^3651 ≤ 708920714833^3651*2500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348640489 2500000000 708920714833 1562500000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635556053/5000000000 : ℝ), (-1730879457/10000000000 : ℝ), (1348640489/2500000000 : ℝ)] ![(44045735937773/100000000000000 : ℝ), (5291669149813/50000000000000 : ℝ), (708920714833/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635556053/5000000000 : ℝ)|^4675 ≤ (44045735937773/100000000000000 : ℝ)^3651
        have hw : |(2635556053/5000000000 : ℝ)|=(2635556053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1730879457/10000000000 : ℝ)|^4675 ≤ (5291669149813/50000000000000 : ℝ)^3651
        have hw : |(-1730879457/10000000000 : ℝ)|=(1730879457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348640489/2500000000 : ℝ)|^4675 ≤ (708920714833/1562500000000 : ℝ)^3651
        have hw : |(1348640489/2500000000 : ℝ)|=(1348640489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_box_2 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52711119/100000000 : ℝ)*x 0 + (5394562099/10000000000 : ℝ)*x 1 + (-1730879541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52711119/100000000 : ℝ)^4675 ≤ (11011433433409/25000000000000 : ℝ)^3651 := by
    have hnat : (52711119 : ℕ)^4675*25000000000000^3651 ≤ 11011433433409^3651*100000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52711119 100000000 11011433433409 25000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394562099/10000000000 : ℝ)^4675 ≤ (9074185457867/20000000000000 : ℝ)^3651 := by
    have hnat : (5394562099 : ℕ)^4675*20000000000000^3651 ≤ 9074185457867^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394562099 10000000000 9074185457867 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1730879541/10000000000 : ℝ)^4675 ≤ (2645834739323/25000000000000 : ℝ)^3651 := by
    have hnat : (1730879541 : ℕ)^4675*25000000000000^3651 ≤ 2645834739323^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1730879541 10000000000 2645834739323 25000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52711119/100000000 : ℝ), (5394562099/10000000000 : ℝ), (-1730879541/10000000000 : ℝ)] ![(11011433433409/25000000000000 : ℝ), (9074185457867/20000000000000 : ℝ), (2645834739323/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52711119/100000000 : ℝ)|^4675 ≤ (11011433433409/25000000000000 : ℝ)^3651
        have hw : |(52711119/100000000 : ℝ)|=(52711119/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394562099/10000000000 : ℝ)|^4675 ≤ (9074185457867/20000000000000 : ℝ)^3651
        have hw : |(5394562099/10000000000 : ℝ)|=(5394562099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1730879541/10000000000 : ℝ)|^4675 ≤ (2645834739323/25000000000000 : ℝ)^3651
        have hw : |(-1730879541/10000000000 : ℝ)|=(1730879541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_box_3 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4435223881/10000000000 : ℝ)*x 0 + (4141740913/10000000000 : ℝ)*x 1 + (1035435189/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4435223881/10000000000 : ℝ)^4675 ≤ (35309011612863/100000000000000 : ℝ)^3651 := by
    have hnat : (4435223881 : ℕ)^4675*100000000000000^3651 ≤ 35309011612863^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4435223881 10000000000 35309011612863 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4141740913/10000000000 : ℝ)^4675 ≤ (6469098993927/20000000000000 : ℝ)^3651 := by
    have hnat : (4141740913 : ℕ)^4675*20000000000000^3651 ≤ 6469098993927^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4141740913 10000000000 6469098993927 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035435189/2500000000 : ℝ)^4675 ≤ (32345493399633/100000000000000 : ℝ)^3651 := by
    have hnat : (1035435189 : ℕ)^4675*100000000000000^3651 ≤ 32345493399633^3651*2500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035435189 2500000000 32345493399633 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4435223881/10000000000 : ℝ), (4141740913/10000000000 : ℝ), (1035435189/2500000000 : ℝ)] ![(35309011612863/100000000000000 : ℝ), (6469098993927/20000000000000 : ℝ), (32345493399633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4435223881/10000000000 : ℝ)|^4675 ≤ (35309011612863/100000000000000 : ℝ)^3651
        have hw : |(4435223881/10000000000 : ℝ)|=(4435223881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4141740913/10000000000 : ℝ)|^4675 ≤ (6469098993927/20000000000000 : ℝ)^3651
        have hw : |(4141740913/10000000000 : ℝ)|=(4141740913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035435189/2500000000 : ℝ)|^4675 ≤ (32345493399633/100000000000000 : ℝ)^3651
        have hw : |(1035435189/2500000000 : ℝ)|=(1035435189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_box_4 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1966167553/10000000000 : ℝ)*x 0 + (5245346443/10000000000 : ℝ)*x 1 + (5245345877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1966167553/10000000000 : ℝ)^4675 ≤ (12459525225467/100000000000000 : ℝ)^3651 := by
    have hnat : (1966167553 : ℕ)^4675*100000000000000^3651 ≤ 12459525225467^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966167553 10000000000 12459525225467 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245346443/10000000000 : ℝ)^4675 ≤ (1750809616013/4000000000000 : ℝ)^3651 := by
    have hnat : (5245346443 : ℕ)^4675*4000000000000^3651 ≤ 1750809616013^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245346443 10000000000 1750809616013 4000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245345877/10000000000 : ℝ)^4675 ≤ (8754046870523/20000000000000 : ℝ)^3651 := by
    have hnat : (5245345877 : ℕ)^4675*20000000000000^3651 ≤ 8754046870523^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245345877 10000000000 8754046870523 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1966167553/10000000000 : ℝ), (5245346443/10000000000 : ℝ), (5245345877/10000000000 : ℝ)] ![(12459525225467/100000000000000 : ℝ), (1750809616013/4000000000000 : ℝ), (8754046870523/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1966167553/10000000000 : ℝ)|^4675 ≤ (12459525225467/100000000000000 : ℝ)^3651
        have hw : |(-1966167553/10000000000 : ℝ)|=(1966167553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245346443/10000000000 : ℝ)|^4675 ≤ (1750809616013/4000000000000 : ℝ)^3651
        have hw : |(5245346443/10000000000 : ℝ)|=(5245346443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245345877/10000000000 : ℝ)|^4675 ≤ (8754046870523/20000000000000 : ℝ)^3651
        have hw : |(5245345877/10000000000 : ℝ)|=(5245345877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_box_5 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4299521/8000000 : ℝ)*x 0 + (-1793469981/10000000000 : ℝ)*x 1 + (5245345821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299521/8000000 : ℝ)^4675 ≤ (45153921069537/100000000000000 : ℝ)^3651 := by
    have hnat : (4299521 : ℕ)^4675*100000000000000^3651 ≤ 45153921069537^3651*8000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299521 8000000 45153921069537 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1793469981/10000000000 : ℝ)^4675 ≤ (11075845159101/100000000000000 : ℝ)^3651 := by
    have hnat : (1793469981 : ℕ)^4675*100000000000000^3651 ≤ 11075845159101^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793469981 10000000000 11075845159101 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245345821/10000000000 : ℝ)^4675 ≤ (8754046750851/20000000000000 : ℝ)^3651 := by
    have hnat : (5245345821 : ℕ)^4675*20000000000000^3651 ≤ 8754046750851^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245345821 10000000000 8754046750851 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299521/8000000 : ℝ), (-1793469981/10000000000 : ℝ), (5245345821/10000000000 : ℝ)] ![(45153921069537/100000000000000 : ℝ), (11075845159101/100000000000000 : ℝ), (8754046750851/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299521/8000000 : ℝ)|^4675 ≤ (45153921069537/100000000000000 : ℝ)^3651
        have hw : |(4299521/8000000 : ℝ)|=(4299521/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1793469981/10000000000 : ℝ)|^4675 ≤ (11075845159101/100000000000000 : ℝ)^3651
        have hw : |(-1793469981/10000000000 : ℝ)|=(1793469981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245345821/10000000000 : ℝ)|^4675 ≤ (8754046750851/20000000000000 : ℝ)^3651
        have hw : |(5245345821/10000000000 : ℝ)|=(5245345821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_box_6 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33589999/62500000 : ℝ)*x 0 + (1311336699/2500000000 : ℝ)*x 1 + (-896735291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33589999/62500000 : ℝ)^4675 ≤ (45153905900631/100000000000000 : ℝ)^3651 := by
    have hnat : (33589999 : ℕ)^4675*100000000000000^3651 ≤ 45153905900631^3651*62500000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33589999 62500000 45153905900631 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311336699/2500000000 : ℝ)^4675 ≤ (4377024417213/10000000000000 : ℝ)^3651 := by
    have hnat : (1311336699 : ℕ)^4675*10000000000000^3651 ≤ 4377024417213^3651*2500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311336699 2500000000 4377024417213 10000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896735291/5000000000 : ℝ)^4675 ≤ (2215169982331/20000000000000 : ℝ)^3651 := by
    have hnat : (896735291 : ℕ)^4675*20000000000000^3651 ≤ 2215169982331^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896735291 5000000000 2215169982331 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33589999/62500000 : ℝ), (1311336699/2500000000 : ℝ), (-896735291/5000000000 : ℝ)] ![(45153905900631/100000000000000 : ℝ), (4377024417213/10000000000000 : ℝ), (2215169982331/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33589999/62500000 : ℝ)|^4675 ≤ (45153905900631/100000000000000 : ℝ)^3651
        have hw : |(33589999/62500000 : ℝ)|=(33589999/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311336699/2500000000 : ℝ)|^4675 ≤ (4377024417213/10000000000000 : ℝ)^3651
        have hw : |(1311336699/2500000000 : ℝ)|=(1311336699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-896735291/5000000000 : ℝ)|^4675 ≤ (2215169982331/20000000000000 : ℝ)^3651
        have hw : |(-896735291/5000000000 : ℝ)|=(896735291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_box_7 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4032429059/10000000000 : ℝ)*x 0 + (4343013441/10000000000 : ℝ)*x 1 + (4343012159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4032429059/10000000000 : ℝ)^4675 ≤ (31256446540749/100000000000000 : ℝ)^3651 := by
    have hnat : (4032429059 : ℕ)^4675*100000000000000^3651 ≤ 31256446540749^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032429059 10000000000 31256446540749 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4343013441/10000000000 : ℝ)^4675 ≤ (34371783218443/100000000000000 : ℝ)^3651 := by
    have hnat : (4343013441 : ℕ)^4675*100000000000000^3651 ≤ 34371783218443^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343013441 10000000000 34371783218443 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4343012159/10000000000 : ℝ)^4675 ≤ (34371770226663/100000000000000 : ℝ)^3651 := by
    have hnat : (4343012159 : ℕ)^4675*100000000000000^3651 ≤ 34371770226663^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343012159 10000000000 34371770226663 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4032429059/10000000000 : ℝ), (4343013441/10000000000 : ℝ), (4343012159/10000000000 : ℝ)] ![(31256446540749/100000000000000 : ℝ), (34371783218443/100000000000000 : ℝ), (34371770226663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4032429059/10000000000 : ℝ)|^4675 ≤ (31256446540749/100000000000000 : ℝ)^3651
        have hw : |(4032429059/10000000000 : ℝ)|=(4032429059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4343013441/10000000000 : ℝ)|^4675 ≤ (34371783218443/100000000000000 : ℝ)^3651
        have hw : |(4343013441/10000000000 : ℝ)|=(4343013441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4343012159/10000000000 : ℝ)|^4675 ≤ (34371770226663/100000000000000 : ℝ)^3651
        have hw : |(4343012159/10000000000 : ℝ)|=(4343012159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_box_8 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-117488979/625000000 : ℝ)*x 0 + (5140025339/10000000000 : ℝ)*x 1 + (2707384841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (117488979/625000000 : ℝ)^4675 ≤ (2940816634901/25000000000000 : ℝ)^3651 := by
    have hnat : (117488979 : ℕ)^4675*25000000000000^3651 ≤ 2940816634901^3651*625000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117488979 625000000 2940816634901 25000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5140025339/10000000000 : ℝ)^4675 ≤ (42648068530947/100000000000000 : ℝ)^3651 := by
    have hnat : (5140025339 : ℕ)^4675*100000000000000^3651 ≤ 42648068530947^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140025339 10000000000 42648068530947 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707384841/5000000000 : ℝ)^4675 ≤ (45588664917261/100000000000000 : ℝ)^3651 := by
    have hnat : (2707384841 : ℕ)^4675*100000000000000^3651 ≤ 45588664917261^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707384841 5000000000 45588664917261 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-117488979/625000000 : ℝ), (5140025339/10000000000 : ℝ), (2707384841/5000000000 : ℝ)] ![(2940816634901/25000000000000 : ℝ), (42648068530947/100000000000000 : ℝ), (45588664917261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-117488979/625000000 : ℝ)|^4675 ≤ (2940816634901/25000000000000 : ℝ)^3651
        have hw : |(-117488979/625000000 : ℝ)|=(117488979/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5140025339/10000000000 : ℝ)|^4675 ≤ (42648068530947/100000000000000 : ℝ)^3651
        have hw : |(5140025339/10000000000 : ℝ)|=(5140025339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707384841/5000000000 : ℝ)|^4675 ≤ (45588664917261/100000000000000 : ℝ)^3651
        have hw : |(2707384841/5000000000 : ℝ)|=(2707384841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_box_9 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628560521/5000000000 : ℝ)*x 0 + (-430543867/2500000000 : ℝ)*x 1 + (270738501/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628560521/5000000000 : ℝ)^4675 ≤ (1371752861791/3125000000000 : ℝ)^3651 := by
    have hnat : (2628560521 : ℕ)^4675*3125000000000^3651 ≤ 1371752861791^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628560521 5000000000 1371752861791 3125000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430543867/2500000000 : ℝ)^4675 ≤ (2628809962293/25000000000000 : ℝ)^3651 := by
    have hnat : (430543867 : ℕ)^4675*25000000000000^3651 ≤ 2628809962293^3651*2500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430543867 2500000000 2628809962293 25000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270738501/500000000 : ℝ)^4675 ≤ (9117733712227/20000000000000 : ℝ)^3651 := by
    have hnat : (270738501 : ℕ)^4675*20000000000000^3651 ≤ 9117733712227^3651*500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270738501 500000000 9117733712227 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628560521/5000000000 : ℝ), (-430543867/2500000000 : ℝ), (270738501/500000000 : ℝ)] ![(1371752861791/3125000000000 : ℝ), (2628809962293/25000000000000 : ℝ), (9117733712227/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628560521/5000000000 : ℝ)|^4675 ≤ (1371752861791/3125000000000 : ℝ)^3651
        have hw : |(2628560521/5000000000 : ℝ)|=(2628560521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430543867/2500000000 : ℝ)|^4675 ≤ (2628809962293/25000000000000 : ℝ)^3651
        have hw : |(-430543867/2500000000 : ℝ)|=(430543867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270738501/500000000 : ℝ)|^4675 ≤ (9117733712227/20000000000000 : ℝ)^3651
        have hw : |(270738501/500000000 : ℝ)|=(270738501/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_box_10 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628560931/5000000000 : ℝ)*x 0 + (5414769123/10000000000 : ℝ)*x 1 + (-1722175583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628560931/5000000000 : ℝ)^4675 ≤ (10974025086131/25000000000000 : ℝ)^3651 := by
    have hnat : (2628560931 : ℕ)^4675*25000000000000^3651 ≤ 10974025086131^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628560931 5000000000 10974025086131 25000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414769123/10000000000 : ℝ)^4675 ≤ (22794329445427/50000000000000 : ℝ)^3651 := by
    have hnat : (5414769123 : ℕ)^4675*50000000000000^3651 ≤ 22794329445427^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414769123 10000000000 22794329445427 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1722175583/10000000000 : ℝ)^4675 ≤ (420609629931/4000000000000 : ℝ)^3651 := by
    have hnat : (1722175583 : ℕ)^4675*4000000000000^3651 ≤ 420609629931^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722175583 10000000000 420609629931 4000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628560931/5000000000 : ℝ), (5414769123/10000000000 : ℝ), (-1722175583/10000000000 : ℝ)] ![(10974025086131/25000000000000 : ℝ), (22794329445427/50000000000000 : ℝ), (420609629931/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628560931/5000000000 : ℝ)|^4675 ≤ (10974025086131/25000000000000 : ℝ)^3651
        have hw : |(2628560931/5000000000 : ℝ)|=(2628560931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414769123/10000000000 : ℝ)|^4675 ≤ (22794329445427/50000000000000 : ℝ)^3651
        have hw : |(5414769123/10000000000 : ℝ)|=(5414769123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1722175583/10000000000 : ℝ)|^4675 ≤ (420609629931/4000000000000 : ℝ)^3651
        have hw : |(-1722175583/10000000000 : ℝ)|=(1722175583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_box_11 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2244314179/5000000000 : ℝ)*x 0 + (4114450051/10000000000 : ℝ)*x 1 + (1028612401/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2244314179/5000000000 : ℝ)^4675 ≤ (17927163705127/50000000000000 : ℝ)^3651 := by
    have hnat : (2244314179 : ℕ)^4675*50000000000000^3651 ≤ 17927163705127^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244314179 5000000000 17927163705127 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4114450051/10000000000 : ℝ)^4675 ≤ (4009104814651/12500000000000 : ℝ)^3651 := by
    have hnat : (4114450051 : ℕ)^4675*12500000000000^3651 ≤ 4009104814651^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4114450051 10000000000 4009104814651 12500000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028612401/2500000000 : ℝ)^4675 ≤ (16036417027741/50000000000000 : ℝ)^3651 := by
    have hnat : (1028612401 : ℕ)^4675*50000000000000^3651 ≤ 16036417027741^3651*2500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028612401 2500000000 16036417027741 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2244314179/5000000000 : ℝ), (4114450051/10000000000 : ℝ), (1028612401/2500000000 : ℝ)] ![(17927163705127/50000000000000 : ℝ), (4009104814651/12500000000000 : ℝ), (16036417027741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2244314179/5000000000 : ℝ)|^4675 ≤ (17927163705127/50000000000000 : ℝ)^3651
        have hw : |(2244314179/5000000000 : ℝ)|=(2244314179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4114450051/10000000000 : ℝ)|^4675 ≤ (4009104814651/12500000000000 : ℝ)^3651
        have hw : |(4114450051/10000000000 : ℝ)|=(4114450051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1028612401/2500000000 : ℝ)|^4675 ≤ (16036417027741/50000000000000 : ℝ)^3651
        have hw : |(1028612401/2500000000 : ℝ)|=(1028612401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_box_12 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1645093577/10000000000 : ℝ)*x 0 + (5496725157/10000000000 : ℝ)*x 1 + (2615149073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1645093577/10000000000 : ℝ)^4675 ≤ (247910390651/2500000000000 : ℝ)^3651 := by
    have hnat : (1645093577 : ℕ)^4675*2500000000000^3651 ≤ 247910390651^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1645093577 10000000000 247910390651 2500000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5496725157/10000000000 : ℝ)^4675 ≤ (23237035144611/50000000000000 : ℝ)^3651 := by
    have hnat : (5496725157 : ℕ)^4675*50000000000000^3651 ≤ 23237035144611^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496725157 10000000000 23237035144611 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615149073/5000000000 : ℝ)^4675 ≤ (43609514077139/100000000000000 : ℝ)^3651 := by
    have hnat : (2615149073 : ℕ)^4675*100000000000000^3651 ≤ 43609514077139^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615149073 5000000000 43609514077139 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1645093577/10000000000 : ℝ), (5496725157/10000000000 : ℝ), (2615149073/5000000000 : ℝ)] ![(247910390651/2500000000000 : ℝ), (23237035144611/50000000000000 : ℝ), (43609514077139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1645093577/10000000000 : ℝ)|^4675 ≤ (247910390651/2500000000000 : ℝ)^3651
        have hw : |(-1645093577/10000000000 : ℝ)|=(1645093577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5496725157/10000000000 : ℝ)|^4675 ≤ (23237035144611/50000000000000 : ℝ)^3651
        have hw : |(5496725157/10000000000 : ℝ)|=(5496725157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615149073/5000000000 : ℝ)|^4675 ≤ (43609514077139/100000000000000 : ℝ)^3651
        have hw : |(2615149073/5000000000 : ℝ)|=(2615149073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_box_13 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5384819331/10000000000 : ℝ)*x 0 + (-1799614573/10000000000 : ℝ)*x 1 + (2615148951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5384819331/10000000000 : ℝ)^4675 ≤ (4526603017373/10000000000000 : ℝ)^3651 := by
    have hnat : (5384819331 : ℕ)^4675*10000000000000^3651 ≤ 4526603017373^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384819331 10000000000 4526603017373 10000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1799614573/10000000000 : ℝ)^4675 ≤ (2224891667951/20000000000000 : ℝ)^3651 := by
    have hnat : (1799614573 : ℕ)^4675*20000000000000^3651 ≤ 2224891667951^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799614573 10000000000 2224891667951 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615148951/5000000000 : ℝ)^4675 ≤ (43609511472099/100000000000000 : ℝ)^3651 := by
    have hnat : (2615148951 : ℕ)^4675*100000000000000^3651 ≤ 43609511472099^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615148951 5000000000 43609511472099 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5384819331/10000000000 : ℝ), (-1799614573/10000000000 : ℝ), (2615148951/5000000000 : ℝ)] ![(4526603017373/10000000000000 : ℝ), (2224891667951/20000000000000 : ℝ), (43609511472099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5384819331/10000000000 : ℝ)|^4675 ≤ (4526603017373/10000000000000 : ℝ)^3651
        have hw : |(5384819331/10000000000 : ℝ)|=(5384819331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1799614573/10000000000 : ℝ)|^4675 ≤ (2224891667951/20000000000000 : ℝ)^3651
        have hw : |(-1799614573/10000000000 : ℝ)|=(1799614573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615148951/5000000000 : ℝ)|^4675 ≤ (43609511472099/100000000000000 : ℝ)^3651
        have hw : |(2615148951/5000000000 : ℝ)|=(2615148951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_box_14 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1346204819/2500000000 : ℝ)*x 0 + (2615148849/5000000000 : ℝ)*x 1 + (-899807461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346204819/2500000000 : ℝ)^4675 ≤ (22633014790857/50000000000000 : ℝ)^3651 := by
    have hnat : (1346204819 : ℕ)^4675*50000000000000^3651 ≤ 22633014790857^3651*2500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346204819 2500000000 22633014790857 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2615148849/5000000000 : ℝ)^4675 ≤ (8721901858823/20000000000000 : ℝ)^3651 := by
    have hnat : (2615148849 : ℕ)^4675*20000000000000^3651 ≤ 8721901858823^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615148849 5000000000 8721901858823 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899807461/5000000000 : ℝ)^4675 ≤ (5562230551103/50000000000000 : ℝ)^3651 := by
    have hnat : (899807461 : ℕ)^4675*50000000000000^3651 ≤ 5562230551103^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899807461 5000000000 5562230551103 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1346204819/2500000000 : ℝ), (2615148849/5000000000 : ℝ), (-899807461/5000000000 : ℝ)] ![(22633014790857/50000000000000 : ℝ), (8721901858823/20000000000000 : ℝ), (5562230551103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1346204819/2500000000 : ℝ)|^4675 ≤ (22633014790857/50000000000000 : ℝ)^3651
        have hw : |(1346204819/2500000000 : ℝ)|=(1346204819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2615148849/5000000000 : ℝ)|^4675 ≤ (8721901858823/20000000000000 : ℝ)^3651
        have hw : |(2615148849/5000000000 : ℝ)|=(2615148849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-899807461/5000000000 : ℝ)|^4675 ≤ (5562230551103/50000000000000 : ℝ)^3651
        have hw : |(-899807461/5000000000 : ℝ)|=(899807461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_box_15 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1995472061/5000000000 : ℝ)*x 0 + (4363285801/10000000000 : ℝ)*x 1 + (4363285049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1995472061/5000000000 : ℝ)^4675 ≤ (1233811701939/4000000000000 : ℝ)^3651 := by
    have hnat : (1995472061 : ℕ)^4675*4000000000000^3651 ≤ 1233811701939^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995472061 5000000000 1233811701939 4000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4363285801/10000000000 : ℝ)^4675 ≤ (8644339384139/25000000000000 : ℝ)^3651 := by
    have hnat : (4363285801 : ℕ)^4675*25000000000000^3651 ≤ 8644339384139^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363285801 10000000000 8644339384139 25000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4363285049/10000000000 : ℝ)^4675 ≤ (4322168738229/12500000000000 : ℝ)^3651 := by
    have hnat : (4363285049 : ℕ)^4675*12500000000000^3651 ≤ 4322168738229^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363285049 10000000000 4322168738229 12500000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1995472061/5000000000 : ℝ), (4363285801/10000000000 : ℝ), (4363285049/10000000000 : ℝ)] ![(1233811701939/4000000000000 : ℝ), (8644339384139/25000000000000 : ℝ), (4322168738229/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1995472061/5000000000 : ℝ)|^4675 ≤ (1233811701939/4000000000000 : ℝ)^3651
        have hw : |(1995472061/5000000000 : ℝ)|=(1995472061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4363285801/10000000000 : ℝ)|^4675 ≤ (8644339384139/25000000000000 : ℝ)^3651
        have hw : |(4363285801/10000000000 : ℝ)|=(4363285801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4363285049/10000000000 : ℝ)|^4675 ≤ (4322168738229/12500000000000 : ℝ)^3651
        have hw : |(4363285049/10000000000 : ℝ)|=(4363285049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1589_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63863/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58993/100000 : ℝ) ∧ (20277/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (43241/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11181/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11181/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11181/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11181/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11181/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11181/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11181/100000 : ℝ) ^ (4673/1024 : ℝ) ≤ (2273703028834319/50000000000000000000 : ℝ) := by
    have hpowers : (11181/100000 : ℝ)^4673 ≤ (2273703028834319/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11181 : ℕ)^4673*50000000000000000000^1024 ≤ 2273703028834319^1024*100000^4673 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11181 100000 2273703028834319 50000000000000000000 4673 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11181/100000 : ℝ)) (X := (2273703028834319/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4673/1024 : ℝ) ≤ (20087357067932809/100000000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4673 ≤ (20087357067932809/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4673*100000000000000000000^1024 ≤ 20087357067932809^1024*100000^4673 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 20087357067932809 100000000000000000000 4673 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (20087357067932809/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002273703028834319/25000000000000000000 : ℝ) ≤ (5000099644306901/5000000000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (25002273703028834319/25000000000000000000 : ℝ)^1024 ≤ (5000099644306901/5000000000000000 : ℝ)^4673 := by
      have hnat : (25002273703028834319 : ℕ)^1024*5000000000000000^4673 ≤ 5000099644306901^4673*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002273703028834319 25000000000000000000 5000099644306901 5000000000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000099644306901/5000000000000000 : ℝ)) (X := (25002273703028834319/25000000000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100024634763125601447/100000000000000000000 : ℝ) ≤ (5000269886277483/5000000000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (100024634763125601447/100000000000000000000 : ℝ)^1024 ≤ (5000269886277483/5000000000000000 : ℝ)^4673 := by
      have hnat : (100024634763125601447 : ℕ)^1024*5000000000000000^4673 ≤ 5000269886277483^4673*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100024634763125601447 100000000000000000000 5000269886277483 5000000000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000269886277483/5000000000000000 : ℝ)) (X := (100024634763125601447/100000000000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020087357067932809/50000000000000000000 : ℝ) ≤ (1000088025649613/1000000000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (50020087357067932809/50000000000000000000 : ℝ)^1024 ≤ (1000088025649613/1000000000000000 : ℝ)^4673 := by
      have hnat : (50020087357067932809 : ℕ)^1024*1000000000000000^4673 ≤ 1000088025649613^4673*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020087357067932809 50000000000000000000 1000088025649613 1000000000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000088025649613/1000000000000000 : ℝ)) (X := (50020087357067932809/50000000000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2273703028834319/50000000000000000000 : ℝ) ≤ ((3584436953143688903/3585000000000000000 : ℝ)+2*(85120985291/107550000000000 : ℝ)*(11181/100000 : ℝ))^(4673/1024 : ℝ) := by
    rw [show (3584436953143688903/3585000000000000000 : ℝ)+2*(85120985291/107550000000000 : ℝ)*(11181/100000 : ℝ)=(5000099644306901/5000000000000000 : ℝ) by norm_num, show 1+2*(2273703028834319/50000000000000000000 : ℝ)=(25002273703028834319/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20087357067932809/100000000000000000000 : ℝ)+(2273703028834319/50000000000000000000 : ℝ) ≤ ((3584436953143688903/3585000000000000000 : ℝ)+(85120985291/107550000000000 : ℝ)*((15483/100000 : ℝ)+(11181/100000 : ℝ)))^(4673/1024 : ℝ) := by
    rw [show (3584436953143688903/3585000000000000000 : ℝ)+(85120985291/107550000000000 : ℝ)*((15483/100000 : ℝ)+(11181/100000 : ℝ))=(5000269886277483/5000000000000000 : ℝ) by norm_num, show 1+(20087357067932809/100000000000000000000 : ℝ)+(2273703028834319/50000000000000000000 : ℝ)=(100024634763125601447/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20087357067932809/100000000000000000000 : ℝ) ≤ ((3584436953143688903/3585000000000000000 : ℝ)+2*(85120985291/107550000000000 : ℝ)*(15483/100000 : ℝ))^(4673/1024 : ℝ) := by
    rw [show (3584436953143688903/3585000000000000000 : ℝ)+2*(85120985291/107550000000000 : ℝ)*(15483/100000 : ℝ)=(1000088025649613/1000000000000000 : ℝ) by norm_num, show 1+2*(20087357067932809/100000000000000000000 : ℝ)=(50020087357067932809/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3584436953143688903/3585000000000000000 : ℝ)*(X 1 0+X 2 0)+(85120985291/107550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (11181/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (3584436953143688903/3585000000000000000 : ℝ)) (alpha := (85120985291/107550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3584436953143688903/3585000000000000000 : ℝ)*(X 0 1+X 2 1)+(85120985291/107550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (11181/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (3584436953143688903/3585000000000000000 : ℝ)) (alpha := (85120985291/107550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3584436953143688903/3585000000000000000 : ℝ)*(X 0 2+X 1 2)+(85120985291/107550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (11181/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (3584436953143688903/3585000000000000000 : ℝ)) (alpha := (85120985291/107550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-62366877/400000000 : ℝ)*X 0 0+(337160123/625000000 : ℝ)*X 0 1+(337160127/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2635556053/5000000000 : ℝ)*X 1 0+(-1730879457/10000000000 : ℝ)*X 1 1+(1348640489/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((52711119/100000000 : ℝ)*X 2 0+(5394562099/10000000000 : ℝ)*X 2 1+(-1730879541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4435223881/10000000000 : ℝ)*X 0 0+(4141740913/10000000000 : ℝ)*X 0 1+(1035435189/2500000000 : ℝ)*X 0 2+(4435223881/10000000000 : ℝ)*X 1 0+(4141740913/10000000000 : ℝ)*X 1 1+(1035435189/2500000000 : ℝ)*X 1 2+(4435223881/10000000000 : ℝ)*X 2 0+(4141740913/10000000000 : ℝ)*X 2 1+(1035435189/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1966167553/10000000000 : ℝ)*X 0 0+(5245346443/10000000000 : ℝ)*X 0 1+(5245345877/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4299521/8000000 : ℝ)*X 1 0+(-1793469981/10000000000 : ℝ)*X 1 1+(5245345821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((33589999/62500000 : ℝ)*X 2 0+(1311336699/2500000000 : ℝ)*X 2 1+(-896735291/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4032429059/10000000000 : ℝ)*X 0 0+(4343013441/10000000000 : ℝ)*X 0 1+(4343012159/10000000000 : ℝ)*X 0 2+(4032429059/10000000000 : ℝ)*X 1 0+(4343013441/10000000000 : ℝ)*X 1 1+(4343012159/10000000000 : ℝ)*X 1 2+(4032429059/10000000000 : ℝ)*X 2 0+(4343013441/10000000000 : ℝ)*X 2 1+(4343012159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-117488979/625000000 : ℝ)*X 0 0+(5140025339/10000000000 : ℝ)*X 0 1+(2707384841/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628560521/5000000000 : ℝ)*X 1 0+(-430543867/2500000000 : ℝ)*X 1 1+(270738501/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2628560931/5000000000 : ℝ)*X 2 0+(5414769123/10000000000 : ℝ)*X 2 1+(-1722175583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2244314179/5000000000 : ℝ)*X 0 0+(4114450051/10000000000 : ℝ)*X 0 1+(1028612401/2500000000 : ℝ)*X 0 2+(2244314179/5000000000 : ℝ)*X 1 0+(4114450051/10000000000 : ℝ)*X 1 1+(1028612401/2500000000 : ℝ)*X 1 2+(2244314179/5000000000 : ℝ)*X 2 0+(4114450051/10000000000 : ℝ)*X 2 1+(1028612401/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1645093577/10000000000 : ℝ)*X 0 0+(5496725157/10000000000 : ℝ)*X 0 1+(2615149073/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5384819331/10000000000 : ℝ)*X 1 0+(-1799614573/10000000000 : ℝ)*X 1 1+(2615148951/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1346204819/2500000000 : ℝ)*X 2 0+(2615148849/5000000000 : ℝ)*X 2 1+(-899807461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1995472061/5000000000 : ℝ)*X 0 0+(4363285801/10000000000 : ℝ)*X 0 1+(4363285049/10000000000 : ℝ)*X 0 2+(1995472061/5000000000 : ℝ)*X 1 0+(4363285801/10000000000 : ℝ)*X 1 1+(4363285049/10000000000 : ℝ)*X 1 2+(1995472061/5000000000 : ℝ)*X 2 0+(4363285801/10000000000 : ℝ)*X 2 1+(4363285049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63863/100000 : ℝ) ≤ (-19078443598662539376297136561891/29875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37237099/20000000000000 : ℝ)*(upper1) + (256629347/100000000000000 : ℝ)*(upper3) + (1518111/500000000000 : ℝ)*(lower4) + (3799523/12500000000000 : ℝ)*(lower5) + (1167430707930399/50000000000000 : ℝ)*(major0) + (1167430707930399/50000000000000 : ℝ)*(major1) + (1167430707930399/50000000000000 : ℝ)*(major2) + (5964644301/100000000000000 : ℝ)*(sp1) + (6471799589/100000000000000 : ℝ)*(sp3) + (207123498288263/6250000000000 : ℝ)*(sp4) + (828492501991977/25000000000000 : ℝ)*(sp5) + (165693902007039/5000000000000 : ℝ)*(sp6) + (688513676834067/50000000000000 : ℝ)*(sp7) + (97932471429/100000000000000 : ℝ)*(sp14) + (1377033825467723/100000000000000 : ℝ)*(f.failure) + (207123498288263/6250000000000 : ℝ)*(f.sum) + (150508424077/3585000000000000000000000000 : ℝ)*base65 + (1035966568199212297/179250000000000000000000000000000 : ℝ)*base67 + (1190675986477462297/179250000000000000000000000000000 : ℝ)*base69 + (686440947813712297/179250000000000000000000000000000 : ℝ)*base71 + (2854568921201/1792500000000000000000000000 : ℝ)*base73 + (1186363445143462297/179250000000000000000000000000000 : ℝ)*base75 + (487859247947212297/179250000000000000000000000000000 : ℝ)*base77 + (379869412542712297/179250000000000000000000000000000 : ℝ)*base79 + (725606902501/448125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (25431069/10000000000000000000000 : ℝ)*base89 + (25431069/10000000000000000000000 : ℝ)*base91 + (25431069/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58993/100000 : ℝ) ≤ (17625007810168951114831683179301/29875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32985397/100000000000000 : ℝ)*(lower0) + (20783907/100000000000000 : ℝ)*(upper1) + (64949251/100000000000000 : ℝ)*(upper2) + (1208202872199111/50000000000000 : ℝ)*(major0) + (1208202872199111/50000000000000 : ℝ)*(major1) + (1208202872199111/50000000000000 : ℝ)*(major2) + (21175122133853/625000000000 : ℝ)*(sp0) + (1694009919355651/50000000000000 : ℝ)*(sp1) + (423502421216809/12500000000000 : ℝ)*(sp2) + (44535115048647/3125000000000 : ℝ)*(sp3) + (27101627/50000000000000 : ℝ)*(sp5) + (104636017/20000000000000 : ℝ)*(sp6) + (2633644371/100000000000000 : ℝ)*(sp11) + (351498077/100000000000000 : ℝ)*(sp12) + (356281578800269/25000000000000 : ℝ)*(f.failure) + (3388019892914557/100000000000000 : ℝ)*(f.sum) + (6213711170821/1195000000000000000000000000 : ℝ)*base65 + (228589501841788411/59750000000000000000000000000000 : ℝ)*base67 + (306075661488788411/59750000000000000000000000000000 : ℝ)*base69 + (470253685509788411/59750000000000000000000000000000 : ℝ)*base71 + (1540356708781/1195000000000000000000000000 : ℝ)*base73 + (740626916759788411/59750000000000000000000000000000 : ℝ)*base75 + (299863792651788411/59750000000000000000000000000000 : ℝ)*base77 + (432260601966538411/59750000000000000000000000000000 : ℝ)*base79 + (3195665073793/597500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (37314507/2500000000000000000000 : ℝ)*base89 + (37314507/2500000000000000000000 : ℝ)*base91 + (37314507/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (20277/25000 : ℝ) ≤ (3028954393942995875351480488663/3734375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1852659/4000000000000 : ℝ)*(lower3) + (133589321/100000000000000 : ℝ)*(upper4) + (27076353/50000000000000 : ℝ)*(lower5) + (162508779538807/6250000000000 : ℝ)*(major0) + (162508779538807/6250000000000 : ℝ)*(major1) + (162508779538807/6250000000000 : ℝ)*(major2) + (58920004971/50000000000000 : ℝ)*(sp1) + (192641593/10000000000000 : ℝ)*(sp3) + (707206099/50000000000000 : ℝ)*(sp4) + (1819876328847717/50000000000000 : ℝ)*(sp8) + (113738708193109/3125000000000 : ℝ)*(sp9) + (363975650218943/10000000000000 : ℝ)*(sp10) + (766742912348051/50000000000000 : ℝ)*(sp11) + (1215040899/50000000000000 : ℝ)*(sp12) + (1533487751112031/100000000000000 : ℝ)*(f.failure) + (363975650218943/10000000000000 : ℝ)*(f.sum) + (17582146322683/5377500000000000000000000000 : ℝ)*base66 + (813126396273711337/67218750000000000000000000000000 : ℝ)*base68 + (377200798061586337/67218750000000000000000000000000 : ℝ)*base70 + (423612411779211337/67218750000000000000000000000000 : ℝ)*base72 + (19639963303393/5377500000000000000000000000 : ℝ)*base74 + (604247597926273837/67218750000000000000000000000000 : ℝ)*base76 + (486540878813961337/67218750000000000000000000000000 : ℝ)*base78 + (746369019910086337/67218750000000000000000000000000 : ℝ)*base80 + (586489106353/5377500000000000000000000000 : ℝ)*base82 + (27212393/10000000000000000000000 : ℝ)*base89 + (27212393/10000000000000000000000 : ℝ)*base91 + (27212393/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-43241/50000 : ℝ) ≤ (-12917894138583011958547520136531/14937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (108967511/100000000000000 : ℝ)*(lower0) + (41140151/100000000000000 : ℝ)*(upper1) + (2838353/6250000000000 : ℝ)*(upper3) + (109862801/100000000000000 : ℝ)*(lower4) + (660273081457359/25000000000000 : ℝ)*(major0) + (660273081457359/25000000000000 : ℝ)*(major1) + (660273081457359/25000000000000 : ℝ)*(major2) + (63700339593/100000000000000 : ℝ)*(sp5) + (14931977997/10000000000000 : ℝ)*(sp6) + (92831021/25000000000000 : ℝ)*(sp7) + (234585701396511/6250000000000 : ℝ)*(sp12) + (3753307522004583/100000000000000 : ℝ)*(sp13) + (1876610951282103/50000000000000 : ℝ)*(sp14) + (778819800000691/50000000000000 : ℝ)*(sp15) + (1557639971325467/100000000000000 : ℝ)*(f.failure) + (234585701396511/6250000000000 : ℝ)*(f.sum) + (643980410119/224062500000000000000000000 : ℝ)*base65 + (1288509571840037177/89625000000000000000000000000000 : ℝ)*base67 + (1419985224427037177/89625000000000000000000000000000 : ℝ)*base69 + (1015315263011912177/89625000000000000000000000000000 : ℝ)*base71 + (2181369235847/1792500000000000000000000000 : ℝ)*base73 + (1221378194115662177/89625000000000000000000000000000 : ℝ)*base75 + (1064881971954287177/89625000000000000000000000000000 : ℝ)*base77 + (457521066353537177/89625000000000000000000000000000 : ℝ)*base79 + (23756246321207/1792500000000000000000000000 : ℝ)*base81 + (80264499/10000000000000000000000 : ℝ)*base90 + (80264499/10000000000000000000000 : ℝ)*base92 + (80264499/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1589_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63863/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58993/100000 : ℝ) else (20277/25000 : ℝ) ≤ X j i ∧ X j i ≤ (43241/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1589_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1589_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63863/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58993/100000 : ℝ) else (20277/25000 : ℝ) ≤ X j i ∧ X j i ≤ (43241/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1589_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11181/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63863/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58993/100000 : ℝ) else (20277/25000 : ℝ) ≤ X j i ∧ X j i ≤ (43241/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1589_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
