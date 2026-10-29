-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1537_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:06:17.846491+00:00
-- url     : https://prove2.me/submissions/ebb11ba3-695f-4639-be16-493b57d49cc0

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
theorem support_rectangle_w1537_s6_0 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1831707437/10000000000 : ℝ)*x 0 + (678749989/1250000000 : ℝ)*x 1 + (5218801957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1831707437/10000000000 : ℝ)^4571 ≤ (11221388413007/100000000000000 : ℝ)^3547 := by
    have hnat : (1831707437 : ℕ)^4571*100000000000000^3547 ≤ 11221388413007^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831707437 10000000000 11221388413007 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678749989/1250000000 : ℝ)^4571 ≤ (22761870531307/50000000000000 : ℝ)^3547 := by
    have hnat : (678749989 : ℕ)^4571*50000000000000^3547 ≤ 22761870531307^3547*1250000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678749989 1250000000 22761870531307 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218801957/10000000000 : ℝ)^4571 ≤ (43254870509243/100000000000000 : ℝ)^3547 := by
    have hnat : (5218801957 : ℕ)^4571*100000000000000^3547 ≤ 43254870509243^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218801957 10000000000 43254870509243 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1831707437/10000000000 : ℝ), (678749989/1250000000 : ℝ), (5218801957/10000000000 : ℝ)] ![(11221388413007/100000000000000 : ℝ), (22761870531307/50000000000000 : ℝ), (43254870509243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1831707437/10000000000 : ℝ)|^4571 ≤ (11221388413007/100000000000000 : ℝ)^3547
        have hw : |(-1831707437/10000000000 : ℝ)|=(1831707437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678749989/1250000000 : ℝ)|^4571 ≤ (22761870531307/50000000000000 : ℝ)^3547
        have hw : |(678749989/1250000000 : ℝ)|=(678749989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218801957/10000000000 : ℝ)|^4571 ≤ (43254870509243/100000000000000 : ℝ)^3547
        have hw : |(5218801957/10000000000 : ℝ)|=(5218801957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s6_1 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350166269/10000000000 : ℝ)*x 0 + (-484954921/2500000000 : ℝ)*x 1 + (5218801673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350166269/10000000000 : ℝ)^4571 ≤ (44663048193639/100000000000000 : ℝ)^3547 := by
    have hnat : (5350166269 : ℕ)^4571*100000000000000^3547 ≤ 44663048193639^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350166269 10000000000 44663048193639 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (484954921/2500000000 : ℝ)^4571 ≤ (12082084318757/100000000000000 : ℝ)^3547 := by
    have hnat : (484954921 : ℕ)^4571*100000000000000^3547 ≤ 12082084318757^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484954921 2500000000 12082084318757 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218801673/10000000000 : ℝ)^4571 ≤ (43254867475823/100000000000000 : ℝ)^3547 := by
    have hnat : (5218801673 : ℕ)^4571*100000000000000^3547 ≤ 43254867475823^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218801673 10000000000 43254867475823 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350166269/10000000000 : ℝ), (-484954921/2500000000 : ℝ), (5218801673/10000000000 : ℝ)] ![(44663048193639/100000000000000 : ℝ), (12082084318757/100000000000000 : ℝ), (43254867475823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350166269/10000000000 : ℝ)|^4571 ≤ (44663048193639/100000000000000 : ℝ)^3547
        have hw : |(5350166269/10000000000 : ℝ)|=(5350166269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-484954921/2500000000 : ℝ)|^4571 ≤ (12082084318757/100000000000000 : ℝ)^3547
        have hw : |(-484954921/2500000000 : ℝ)|=(484954921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218801673/10000000000 : ℝ)|^4571 ≤ (43254867475823/100000000000000 : ℝ)^3547
        have hw : |(5218801673/10000000000 : ℝ)|=(5218801673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s6_2 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675083151/5000000000 : ℝ)*x 0 + (260940087/500000000 : ℝ)*x 1 + (-38796391/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675083151/5000000000 : ℝ)^4571 ≤ (11165762137163/25000000000000 : ℝ)^3547 := by
    have hnat : (2675083151 : ℕ)^4571*25000000000000^3547 ≤ 11165762137163^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675083151 5000000000 11165762137163 25000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260940087/500000000 : ℝ)^4571 ≤ (21627434095727/50000000000000 : ℝ)^3547 := by
    have hnat : (260940087 : ℕ)^4571*50000000000000^3547 ≤ 21627434095727^3547*500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260940087 500000000 21627434095727 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38796391/200000000 : ℝ)^4571 ≤ (2416416648639/20000000000000 : ℝ)^3547 := by
    have hnat : (38796391 : ℕ)^4571*20000000000000^3547 ≤ 2416416648639^3547*200000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38796391 200000000 2416416648639 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675083151/5000000000 : ℝ), (260940087/500000000 : ℝ), (-38796391/200000000 : ℝ)] ![(11165762137163/25000000000000 : ℝ), (21627434095727/50000000000000 : ℝ), (2416416648639/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675083151/5000000000 : ℝ)|^4571 ≤ (11165762137163/25000000000000 : ℝ)^3547
        have hw : |(2675083151/5000000000 : ℝ)|=(2675083151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260940087/500000000 : ℝ)|^4571 ≤ (21627434095727/50000000000000 : ℝ)^3547
        have hw : |(260940087/500000000 : ℝ)|=(260940087/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38796391/200000000 : ℝ)|^4571 ≤ (2416416648639/20000000000000 : ℝ)^3547
        have hw : |(-38796391/200000000 : ℝ)|=(38796391/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s6_3 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (851653939/2000000000 : ℝ)*x 0 + (4020390171/10000000000 : ℝ)*x 1 + (4507748531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851653939/2000000000 : ℝ)^4571 ≤ (33280876362383/100000000000000 : ℝ)^3547 := by
    have hnat : (851653939 : ℕ)^4571*100000000000000^3547 ≤ 33280876362383^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851653939 2000000000 33280876362383 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4020390171/10000000000 : ℝ)^4571 ≤ (30904558329041/100000000000000 : ℝ)^3547 := by
    have hnat : (4020390171 : ℕ)^4571*100000000000000^3547 ≤ 30904558329041^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4020390171 10000000000 30904558329041 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507748531/10000000000 : ℝ)^4571 ≤ (17907282644989/50000000000000 : ℝ)^3547 := by
    have hnat : (4507748531 : ℕ)^4571*50000000000000^3547 ≤ 17907282644989^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507748531 10000000000 17907282644989 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(851653939/2000000000 : ℝ), (4020390171/10000000000 : ℝ), (4507748531/10000000000 : ℝ)] ![(33280876362383/100000000000000 : ℝ), (30904558329041/100000000000000 : ℝ), (17907282644989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(851653939/2000000000 : ℝ)|^4571 ≤ (33280876362383/100000000000000 : ℝ)^3547
        have hw : |(851653939/2000000000 : ℝ)|=(851653939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4020390171/10000000000 : ℝ)|^4571 ≤ (30904558329041/100000000000000 : ℝ)^3547
        have hw : |(4020390171/10000000000 : ℝ)|=(4020390171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507748531/10000000000 : ℝ)|^4571 ≤ (17907282644989/50000000000000 : ℝ)^3547
        have hw : |(4507748531/10000000000 : ℝ)|=(4507748531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s6_4 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-457933641/2500000000 : ℝ)*x 0 + (5219895133/10000000000 : ℝ)*x 1 + (2714449649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (457933641/2500000000 : ℝ)^4571 ≤ (5610801287701/50000000000000 : ℝ)^3547 := by
    have hnat : (457933641 : ℕ)^4571*50000000000000^3547 ≤ 5610801287701^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457933641 2500000000 5610801287701 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219895133/10000000000 : ℝ)^4571 ≤ (43266547137433/100000000000000 : ℝ)^3547 := by
    have hnat : (5219895133 : ℕ)^4571*100000000000000^3547 ≤ 43266547137433^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219895133 10000000000 43266547137433 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714449649/5000000000 : ℝ)^4571 ≤ (22755925139443/50000000000000 : ℝ)^3547 := by
    have hnat : (2714449649 : ℕ)^4571*50000000000000^3547 ≤ 22755925139443^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714449649 5000000000 22755925139443 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-457933641/2500000000 : ℝ), (5219895133/10000000000 : ℝ), (2714449649/5000000000 : ℝ)] ![(5610801287701/50000000000000 : ℝ), (43266547137433/100000000000000 : ℝ), (22755925139443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-457933641/2500000000 : ℝ)|^4571 ≤ (5610801287701/50000000000000 : ℝ)^3547
        have hw : |(-457933641/2500000000 : ℝ)|=(457933641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219895133/10000000000 : ℝ)|^4571 ≤ (43266547137433/100000000000000 : ℝ)^3547
        have hw : |(5219895133/10000000000 : ℝ)|=(5219895133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714449649/5000000000 : ℝ)|^4571 ≤ (22755925139443/50000000000000 : ℝ)^3547
        have hw : |(2714449649/5000000000 : ℝ)|=(2714449649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s6_5 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294526977/10000000000 : ℝ)*x 0 + (-216215763/1250000000 : ℝ)*x 1 + (1085778793/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294526977/10000000000 : ℝ)^4571 ≤ (11016345510001/25000000000000 : ℝ)^3547 := by
    have hnat : (5294526977 : ℕ)^4571*25000000000000^3547 ≤ 11016345510001^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294526977 10000000000 11016345510001 25000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216215763/1250000000 : ℝ)^4571 ≤ (10422825286147/100000000000000 : ℝ)^3547 := by
    have hnat : (216215763 : ℕ)^4571*100000000000000^3547 ≤ 10422825286147^3547*1250000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216215763 1250000000 10422825286147 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085778793/2000000000 : ℝ)^4571 ≤ (45511792664059/100000000000000 : ℝ)^3547 := by
    have hnat : (1085778793 : ℕ)^4571*100000000000000^3547 ≤ 45511792664059^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085778793 2000000000 45511792664059 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294526977/10000000000 : ℝ), (-216215763/1250000000 : ℝ), (1085778793/2000000000 : ℝ)] ![(11016345510001/25000000000000 : ℝ), (10422825286147/100000000000000 : ℝ), (45511792664059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294526977/10000000000 : ℝ)|^4571 ≤ (11016345510001/25000000000000 : ℝ)^3547
        have hw : |(5294526977/10000000000 : ℝ)|=(5294526977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-216215763/1250000000 : ℝ)|^4571 ≤ (10422825286147/100000000000000 : ℝ)^3547
        have hw : |(-216215763/1250000000 : ℝ)|=(216215763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085778793/2000000000 : ℝ)|^4571 ≤ (45511792664059/100000000000000 : ℝ)^3547
        have hw : |(1085778793/2000000000 : ℝ)|=(1085778793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s6_6 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058905349/2000000000 : ℝ)*x 0 + (1085779659/2000000000 : ℝ)*x 1 + (-1729720399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058905349/2000000000 : ℝ)^4571 ≤ (5508172443959/12500000000000 : ℝ)^3547 := by
    have hnat : (1058905349 : ℕ)^4571*12500000000000^3547 ≤ 5508172443959^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058905349 2000000000 5508172443959 12500000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085779659/2000000000 : ℝ)^4571 ≤ (45511839443019/100000000000000 : ℝ)^3547 := by
    have hnat : (1085779659 : ℕ)^4571*100000000000000^3547 ≤ 45511839443019^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085779659 2000000000 45511839443019 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1729720399/10000000000 : ℝ)^4571 ≤ (521139049257/5000000000000 : ℝ)^3547 := by
    have hnat : (1729720399 : ℕ)^4571*5000000000000^3547 ≤ 521139049257^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1729720399 10000000000 521139049257 5000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058905349/2000000000 : ℝ), (1085779659/2000000000 : ℝ), (-1729720399/10000000000 : ℝ)] ![(5508172443959/12500000000000 : ℝ), (45511839443019/100000000000000 : ℝ), (521139049257/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058905349/2000000000 : ℝ)|^4571 ≤ (5508172443959/12500000000000 : ℝ)^3547
        have hw : |(1058905349/2000000000 : ℝ)|=(1058905349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085779659/2000000000 : ℝ)|^4571 ≤ (45511839443019/100000000000000 : ℝ)^3547
        have hw : |(1085779659/2000000000 : ℝ)|=(1085779659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1729720399/10000000000 : ℝ)|^4571 ≤ (521139049257/5000000000000 : ℝ)^3547
        have hw : |(-1729720399/10000000000 : ℝ)|=(1729720399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s6_7 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4258336747/10000000000 : ℝ)*x 0 + (450522973/1000000000 : ℝ)*x 1 + (4022924949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4258336747/10000000000 : ℝ)^4571 ≤ (2080096981581/6250000000000 : ℝ)^3547 := by
    have hnat : (4258336747 : ℕ)^4571*6250000000000^3547 ≤ 2080096981581^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4258336747 10000000000 2080096981581 6250000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450522973/1000000000 : ℝ)^4571 ≤ (3578877781269/10000000000000 : ℝ)^3547 := by
    have hnat : (450522973 : ℕ)^4571*10000000000000^3547 ≤ 3578877781269^3547*1000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450522973 1000000000 3578877781269 10000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4022924949/10000000000 : ℝ)^4571 ≤ (15464835237221/50000000000000 : ℝ)^3547 := by
    have hnat : (4022924949 : ℕ)^4571*50000000000000^3547 ≤ 15464835237221^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022924949 10000000000 15464835237221 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4258336747/10000000000 : ℝ), (450522973/1000000000 : ℝ), (4022924949/10000000000 : ℝ)] ![(2080096981581/6250000000000 : ℝ), (3578877781269/10000000000000 : ℝ), (15464835237221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4258336747/10000000000 : ℝ)|^4571 ≤ (2080096981581/6250000000000 : ℝ)^3547
        have hw : |(4258336747/10000000000 : ℝ)|=(4258336747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(450522973/1000000000 : ℝ)|^4571 ≤ (3578877781269/10000000000000 : ℝ)^3547
        have hw : |(450522973/1000000000 : ℝ)|=(450522973/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4022924949/10000000000 : ℝ)|^4571 ≤ (15464835237221/50000000000000 : ℝ)^3547
        have hw : |(4022924949/10000000000 : ℝ)|=(4022924949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s6_8 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-26386781/2000000000 : ℝ)*x 0 + (1164268337/2000000000 : ℝ)*x 1 + (5824210837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26386781/2000000000 : ℝ)^4571 ≤ (378192864063/100000000000000 : ℝ)^3547 := by
    have hnat : (26386781 : ℕ)^4571*100000000000000^3547 ≤ 378192864063^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26386781 2000000000 378192864063 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1164268337/2000000000 : ℝ)^4571 ≤ (49795088605911/100000000000000 : ℝ)^3547 := by
    have hnat : (1164268337 : ℕ)^4571*100000000000000^3547 ≤ 49795088605911^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1164268337 2000000000 49795088605911 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5824210837/10000000000 : ℝ)^4571 ≤ (4982671851187/10000000000000 : ℝ)^3547 := by
    have hnat : (5824210837 : ℕ)^4571*10000000000000^3547 ≤ 4982671851187^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5824210837 10000000000 4982671851187 10000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-26386781/2000000000 : ℝ), (1164268337/2000000000 : ℝ), (5824210837/10000000000 : ℝ)] ![(378192864063/100000000000000 : ℝ), (49795088605911/100000000000000 : ℝ), (4982671851187/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-26386781/2000000000 : ℝ)|^4571 ≤ (378192864063/100000000000000 : ℝ)^3547
        have hw : |(-26386781/2000000000 : ℝ)|=(26386781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1164268337/2000000000 : ℝ)|^4571 ≤ (49795088605911/100000000000000 : ℝ)^3547
        have hw : |(1164268337/2000000000 : ℝ)|=(1164268337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5824210837/10000000000 : ℝ)|^4571 ≤ (4982671851187/10000000000000 : ℝ)^3547
        have hw : |(5824210837/10000000000 : ℝ)|=(5824210837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s6_9 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1324951679/10000000000 : ℝ)*x 0 + (-816278053/2500000000 : ℝ)*x 1 + (1499148197/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1324951679/10000000000 : ℝ)^4571 ≤ (924046617573/12500000000000 : ℝ)^3547 := by
    have hnat : (1324951679 : ℕ)^4571*12500000000000^3547 ≤ 924046617573^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324951679 10000000000 924046617573 12500000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (816278053/2500000000 : ℝ)^4571 ≤ (2954425881221/12500000000000 : ℝ)^3547 := by
    have hnat : (816278053 : ℕ)^4571*12500000000000^3547 ≤ 2954425881221^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      816278053 2500000000 2954425881221 12500000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1499148197/2000000000 : ℝ)^4571 ≤ (68972220006601/100000000000000 : ℝ)^3547 := by
    have hnat : (1499148197 : ℕ)^4571*100000000000000^3547 ≤ 68972220006601^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499148197 2000000000 68972220006601 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1324951679/10000000000 : ℝ), (-816278053/2500000000 : ℝ), (1499148197/2000000000 : ℝ)] ![(924046617573/12500000000000 : ℝ), (2954425881221/12500000000000 : ℝ), (68972220006601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1324951679/10000000000 : ℝ)|^4571 ≤ (924046617573/12500000000000 : ℝ)^3547
        have hw : |(1324951679/10000000000 : ℝ)|=(1324951679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-816278053/2500000000 : ℝ)|^4571 ≤ (2954425881221/12500000000000 : ℝ)^3547
        have hw : |(-816278053/2500000000 : ℝ)|=(816278053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1499148197/2000000000 : ℝ)|^4571 ≤ (68972220006601/100000000000000 : ℝ)^3547
        have hw : |(1499148197/2000000000 : ℝ)|=(1499148197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_s6_10 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1420965799/10000000000 : ℝ)*x 0 + (5468682097/10000000000 : ℝ)*x 1 + (5471082129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1420965799/10000000000 : ℝ)^4571 ≤ (8089823250081/100000000000000 : ℝ)^3547 := by
    have hnat : (1420965799 : ℕ)^4571*100000000000000^3547 ≤ 8089823250081^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1420965799 10000000000 8089823250081 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468682097/10000000000 : ℝ)^4571 ≤ (45942095863121/100000000000000 : ℝ)^3547 := by
    have hnat : (5468682097 : ℕ)^4571*100000000000000^3547 ≤ 45942095863121^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468682097 10000000000 45942095863121 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471082129/10000000000 : ℝ)^4571 ≤ (45968080861823/100000000000000 : ℝ)^3547 := by
    have hnat : (5471082129 : ℕ)^4571*100000000000000^3547 ≤ 45968080861823^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471082129 10000000000 45968080861823 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1420965799/10000000000 : ℝ), (5468682097/10000000000 : ℝ), (5471082129/10000000000 : ℝ)] ![(8089823250081/100000000000000 : ℝ), (45942095863121/100000000000000 : ℝ), (45968080861823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1420965799/10000000000 : ℝ)|^4571 ≤ (8089823250081/100000000000000 : ℝ)^3547
        have hw : |(1420965799/10000000000 : ℝ)|=(1420965799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468682097/10000000000 : ℝ)|^4571 ≤ (45942095863121/100000000000000 : ℝ)^3547
        have hw : |(5468682097/10000000000 : ℝ)|=(5468682097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471082129/10000000000 : ℝ)|^4571 ≤ (45968080861823/100000000000000 : ℝ)^3547
        have hw : |(5471082129/10000000000 : ℝ)|=(5471082129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1537_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11009/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (344/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (344/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (344/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (344/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (344/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (344/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (344/3125 : ℝ) ^ (4569/1024 : ℝ) ≤ (1059779032557749/20000000000000000000 : ℝ) := by
    have hpowers : (344/3125 : ℝ)^4569 ≤ (1059779032557749/20000000000000000000 : ℝ)^1024 := by
      have hnat : (344 : ℕ)^4569*20000000000000000000^1024 ≤ 1059779032557749^1024*3125^4569 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        344 3125 1059779032557749 20000000000000000000 4569 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (344/3125 : ℝ)) (X := (1059779032557749/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4569/1024 : ℝ) ≤ (12145724867527593/50000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4569 ≤ (12145724867527593/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4569*50000000000000000000^1024 ≤ 12145724867527593^1024*20000^4569 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 12145724867527593 50000000000000000000 4569 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (12145724867527593/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001059779032557749/10000000000000000000 : ℝ) ≤ (10000237506919593/10000000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (10001059779032557749/10000000000000000000 : ℝ)^1024 ≤ (10000237506919593/10000000000000000 : ℝ)^4569 := by
      have hnat : (10001059779032557749 : ℕ)^1024*10000000000000000^4569 ≤ 10000237506919593^4569*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001059779032557749 10000000000000000000 10000237506919593 10000000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000237506919593/10000000000000000 : ℝ)) (X := (10001059779032557749/10000000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029590344897843931/100000000000000000000 : ℝ) ≤ (10000663099923399/10000000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (100029590344897843931/100000000000000000000 : ℝ)^1024 ≤ (10000663099923399/10000000000000000 : ℝ)^4569 := by
      have hnat : (100029590344897843931 : ℕ)^1024*10000000000000000^4569 ≤ 10000663099923399^4569*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029590344897843931 100000000000000000000 10000663099923399 10000000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000663099923399/10000000000000000 : ℝ)) (X := (100029590344897843931/100000000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012145724867527593/25000000000000000000 : ℝ) ≤ (2000217738585441/2000000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (25012145724867527593/25000000000000000000 : ℝ)^1024 ≤ (2000217738585441/2000000000000000 : ℝ)^4569 := by
      have hnat : (25012145724867527593 : ℕ)^1024*2000000000000000^4569 ≤ 2000217738585441^4569*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012145724867527593 25000000000000000000 2000217738585441 2000000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000217738585441/2000000000000000 : ℝ)) (X := (25012145724867527593/25000000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1059779032557749/20000000000000000000 : ℝ) ≤ ((8952338692581444993/8954000000000000000 : ℝ)+2*(212796501903/223850000000000 : ℝ)*(344/3125 : ℝ))^(4569/1024 : ℝ) := by
    rw [show (8952338692581444993/8954000000000000000 : ℝ)+2*(212796501903/223850000000000 : ℝ)*(344/3125 : ℝ)=(10000237506919593/10000000000000000 : ℝ) by norm_num, show 1+2*(1059779032557749/20000000000000000000 : ℝ)=(10001059779032557749/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12145724867527593/50000000000000000000 : ℝ)+(1059779032557749/20000000000000000000 : ℝ) ≤ ((8952338692581444993/8954000000000000000 : ℝ)+(212796501903/223850000000000 : ℝ)*((3097/20000 : ℝ)+(344/3125 : ℝ)))^(4569/1024 : ℝ) := by
    rw [show (8952338692581444993/8954000000000000000 : ℝ)+(212796501903/223850000000000 : ℝ)*((3097/20000 : ℝ)+(344/3125 : ℝ))=(10000663099923399/10000000000000000 : ℝ) by norm_num, show 1+(12145724867527593/50000000000000000000 : ℝ)+(1059779032557749/20000000000000000000 : ℝ)=(100029590344897843931/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12145724867527593/50000000000000000000 : ℝ) ≤ ((8952338692581444993/8954000000000000000 : ℝ)+2*(212796501903/223850000000000 : ℝ)*(3097/20000 : ℝ))^(4569/1024 : ℝ) := by
    rw [show (8952338692581444993/8954000000000000000 : ℝ)+2*(212796501903/223850000000000 : ℝ)*(3097/20000 : ℝ)=(2000217738585441/2000000000000000 : ℝ) by norm_num, show 1+2*(12145724867527593/50000000000000000000 : ℝ)=(25012145724867527593/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8952338692581444993/8954000000000000000 : ℝ)*(X 1 0+X 2 0)+(212796501903/223850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (344/3125 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (8952338692581444993/8954000000000000000 : ℝ)) (alpha := (212796501903/223850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8952338692581444993/8954000000000000000 : ℝ)*(X 0 1+X 2 1)+(212796501903/223850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (344/3125 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (8952338692581444993/8954000000000000000 : ℝ)) (alpha := (212796501903/223850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8952338692581444993/8954000000000000000 : ℝ)*(X 0 2+X 1 2)+(212796501903/223850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (344/3125 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (8952338692581444993/8954000000000000000 : ℝ)) (alpha := (212796501903/223850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1831707437/10000000000 : ℝ)*X 0 0+(678749989/1250000000 : ℝ)*X 0 1+(5218801957/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350166269/10000000000 : ℝ)*X 1 0+(-484954921/2500000000 : ℝ)*X 1 1+(5218801673/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675083151/5000000000 : ℝ)*X 2 0+(260940087/500000000 : ℝ)*X 2 1+(-38796391/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((851653939/2000000000 : ℝ)*X 0 0+(4020390171/10000000000 : ℝ)*X 0 1+(4507748531/10000000000 : ℝ)*X 0 2+(851653939/2000000000 : ℝ)*X 1 0+(4020390171/10000000000 : ℝ)*X 1 1+(4507748531/10000000000 : ℝ)*X 1 2+(851653939/2000000000 : ℝ)*X 2 0+(4020390171/10000000000 : ℝ)*X 2 1+(4507748531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-457933641/2500000000 : ℝ)*X 0 0+(5219895133/10000000000 : ℝ)*X 0 1+(2714449649/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294526977/10000000000 : ℝ)*X 1 0+(-216215763/1250000000 : ℝ)*X 1 1+(1085778793/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058905349/2000000000 : ℝ)*X 2 0+(1085779659/2000000000 : ℝ)*X 2 1+(-1729720399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4258336747/10000000000 : ℝ)*X 0 0+(450522973/1000000000 : ℝ)*X 0 1+(4022924949/10000000000 : ℝ)*X 0 2+(4258336747/10000000000 : ℝ)*X 1 0+(450522973/1000000000 : ℝ)*X 1 1+(4022924949/10000000000 : ℝ)*X 1 2+(4258336747/10000000000 : ℝ)*X 2 0+(450522973/1000000000 : ℝ)*X 2 1+(4022924949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-26386781/2000000000 : ℝ)*X 0 0+(1164268337/2000000000 : ℝ)*X 0 1+(5824210837/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s6_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1324951679/10000000000 : ℝ)*X 1 0+(-816278053/2500000000 : ℝ)*X 1 1+(1499148197/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s6_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1420965799/10000000000 : ℝ)*X 0 0+(5468682097/10000000000 : ℝ)*X 0 1+(5471082129/10000000000 : ℝ)*X 0 2+(1420965799/10000000000 : ℝ)*X 1 0+(5468682097/10000000000 : ℝ)*X 1 1+(5471082129/10000000000 : ℝ)*X 1 2+(1420965799/10000000000 : ℝ)*X 2 0+(5468682097/10000000000 : ℝ)*X 2 1+(5471082129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_s6_10 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4053636423219147946495002099/447700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (249300317/50000000000000 : ℝ)*(lower2) + (158379199/100000000000000 : ℝ)*(lower3) + (154863339/100000000000000 : ℝ)*(lower4) + (9608471/10000000000000 : ℝ)*(lower5) + (1696691241243641/50000000000000 : ℝ)*(major0) + (1696691241243641/50000000000000 : ℝ)*(major1) + (3393382482487283/100000000000000 : ℝ)*(major2) + (946976828627681/20000000000000 : ℝ)*(sp0) + (4734886788654021/100000000000000 : ℝ)*(sp1) + (2367443801898033/50000000000000 : ℝ)*(sp2) + (512969128091513/25000000000000 : ℝ)*(sp3) + (547000483/100000000000000 : ℝ)*(sp7) + (3460657661/100000000000000 : ℝ)*(sp8) + (163028409/20000000000000 : ℝ)*(sp9) + (1025938529683267/50000000000000 : ℝ)*(f.failure) + (2367443801898033/50000000000000 : ℝ)*(f.sum) + (4658928749697/1119250000000000000000000000 : ℝ)*base66 + (436142440664380487/447700000000000000000000000000000 : ℝ)*base68 + (1565209903668964019/895400000000000000000000000000000 : ℝ)*base69 + (3843475447572980487/447700000000000000000000000000000 : ℝ)*base72 + (14086200255267/4477000000000000000000000000 : ℝ)*base74 + (2427425828102564019/895400000000000000000000000000000 : ℝ)*base75 + (884721479736640487/447700000000000000000000000000000 : ℝ)*base78 + (3036268491353940487/447700000000000000000000000000000 : ℝ)*base80 + (94550935269123/22385000000000000000000000000 : ℝ)*base82 + (1143259/200000000000000000000 : ℝ)*base89 + (1143259/200000000000000000000 : ℝ)*base91 + (856741/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (178260428331834540091392051/447700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (445708219/50000000000000 : ℝ)*(upper1) + (31047657/10000000000000 : ℝ)*(lower2) + (232121529/12500000000000 : ℝ)*(lower3) + (214317919751491/6250000000000 : ℝ)*(major0) + (214317919751491/6250000000000 : ℝ)*(major1) + (3429086716023857/100000000000000 : ℝ)*(major2) + (3030087207/4000000000000 : ℝ)*(sp2) + (39696090863/100000000000000 : ℝ)*(sp3) + (4784702099599021/100000000000000 : ℝ)*(sp4) + (4784707075532351/100000000000000 : ℝ)*(sp5) + (299039457709511/6250000000000 : ℝ)*(sp6) + (414684292500203/20000000000000 : ℝ)*(sp7) + (497593333/10000000000000 : ℝ)*(sp8) + (2592325579/50000000000000 : ℝ)*(sp10) + (1036733171621517/50000000000000 : ℝ)*(f.failure) + (4784707075532351/100000000000000 : ℝ)*(f.sum) + (173645419962291/22385000000000000000000000000 : ℝ)*base66 + (942893196467637937/55962500000000000000000000000000 : ℝ)*base68 + (11856734877205281999/895400000000000000000000000000000 : ℝ)*base70 + (723405219664625437/55962500000000000000000000000000 : ℝ)*base72 + (43121443829993/11192500000000000000000000000 : ℝ)*base74 + (15028489924169081999/895400000000000000000000000000000 : ℝ)*base76 + (1014812212438270437/55962500000000000000000000000000 : ℝ)*base78 + (1020380261087757937/55962500000000000000000000000000 : ℝ)*base80 + (38874882900881/5596250000000000000000000000 : ℝ)*base82 + (36491/200000000000000000000 : ℝ)*base90 + (36491/200000000000000000000 : ℝ)*base92 + (2036491/200000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1537_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11009/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1537_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1537_box_0 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-101402987/625000000 : ℝ)*x 0 + (5400133987/10000000000 : ℝ)*x 1 + (2700067241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (101402987/625000000 : ℝ)^4571 ≤ (9597347704917/100000000000000 : ℝ)^3547 := by
    have hnat : (101402987 : ℕ)^4571*100000000000000^3547 ≤ 9597347704917^3547*625000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101402987 625000000 9597347704917 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400133987/10000000000 : ℝ)^4571 ≤ (22600661733391/50000000000000 : ℝ)^3547 := by
    have hnat : (5400133987 : ℕ)^4571*50000000000000^3547 ≤ 22600661733391^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400133987 10000000000 22600661733391 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700067241/5000000000 : ℝ)^4571 ≤ (22600664403149/50000000000000 : ℝ)^3547 := by
    have hnat : (2700067241 : ℕ)^4571*50000000000000^3547 ≤ 22600664403149^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700067241 5000000000 22600664403149 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-101402987/625000000 : ℝ), (5400133987/10000000000 : ℝ), (2700067241/5000000000 : ℝ)] ![(9597347704917/100000000000000 : ℝ), (22600661733391/50000000000000 : ℝ), (22600664403149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-101402987/625000000 : ℝ)|^4571 ≤ (9597347704917/100000000000000 : ℝ)^3547
        have hw : |(-101402987/625000000 : ℝ)|=(101402987/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400133987/10000000000 : ℝ)|^4571 ≤ (22600661733391/50000000000000 : ℝ)^3547
        have hw : |(5400133987/10000000000 : ℝ)|=(5400133987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700067241/5000000000 : ℝ)|^4571 ≤ (22600664403149/50000000000000 : ℝ)^3547
        have hw : |(2700067241/5000000000 : ℝ)|=(2700067241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_box_1 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635513231/5000000000 : ℝ)*x 0 + (-900858823/5000000000 : ℝ)*x 1 + (5400134187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635513231/5000000000 : ℝ)^4571 ≤ (8762697454199/20000000000000 : ℝ)^3547 := by
    have hnat : (2635513231 : ℕ)^4571*20000000000000^3547 ≤ 8762697454199^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635513231 5000000000 8762697454199 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900858823/5000000000 : ℝ)^4571 ≤ (10985187084331/100000000000000 : ℝ)^3547 := by
    have hnat : (900858823 : ℕ)^4571*100000000000000^3547 ≤ 10985187084331^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900858823 5000000000 10985187084331 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400134187/10000000000 : ℝ)^4571 ≤ (22600662812081/50000000000000 : ℝ)^3547 := by
    have hnat : (5400134187 : ℕ)^4571*50000000000000^3547 ≤ 22600662812081^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400134187 10000000000 22600662812081 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635513231/5000000000 : ℝ), (-900858823/5000000000 : ℝ), (5400134187/10000000000 : ℝ)] ![(8762697454199/20000000000000 : ℝ), (10985187084331/100000000000000 : ℝ), (22600662812081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635513231/5000000000 : ℝ)|^4571 ≤ (8762697454199/20000000000000 : ℝ)^3547
        have hw : |(2635513231/5000000000 : ℝ)|=(2635513231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-900858823/5000000000 : ℝ)|^4571 ≤ (10985187084331/100000000000000 : ℝ)^3547
        have hw : |(-900858823/5000000000 : ℝ)|=(900858823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400134187/10000000000 : ℝ)|^4571 ≤ (22600662812081/50000000000000 : ℝ)^3547
        have hw : |(5400134187/10000000000 : ℝ)|=(5400134187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_box_2 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271025707/10000000000 : ℝ)*x 0 + (1080026977/2000000000 : ℝ)*x 1 + (-1801717717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271025707/10000000000 : ℝ)^4571 ≤ (43813479183583/100000000000000 : ℝ)^3547 := by
    have hnat : (5271025707 : ℕ)^4571*100000000000000^3547 ≤ 43813479183583^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271025707 10000000000 43813479183583 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080026977/2000000000 : ℝ)^4571 ≤ (45201333153419/100000000000000 : ℝ)^3547 := by
    have hnat : (1080026977 : ℕ)^4571*100000000000000^3547 ≤ 45201333153419^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080026977 2000000000 45201333153419 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1801717717/10000000000 : ℝ)^4571 ≤ (2746296910549/25000000000000 : ℝ)^3547 := by
    have hnat : (1801717717 : ℕ)^4571*25000000000000^3547 ≤ 2746296910549^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1801717717 10000000000 2746296910549 25000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271025707/10000000000 : ℝ), (1080026977/2000000000 : ℝ), (-1801717717/10000000000 : ℝ)] ![(43813479183583/100000000000000 : ℝ), (45201333153419/100000000000000 : ℝ), (2746296910549/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271025707/10000000000 : ℝ)|^4571 ≤ (43813479183583/100000000000000 : ℝ)^3547
        have hw : |(5271025707/10000000000 : ℝ)|=(5271025707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080026977/2000000000 : ℝ)|^4571 ≤ (45201333153419/100000000000000 : ℝ)^3547
        have hw : |(1080026977/2000000000 : ℝ)|=(1080026977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1801717717/10000000000 : ℝ)|^4571 ≤ (2746296910549/25000000000000 : ℝ)^3547
        have hw : |(-1801717717/10000000000 : ℝ)|=(1801717717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_box_3 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4460247199/10000000000 : ℝ)*x 0 + (130128351/312500000 : ℝ)*x 1 + (4164107467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4460247199/10000000000 : ℝ)^4571 ≤ (35328949208737/100000000000000 : ℝ)^3547 := by
    have hnat : (4460247199 : ℕ)^4571*100000000000000^3547 ≤ 35328949208737^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4460247199 10000000000 35328949208737 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130128351/312500000 : ℝ)^4571 ≤ (3233552421179/10000000000000 : ℝ)^3547 := by
    have hnat : (130128351 : ℕ)^4571*10000000000000^3547 ≤ 3233552421179^3547*312500000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130128351 312500000 3233552421179 10000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4164107467/10000000000 : ℝ)^4571 ≤ (32335526563457/100000000000000 : ℝ)^3547 := by
    have hnat : (4164107467 : ℕ)^4571*100000000000000^3547 ≤ 32335526563457^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164107467 10000000000 32335526563457 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4460247199/10000000000 : ℝ), (130128351/312500000 : ℝ), (4164107467/10000000000 : ℝ)] ![(35328949208737/100000000000000 : ℝ), (3233552421179/10000000000000 : ℝ), (32335526563457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4460247199/10000000000 : ℝ)|^4571 ≤ (35328949208737/100000000000000 : ℝ)^3547
        have hw : |(4460247199/10000000000 : ℝ)|=(4460247199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130128351/312500000 : ℝ)|^4571 ≤ (3233552421179/10000000000000 : ℝ)^3547
        have hw : |(130128351/312500000 : ℝ)|=(130128351/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4164107467/10000000000 : ℝ)|^4571 ≤ (32335526563457/100000000000000 : ℝ)^3547
        have hw : |(4164107467/10000000000 : ℝ)|=(4164107467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_box_4 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-511596671/2500000000 : ℝ)*x 0 + (2622174101/5000000000 : ℝ)*x 1 + (5244348433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (511596671/2500000000 : ℝ)^4571 ≤ (3236037387003/25000000000000 : ℝ)^3547 := by
    have hnat : (511596671 : ℕ)^4571*25000000000000^3547 ≤ 3236037387003^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511596671 2500000000 3236037387003 25000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622174101/5000000000 : ℝ)^4571 ≤ (21763961992233/50000000000000 : ℝ)^3547 := by
    have hnat : (2622174101 : ℕ)^4571*50000000000000^3547 ≤ 21763961992233^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622174101 5000000000 21763961992233 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244348433/10000000000 : ℝ)^4571 ≤ (43527926455271/100000000000000 : ℝ)^3547 := by
    have hnat : (5244348433 : ℕ)^4571*100000000000000^3547 ≤ 43527926455271^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244348433 10000000000 43527926455271 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-511596671/2500000000 : ℝ), (2622174101/5000000000 : ℝ), (5244348433/10000000000 : ℝ)] ![(3236037387003/25000000000000 : ℝ), (21763961992233/50000000000000 : ℝ), (43527926455271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-511596671/2500000000 : ℝ)|^4571 ≤ (3236037387003/25000000000000 : ℝ)^3547
        have hw : |(-511596671/2500000000 : ℝ)|=(511596671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622174101/5000000000 : ℝ)|^4571 ≤ (21763961992233/50000000000000 : ℝ)^3547
        have hw : |(2622174101/5000000000 : ℝ)|=(2622174101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244348433/10000000000 : ℝ)|^4571 ≤ (43527926455271/100000000000000 : ℝ)^3547
        have hw : |(5244348433/10000000000 : ℝ)|=(5244348433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_box_5 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689640319/5000000000 : ℝ)*x 0 + (-186634239/1000000000 : ℝ)*x 1 + (5244348479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689640319/5000000000 : ℝ)^4571 ≤ (22488252990393/50000000000000 : ℝ)^3547 := by
    have hnat : (2689640319 : ℕ)^4571*50000000000000^3547 ≤ 22488252990393^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689640319 5000000000 22488252990393 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186634239/1000000000 : ℝ)^4571 ≤ (2873891762529/25000000000000 : ℝ)^3547 := by
    have hnat : (186634239 : ℕ)^4571*25000000000000^3547 ≤ 2873891762529^3547*1000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186634239 1000000000 2873891762529 25000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244348479/10000000000 : ℝ)^4571 ≤ (43527926947293/100000000000000 : ℝ)^3547 := by
    have hnat : (5244348479 : ℕ)^4571*100000000000000^3547 ≤ 43527926947293^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244348479 10000000000 43527926947293 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689640319/5000000000 : ℝ), (-186634239/1000000000 : ℝ), (5244348479/10000000000 : ℝ)] ![(22488252990393/50000000000000 : ℝ), (2873891762529/25000000000000 : ℝ), (43527926947293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689640319/5000000000 : ℝ)|^4571 ≤ (22488252990393/50000000000000 : ℝ)^3547
        have hw : |(2689640319/5000000000 : ℝ)|=(2689640319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-186634239/1000000000 : ℝ)|^4571 ≤ (2873891762529/25000000000000 : ℝ)^3547
        have hw : |(-186634239/1000000000 : ℝ)|=(186634239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244348479/10000000000 : ℝ)|^4571 ≤ (43527926947293/100000000000000 : ℝ)^3547
        have hw : |(5244348479/10000000000 : ℝ)|=(5244348479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_box_6 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379281013/10000000000 : ℝ)*x 0 + (8390957/16000000 : ℝ)*x 1 + (-1866342359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379281013/10000000000 : ℝ)^4571 ≤ (22488255010679/50000000000000 : ℝ)^3547 := by
    have hnat : (5379281013 : ℕ)^4571*50000000000000^3547 ≤ 22488255010679^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379281013 10000000000 22488255010679 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8390957/16000000 : ℝ)^4571 ≤ (8705584632173/20000000000000 : ℝ)^3547 := by
    have hnat : (8390957 : ℕ)^4571*20000000000000^3547 ≤ 8705584632173^3547*16000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8390957 16000000 8705584632173 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1866342359/10000000000 : ℝ)^4571 ≤ (229911336081/2000000000000 : ℝ)^3547 := by
    have hnat : (1866342359 : ℕ)^4571*2000000000000^3547 ≤ 229911336081^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866342359 10000000000 229911336081 2000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379281013/10000000000 : ℝ), (8390957/16000000 : ℝ), (-1866342359/10000000000 : ℝ)] ![(22488255010679/50000000000000 : ℝ), (8705584632173/20000000000000 : ℝ), (229911336081/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379281013/10000000000 : ℝ)|^4571 ≤ (22488255010679/50000000000000 : ℝ)^3547
        have hw : |(5379281013/10000000000 : ℝ)|=(5379281013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8390957/16000000 : ℝ)|^4571 ≤ (8705584632173/20000000000000 : ℝ)^3547
        have hw : |(8390957/16000000 : ℝ)|=(8390957/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1866342359/10000000000 : ℝ)|^4571 ≤ (229911336081/2000000000000 : ℝ)^3547
        have hw : |(-1866342359/10000000000 : ℝ)|=(1866342359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_box_7 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2026877489/5000000000 : ℝ)*x 0 + (4367222307/10000000000 : ℝ)*x 1 + (873444453/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2026877489/5000000000 : ℝ)^4571 ≤ (31235469866961/100000000000000 : ℝ)^3547 := by
    have hnat : (2026877489 : ℕ)^4571*100000000000000^3547 ≤ 31235469866961^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026877489 5000000000 31235469866961 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4367222307/10000000000 : ℝ)^4571 ≤ (34382265272357/100000000000000 : ℝ)^3547 := by
    have hnat : (4367222307 : ℕ)^4571*100000000000000^3547 ≤ 34382265272357^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367222307 10000000000 34382265272357 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (873444453/2000000000 : ℝ)^4571 ≤ (214889155289/625000000000 : ℝ)^3547 := by
    have hnat : (873444453 : ℕ)^4571*625000000000^3547 ≤ 214889155289^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873444453 2000000000 214889155289 625000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2026877489/5000000000 : ℝ), (4367222307/10000000000 : ℝ), (873444453/2000000000 : ℝ)] ![(31235469866961/100000000000000 : ℝ), (34382265272357/100000000000000 : ℝ), (214889155289/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2026877489/5000000000 : ℝ)|^4571 ≤ (31235469866961/100000000000000 : ℝ)^3547
        have hw : |(2026877489/5000000000 : ℝ)|=(2026877489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4367222307/10000000000 : ℝ)|^4571 ≤ (34382265272357/100000000000000 : ℝ)^3547
        have hw : |(4367222307/10000000000 : ℝ)|=(4367222307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(873444453/2000000000 : ℝ)|^4571 ≤ (214889155289/625000000000 : ℝ)^3547
        have hw : |(873444453/2000000000 : ℝ)|=(873444453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_box_8 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-489168383/2500000000 : ℝ)*x 0 + (1026988003/2000000000 : ℝ)*x 1 + (5420510789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (489168383/2500000000 : ℝ)^4571 ≤ (2443506477361/20000000000000 : ℝ)^3547 := by
    have hnat : (489168383 : ℕ)^4571*20000000000000^3547 ≤ 2443506477361^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489168383 2500000000 2443506477361 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026988003/2000000000 : ℝ)^4571 ≤ (21180610997083/50000000000000 : ℝ)^3547 := by
    have hnat : (1026988003 : ℕ)^4571*50000000000000^3547 ≤ 21180610997083^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026988003 2000000000 21180610997083 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420510789/10000000000 : ℝ)^4571 ≤ (1419413925149/3125000000000 : ℝ)^3547 := by
    have hnat : (5420510789 : ℕ)^4571*3125000000000^3547 ≤ 1419413925149^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420510789 10000000000 1419413925149 3125000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-489168383/2500000000 : ℝ), (1026988003/2000000000 : ℝ), (5420510789/10000000000 : ℝ)] ![(2443506477361/20000000000000 : ℝ), (21180610997083/50000000000000 : ℝ), (1419413925149/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-489168383/2500000000 : ℝ)|^4571 ≤ (2443506477361/20000000000000 : ℝ)^3547
        have hw : |(-489168383/2500000000 : ℝ)|=(489168383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1026988003/2000000000 : ℝ)|^4571 ≤ (21180610997083/50000000000000 : ℝ)^3547
        have hw : |(1026988003/2000000000 : ℝ)|=(1026988003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420510789/10000000000 : ℝ)|^4571 ≤ (1419413925149/3125000000000 : ℝ)^3547
        have hw : |(5420510789/10000000000 : ℝ)|=(5420510789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_box_9 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314215473/2500000000 : ℝ)*x 0 + (-1793024973/10000000000 : ℝ)*x 1 + (5420510989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314215473/2500000000 : ℝ)^4571 ≤ (43661818051803/100000000000000 : ℝ)^3547 := by
    have hnat : (1314215473 : ℕ)^4571*100000000000000^3547 ≤ 43661818051803^3547*2500000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314215473 2500000000 43661818051803 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1793024973/10000000000 : ℝ)^4571 ≤ (10916934170869/100000000000000 : ℝ)^3547 := by
    have hnat : (1793024973 : ℕ)^4571*100000000000000^3547 ≤ 10916934170869^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1793024973 10000000000 10916934170869 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420510989/10000000000 : ℝ)^4571 ≤ (9084249552899/20000000000000 : ℝ)^3547 := by
    have hnat : (5420510989 : ℕ)^4571*20000000000000^3547 ≤ 9084249552899^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420510989 10000000000 9084249552899 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314215473/2500000000 : ℝ), (-1793024973/10000000000 : ℝ), (5420510989/10000000000 : ℝ)] ![(43661818051803/100000000000000 : ℝ), (10916934170869/100000000000000 : ℝ), (9084249552899/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314215473/2500000000 : ℝ)|^4571 ≤ (43661818051803/100000000000000 : ℝ)^3547
        have hw : |(1314215473/2500000000 : ℝ)|=(1314215473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1793024973/10000000000 : ℝ)|^4571 ≤ (10916934170869/100000000000000 : ℝ)^3547
        have hw : |(-1793024973/10000000000 : ℝ)|=(1793024973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420510989/10000000000 : ℝ)|^4571 ≤ (9084249552899/20000000000000 : ℝ)^3547
        have hw : |(5420510989/10000000000 : ℝ)|=(5420510989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_box_10 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525686219/1000000000 : ℝ)*x 0 + (5420510661/10000000000 : ℝ)*x 1 + (-896512509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525686219/1000000000 : ℝ)^4571 ≤ (43661821241443/100000000000000 : ℝ)^3547 := by
    have hnat : (525686219 : ℕ)^4571*100000000000000^3547 ≤ 43661821241443^3547*1000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525686219 1000000000 43661821241443 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420510661/10000000000 : ℝ)^4571 ≤ (45421244222543/100000000000000 : ℝ)^3547 := by
    have hnat : (5420510661 : ℕ)^4571*100000000000000^3547 ≤ 45421244222543^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420510661 10000000000 45421244222543 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896512509/5000000000 : ℝ)^4571 ≤ (682308407747/6250000000000 : ℝ)^3547 := by
    have hnat : (896512509 : ℕ)^4571*6250000000000^3547 ≤ 682308407747^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896512509 5000000000 682308407747 6250000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525686219/1000000000 : ℝ), (5420510661/10000000000 : ℝ), (-896512509/5000000000 : ℝ)] ![(43661821241443/100000000000000 : ℝ), (45421244222543/100000000000000 : ℝ), (682308407747/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525686219/1000000000 : ℝ)|^4571 ≤ (43661821241443/100000000000000 : ℝ)^3547
        have hw : |(525686219/1000000000 : ℝ)|=(525686219/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420510661/10000000000 : ℝ)|^4571 ≤ (45421244222543/100000000000000 : ℝ)^3547
        have hw : |(5420510661/10000000000 : ℝ)|=(5420510661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-896512509/5000000000 : ℝ)|^4571 ≤ (682308407747/6250000000000 : ℝ)^3547
        have hw : |(-896512509/5000000000 : ℝ)|=(896512509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_box_11 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (564033309/1250000000 : ℝ)*x 0 + (4137507577/10000000000 : ℝ)*x 1 + (4137507589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (564033309/1250000000 : ℝ)^4571 ≤ (17930415189551/50000000000000 : ℝ)^3547 := by
    have hnat : (564033309 : ℕ)^4571*50000000000000^3547 ≤ 17930415189551^3547*1250000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564033309 1250000000 17930415189551 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4137507577/10000000000 : ℝ)^4571 ≤ (32069584743899/100000000000000 : ℝ)^3547 := by
    have hnat : (4137507577 : ℕ)^4571*100000000000000^3547 ≤ 32069584743899^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137507577 10000000000 32069584743899 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4137507589/10000000000 : ℝ)^4571 ≤ (32069584863763/100000000000000 : ℝ)^3547 := by
    have hnat : (4137507589 : ℕ)^4571*100000000000000^3547 ≤ 32069584863763^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137507589 10000000000 32069584863763 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(564033309/1250000000 : ℝ), (4137507577/10000000000 : ℝ), (4137507589/10000000000 : ℝ)] ![(17930415189551/50000000000000 : ℝ), (32069584743899/100000000000000 : ℝ), (32069584863763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(564033309/1250000000 : ℝ)|^4571 ≤ (17930415189551/50000000000000 : ℝ)^3547
        have hw : |(564033309/1250000000 : ℝ)|=(564033309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4137507577/10000000000 : ℝ)|^4571 ≤ (32069584743899/100000000000000 : ℝ)^3547
        have hw : |(4137507577/10000000000 : ℝ)|=(4137507577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4137507589/10000000000 : ℝ)|^4571 ≤ (32069584863763/100000000000000 : ℝ)^3547
        have hw : |(4137507589/10000000000 : ℝ)|=(4137507589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_box_12 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-855990009/5000000000 : ℝ)*x 0 + (5506107433/10000000000 : ℝ)*x 1 + (5229306449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855990009/5000000000 : ℝ)^4571 ≤ (10285226208239/100000000000000 : ℝ)^3547 := by
    have hnat : (855990009 : ℕ)^4571*100000000000000^3547 ≤ 10285226208239^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855990009 5000000000 10285226208239 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5506107433/10000000000 : ℝ)^4571 ≤ (9269534322647/20000000000000 : ℝ)^3547 := by
    have hnat : (5506107433 : ℕ)^4571*20000000000000^3547 ≤ 9269534322647^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506107433 10000000000 9269534322647 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229306449/10000000000 : ℝ)^4571 ≤ (43367102170297/100000000000000 : ℝ)^3547 := by
    have hnat : (5229306449 : ℕ)^4571*100000000000000^3547 ≤ 43367102170297^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229306449 10000000000 43367102170297 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-855990009/5000000000 : ℝ), (5506107433/10000000000 : ℝ), (5229306449/10000000000 : ℝ)] ![(10285226208239/100000000000000 : ℝ), (9269534322647/20000000000000 : ℝ), (43367102170297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-855990009/5000000000 : ℝ)|^4571 ≤ (10285226208239/100000000000000 : ℝ)^3547
        have hw : |(-855990009/5000000000 : ℝ)|=(855990009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5506107433/10000000000 : ℝ)|^4571 ≤ (9269534322647/20000000000000 : ℝ)^3547
        have hw : |(5506107433/10000000000 : ℝ)|=(5506107433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229306449/10000000000 : ℝ)|^4571 ≤ (43367102170297/100000000000000 : ℝ)^3547
        have hw : |(5229306449/10000000000 : ℝ)|=(5229306449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_box_13 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389733779/10000000000 : ℝ)*x 0 + (-1872407287/10000000000 : ℝ)*x 1 + (2614653169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389733779/10000000000 : ℝ)^4571 ≤ (45089168666341/100000000000000 : ℝ)^3547 := by
    have hnat : (5389733779 : ℕ)^4571*100000000000000^3547 ≤ 45089168666341^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389733779 10000000000 45089168666341 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1872407287/10000000000 : ℝ)^4571 ≤ (2885932582453/25000000000000 : ℝ)^3547 := by
    have hnat : (1872407287 : ℕ)^4571*25000000000000^3547 ≤ 2885932582453^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872407287 10000000000 2885932582453 25000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614653169/5000000000 : ℝ)^4571 ≤ (43367100984011/100000000000000 : ℝ)^3547 := by
    have hnat : (2614653169 : ℕ)^4571*100000000000000^3547 ≤ 43367100984011^3547*5000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614653169 5000000000 43367100984011 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389733779/10000000000 : ℝ), (-1872407287/10000000000 : ℝ), (2614653169/5000000000 : ℝ)] ![(45089168666341/100000000000000 : ℝ), (2885932582453/25000000000000 : ℝ), (43367100984011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389733779/10000000000 : ℝ)|^4571 ≤ (45089168666341/100000000000000 : ℝ)^3547
        have hw : |(5389733779/10000000000 : ℝ)|=(5389733779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1872407287/10000000000 : ℝ)|^4571 ≤ (2885932582453/25000000000000 : ℝ)^3547
        have hw : |(-1872407287/10000000000 : ℝ)|=(1872407287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614653169/5000000000 : ℝ)|^4571 ≤ (43367100984011/100000000000000 : ℝ)^3547
        have hw : |(2614653169/5000000000 : ℝ)|=(2614653169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_box_14 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389733661/10000000000 : ℝ)*x 0 + (1045861281/2000000000 : ℝ)*x 1 + (-1872407357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389733661/10000000000 : ℝ)^4571 ≤ (9017833478839/20000000000000 : ℝ)^3547 := by
    have hnat : (5389733661 : ℕ)^4571*20000000000000^3547 ≤ 9017833478839^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389733661 10000000000 9017833478839 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045861281/2000000000 : ℝ)^4571 ≤ (21683550850029/50000000000000 : ℝ)^3547 := by
    have hnat : (1045861281 : ℕ)^4571*50000000000000^3547 ≤ 21683550850029^3547*2000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045861281 2000000000 21683550850029 50000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1872407357/10000000000 : ℝ)^4571 ≤ (2308746177193/20000000000000 : ℝ)^3547 := by
    have hnat : (1872407357 : ℕ)^4571*20000000000000^3547 ≤ 2308746177193^3547*10000000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872407357 10000000000 2308746177193 20000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389733661/10000000000 : ℝ), (1045861281/2000000000 : ℝ), (-1872407357/10000000000 : ℝ)] ![(9017833478839/20000000000000 : ℝ), (21683550850029/50000000000000 : ℝ), (2308746177193/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389733661/10000000000 : ℝ)|^4571 ≤ (9017833478839/20000000000000 : ℝ)^3547
        have hw : |(5389733661/10000000000 : ℝ)|=(5389733661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045861281/2000000000 : ℝ)|^4571 ≤ (21683550850029/50000000000000 : ℝ)^3547
        have hw : |(1045861281/2000000000 : ℝ)|=(1045861281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1872407357/10000000000 : ℝ)|^4571 ≤ (2308746177193/20000000000000 : ℝ)^3547
        have hw : |(-1872407357/10000000000 : ℝ)|=(1872407357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1537_box_15 (p : ℝ) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (32109151/80000000 : ℝ)*x 0 + (548351299/1250000000 : ℝ)*x 1 + (109670261/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32109151/80000000 : ℝ)^4571 ≤ (30837744784009/100000000000000 : ℝ)^3547 := by
    have hnat : (32109151 : ℕ)^4571*100000000000000^3547 ≤ 30837744784009^3547*80000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32109151 80000000 30837744784009 100000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548351299/1250000000 : ℝ)^4571 ≤ (1729056367847/5000000000000 : ℝ)^3547 := by
    have hnat : (548351299 : ℕ)^4571*5000000000000^3547 ≤ 1729056367847^3547*1250000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548351299 1250000000 1729056367847 5000000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109670261/250000000 : ℝ)^4571 ≤ (432264098057/1250000000000 : ℝ)^3547 := by
    have hnat : (109670261 : ℕ)^4571*1250000000000^3547 ≤ 432264098057^3547*250000000^4571 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109670261 250000000 432264098057 1250000000000 4571 3547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4571/1024 : ℝ)) 4571 3547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32109151/80000000 : ℝ), (548351299/1250000000 : ℝ), (109670261/250000000 : ℝ)] ![(30837744784009/100000000000000 : ℝ), (1729056367847/5000000000000 : ℝ), (432264098057/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32109151/80000000 : ℝ)|^4571 ≤ (30837744784009/100000000000000 : ℝ)^3547
        have hw : |(32109151/80000000 : ℝ)|=(32109151/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548351299/1250000000 : ℝ)|^4571 ≤ (1729056367847/5000000000000 : ℝ)^3547
        have hw : |(548351299/1250000000 : ℝ)|=(548351299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(109670261/250000000 : ℝ)|^4571 ≤ (432264098057/1250000000000 : ℝ)^3547
        have hw : |(109670261/250000000 : ℝ)|=(109670261/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1537_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11009/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2551/4000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29373/50000 : ℝ) ∧ (10073/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (86161/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11009/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11009/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11009/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11009/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11009/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11009/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11009/100000 : ℝ) ^ (4569/1024 : ℝ) ≤ (2650521660832317/50000000000000000000 : ℝ) := by
    have hpowers : (11009/100000 : ℝ)^4569 ≤ (2650521660832317/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11009 : ℕ)^4569*50000000000000000000^1024 ≤ 2650521660832317^1024*100000^4569 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11009 100000 2650521660832317 50000000000000000000 4569 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11009/100000 : ℝ)) (X := (2650521660832317/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4569/1024 : ℝ) ≤ (60711127688287/250000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4569 ≤ (60711127688287/250000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4569*250000000000000000^1024 ≤ 60711127688287^1024*25000^4569 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 60711127688287 250000000000000000 4569 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (60711127688287/250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002650521660832317/25000000000000000000 : ℝ) ≤ (5000118801600173/5000000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (25002650521660832317/25000000000000000000 : ℝ)^1024 ≤ (5000118801600173/5000000000000000 : ℝ)^4569 := by
      have hnat : (25002650521660832317 : ℕ)^1024*5000000000000000^4569 ≤ 5000118801600173^4569*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002650521660832317 25000000000000000000 5000118801600173 5000000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000118801600173/5000000000000000 : ℝ)) (X := (25002650521660832317/25000000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014792747198489717/50000000000000000000 : ℝ) ≤ (10000662991239377/10000000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (50014792747198489717/50000000000000000000 : ℝ)^1024 ≤ (10000662991239377/10000000000000000 : ℝ)^4569 := by
      have hnat : (50014792747198489717 : ℕ)^1024*10000000000000000^4569 ≤ 10000662991239377^4569*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014792747198489717 50000000000000000000 10000662991239377 10000000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000662991239377/10000000000000000 : ℝ)) (X := (50014792747198489717/50000000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (125060711127688287/125000000000000000 : ℝ) ≤ (1250136047409801/1250000000000000 : ℝ) ^ (4569/1024 : ℝ) := by
    have hpowers : (125060711127688287/125000000000000000 : ℝ)^1024 ≤ (1250136047409801/1250000000000000 : ℝ)^4569 := by
      have hnat : (125060711127688287 : ℕ)^1024*1250000000000000^4569 ≤ 1250136047409801^4569*125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125060711127688287 125000000000000000 1250136047409801 1250000000000000 1024 4569 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250136047409801/1250000000000000 : ℝ)) (X := (125060711127688287/125000000000000000 : ℝ)) (by norm_num) 4569 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2650521660832317/50000000000000000000 : ℝ) ≤ ((2796356067529885237/2796875000000000000 : ℝ)+2*(425388039031/447500000000000 : ℝ)*(11009/100000 : ℝ))^(4569/1024 : ℝ) := by
    rw [show (2796356067529885237/2796875000000000000 : ℝ)+2*(425388039031/447500000000000 : ℝ)*(11009/100000 : ℝ)=(5000118801600173/5000000000000000 : ℝ) by norm_num, show 1+2*(2650521660832317/50000000000000000000 : ℝ)=(25002650521660832317/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(60711127688287/250000000000000000 : ℝ)+(2650521660832317/50000000000000000000 : ℝ) ≤ ((2796356067529885237/2796875000000000000 : ℝ)+(425388039031/447500000000000 : ℝ)*((3871/25000 : ℝ)+(11009/100000 : ℝ)))^(4569/1024 : ℝ) := by
    rw [show (2796356067529885237/2796875000000000000 : ℝ)+(425388039031/447500000000000 : ℝ)*((3871/25000 : ℝ)+(11009/100000 : ℝ))=(10000662991239377/10000000000000000 : ℝ) by norm_num, show 1+(60711127688287/250000000000000000 : ℝ)+(2650521660832317/50000000000000000000 : ℝ)=(50014792747198489717/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(60711127688287/250000000000000000 : ℝ) ≤ ((2796356067529885237/2796875000000000000 : ℝ)+2*(425388039031/447500000000000 : ℝ)*(3871/25000 : ℝ))^(4569/1024 : ℝ) := by
    rw [show (2796356067529885237/2796875000000000000 : ℝ)+2*(425388039031/447500000000000 : ℝ)*(3871/25000 : ℝ)=(1250136047409801/1250000000000000 : ℝ) by norm_num, show 1+2*(60711127688287/250000000000000000 : ℝ)=(125060711127688287/125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2796356067529885237/2796875000000000000 : ℝ)*(X 1 0+X 2 0)+(425388039031/447500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (11009/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (2796356067529885237/2796875000000000000 : ℝ)) (alpha := (425388039031/447500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2796356067529885237/2796875000000000000 : ℝ)*(X 0 1+X 2 1)+(425388039031/447500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (11009/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (2796356067529885237/2796875000000000000 : ℝ)) (alpha := (425388039031/447500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2796356067529885237/2796875000000000000 : ℝ)*(X 0 2+X 1 2)+(425388039031/447500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4569/1024 : ℝ)) (lo := (11009/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (2796356067529885237/2796875000000000000 : ℝ)) (alpha := (425388039031/447500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-101402987/625000000 : ℝ)*X 0 0+(5400133987/10000000000 : ℝ)*X 0 1+(2700067241/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2635513231/5000000000 : ℝ)*X 1 0+(-900858823/5000000000 : ℝ)*X 1 1+(5400134187/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5271025707/10000000000 : ℝ)*X 2 0+(1080026977/2000000000 : ℝ)*X 2 1+(-1801717717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4460247199/10000000000 : ℝ)*X 0 0+(130128351/312500000 : ℝ)*X 0 1+(4164107467/10000000000 : ℝ)*X 0 2+(4460247199/10000000000 : ℝ)*X 1 0+(130128351/312500000 : ℝ)*X 1 1+(4164107467/10000000000 : ℝ)*X 1 2+(4460247199/10000000000 : ℝ)*X 2 0+(130128351/312500000 : ℝ)*X 2 1+(4164107467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-511596671/2500000000 : ℝ)*X 0 0+(2622174101/5000000000 : ℝ)*X 0 1+(5244348433/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2689640319/5000000000 : ℝ)*X 1 0+(-186634239/1000000000 : ℝ)*X 1 1+(5244348479/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5379281013/10000000000 : ℝ)*X 2 0+(8390957/16000000 : ℝ)*X 2 1+(-1866342359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2026877489/5000000000 : ℝ)*X 0 0+(4367222307/10000000000 : ℝ)*X 0 1+(873444453/2000000000 : ℝ)*X 0 2+(2026877489/5000000000 : ℝ)*X 1 0+(4367222307/10000000000 : ℝ)*X 1 1+(873444453/2000000000 : ℝ)*X 1 2+(2026877489/5000000000 : ℝ)*X 2 0+(4367222307/10000000000 : ℝ)*X 2 1+(873444453/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-489168383/2500000000 : ℝ)*X 0 0+(1026988003/2000000000 : ℝ)*X 0 1+(5420510789/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1314215473/2500000000 : ℝ)*X 1 0+(-1793024973/10000000000 : ℝ)*X 1 1+(5420510989/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((525686219/1000000000 : ℝ)*X 2 0+(5420510661/10000000000 : ℝ)*X 2 1+(-896512509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((564033309/1250000000 : ℝ)*X 0 0+(4137507577/10000000000 : ℝ)*X 0 1+(4137507589/10000000000 : ℝ)*X 0 2+(564033309/1250000000 : ℝ)*X 1 0+(4137507577/10000000000 : ℝ)*X 1 1+(4137507589/10000000000 : ℝ)*X 1 2+(564033309/1250000000 : ℝ)*X 2 0+(4137507577/10000000000 : ℝ)*X 2 1+(4137507589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-855990009/5000000000 : ℝ)*X 0 0+(5506107433/10000000000 : ℝ)*X 0 1+(5229306449/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5389733779/10000000000 : ℝ)*X 1 0+(-1872407287/10000000000 : ℝ)*X 1 1+(2614653169/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5389733661/10000000000 : ℝ)*X 2 0+(1045861281/2000000000 : ℝ)*X 2 1+(-1872407357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((32109151/80000000 : ℝ)*X 0 0+(548351299/1250000000 : ℝ)*X 0 1+(109670261/250000000 : ℝ)*X 0 2+(32109151/80000000 : ℝ)*X 1 0+(548351299/1250000000 : ℝ)*X 1 1+(109670261/250000000 : ℝ)*X 1 2+(32109151/80000000 : ℝ)*X 2 0+(548351299/1250000000 : ℝ)*X 2 1+(109670261/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1537_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2551/4000 : ℝ) ≤ (-8918120876380193656639092240681/13984375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3299059/6250000000000 : ℝ)*(lower2) + (6778337/25000000000000 : ℝ)*(lower3) + (16056213/100000000000000 : ℝ)*(upper5) + (226009602637757/10000000000000 : ℝ)*(major0) + (226009602637757/10000000000000 : ℝ)*(major1) + (226009602637757/10000000000000 : ℝ)*(major2) + (3397930387/100000000000000 : ℝ)*(sp2) + (2383063/20000000000000 : ℝ)*(sp3) + (3174836343879217/100000000000000 : ℝ)*(sp4) + (3174808610068343/100000000000000 : ℝ)*(sp5) + (3174833420919679/100000000000000 : ℝ)*(sp6) + (68330628392017/5000000000000 : ℝ)*(sp7) + (9499417/2000000000000 : ℝ)*(sp12) + (28208781723/100000000000000 : ℝ)*(sp13) + (170826572469457/12500000000000 : ℝ)*(f.failure) + (1587418409425033/50000000000000 : ℝ)*(f.sum) + (17814908527359/4475000000000000000000000000 : ℝ)*base65 + (25952089906012159/27968750000000000000000000000000 : ℝ)*base67 + (253517377798512159/27968750000000000000000000000000 : ℝ)*base69 + (253199276898512159/27968750000000000000000000000000 : ℝ)*base71 + (7770473083841/4475000000000000000000000000 : ℝ)*base74 + (246991371745387159/27968750000000000000000000000000 : ℝ)*base75 + (240091739411793409/27968750000000000000000000000000 : ℝ)*base77 + (278871916313199659/27968750000000000000000000000000 : ℝ)*base79 + (6632624193559/4475000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (148889/50000000000000000000 : ℝ)*base89 + (148889/50000000000000000000 : ℝ)*base91 + (148889/50000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (29373/50000 : ℝ) ≤ (16431128546621800287747822367053/27968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (130972849/100000000000000 : ℝ)*(upper2) + (22461763/20000000000000 : ℝ)*(upper3) + (6767431/12500000000000 : ℝ)*(upper5) + (467611130247527/20000000000000 : ℝ)*(major0) + (467611130247527/20000000000000 : ℝ)*(major1) + (467611130247527/20000000000000 : ℝ)*(major2) + (324276598365079/10000000000000 : ℝ)*(sp0) + (1621379622850469/50000000000000 : ℝ)*(sp1) + (1621383917923831/50000000000000 : ℝ)*(sp2) + (1413751916065301/100000000000000 : ℝ)*(sp3) + (8306590377/100000000000000 : ℝ)*(sp6) + (104187369/20000000000000 : ℝ)*(sp7) + (16896737101/100000000000000 : ℝ)*(sp9) + (10158787249/100000000000000 : ℝ)*(sp12) + (282750487400429/20000000000000 : ℝ)*(f.failure) + (3242776142438039/100000000000000 : ℝ)*(f.sum) + (113411397367/69921875000000000000000000 : ℝ)*base66 + (241743501900790149/55937500000000000000000000000000 : ℝ)*base67 + (361692699330772351/55937500000000000000000000000000 : ℝ)*base70 + (124917867407977649/55937500000000000000000000000000 : ℝ)*base71 + (16949491815013/4475000000000000000000000000 : ℝ)*base74 + (235612970520147351/55937500000000000000000000000000 : ℝ)*base76 + (70279097041415149/55937500000000000000000000000000 : ℝ)*base77 + (103468214340790149/55937500000000000000000000000000 : ℝ)*base79 + (7081981065947/1118750000000000000000000000 : ℝ)*base82 + (289067/80000000000000000000 : ℝ)*base90 + (289067/80000000000000000000 : ℝ)*base92 + (289067/80000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (10073/12500 : ℝ) ≤ (9015581801785214854078693071/11187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (39913529/100000000000000 : ℝ)*(upper0) + (3363467/20000000000000 : ℝ)*(upper1) + (2201443/5000000000000 : ℝ)*(upper4) + (632220223823411/25000000000000 : ℝ)*(major0) + (632220223823411/25000000000000 : ℝ)*(major1) + (632220223823411/25000000000000 : ℝ)*(major2) + (58889223081/100000000000000 : ℝ)*(sp1) + (1018922201/6250000000000 : ℝ)*(sp2) + (7670137911/100000000000000 : ℝ)*(sp3) + (940747241/50000000000000 : ℝ)*(sp4) + (218859942277933/6250000000000 : ℝ)*(sp8) + (437712758589791/12500000000000 : ℝ)*(sp9) + (3501744655186193/100000000000000 : ℝ)*(sp10) + (1529131093824803/100000000000000 : ℝ)*(sp11) + (764569381981357/50000000000000 : ℝ)*(f.failure) + (3501760957941409/100000000000000 : ℝ)*(f.sum) + (35834975138411/22375000000000000000000000000 : ℝ)*base66 + (65442163268203367/17480468750000000000000000000000 : ℝ)*base68 + (108528874152891593/69921875000000000000000000000000 : ℝ)*base70 + (30981110350546633/17480468750000000000000000000000 : ℝ)*base71 + (147981617453089/22375000000000000000000000000 : ℝ)*base73 + (3239682659140383/17480468750000000000000000000000 : ℝ)*base75 + (143926712427109133/17480468750000000000000000000000 : ℝ)*base77 + (490634728217735343/69921875000000000000000000000000 : ℝ)*base80 + (15562453226893/11187500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (744811/200000000000000000000 : ℝ)*base90 + (744811/200000000000000000000 : ℝ)*base92 + (744811/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-86161/100000 : ℝ) ≤ (-3765225316249395036448207784271/4370117187500000000000000000000 : ℝ) := by norm_num
    linear_combination (56239/2000000000000 : ℝ)*(upper1) + (4462707/25000000000000 : ℝ)*(upper3) + (18876119/50000000000000 : ℝ)*(lower4) + (1284279245480063/50000000000000 : ℝ)*(major0) + (1284279245480063/50000000000000 : ℝ)*(major1) + (1284279245480063/50000000000000 : ℝ)*(major2) + (760239557/100000000000000 : ℝ)*(sp4) + (2338574173/6250000000000 : ℝ)*(sp5) + (16376243573/50000000000000 : ℝ)*(sp6) + (2246985617/20000000000000 : ℝ)*(sp7) + (903176271096049/25000000000000 : ℝ)*(sp12) + (1806334213718493/50000000000000 : ℝ)*(sp13) + (112896034129269/3125000000000 : ℝ)*(sp14) + (1553119386344861/100000000000000 : ℝ)*(sp15) + (776565310636473/50000000000000 : ℝ)*(f.failure) + (1806352922311877/50000000000000 : ℝ)*(f.sum) + (36250564700969/22375000000000000000000000000 : ℝ)*base66 + (1322424961362017431/139843750000000000000000000000000 : ℝ)*base67 + (2410768631152826319/139843750000000000000000000000000 : ℝ)*base70 + (350827142357329931/139843750000000000000000000000000 : ℝ)*base71 + (9642884703531/22375000000000000000000000000 : ℝ)*base73 + (2566116749358892431/139843750000000000000000000000000 : ℝ)*base75 + (325379396472954931/139843750000000000000000000000000 : ℝ)*base77 + (637817071258892431/139843750000000000000000000000000 : ℝ)*base79 + (321769882597719/22375000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (449279/200000000000000000000 : ℝ)*base90 + (449279/200000000000000000000 : ℝ)*base92 + (449279/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1537_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11009/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2551/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(29373/50000 : ℝ) else (10073/12500 : ℝ) ≤ X j i ∧ X j i ≤ (86161/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1537_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1537_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2551/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(29373/50000 : ℝ) else (10073/12500 : ℝ) ≤ X j i ∧ X j i ≤ (86161/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1537_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1537_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4569/1024 : ℝ) ≤ p) (hpb : p ≤ (4571/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6615177/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2551/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(29373/50000 : ℝ) else (10073/12500 : ℝ) ≤ X j i ∧ X j i ≤ (86161/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1537_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
