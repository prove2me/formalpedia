-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1753_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:19:37.176801+00:00
-- url     : https://prove2.me/submissions/5ce474eb-93af-424c-8ba0-14d6b5cb2d11

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
theorem support_rectangle_w1753_s0_0 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1162947427/10000000000 : ℝ)*x 0 + (5621219979/10000000000 : ℝ)*x 1 + (4982361993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1162947427/10000000000 : ℝ)^5823 ≤ (7348037438213/100000000000000 : ℝ)^4799 := by
    have hnat : (1162947427 : ℕ)^5823*100000000000000^4799 ≤ 7348037438213^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1162947427 10000000000 7348037438213 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5621219979/10000000000 : ℝ)^5823 ≤ (9942142415171/20000000000000 : ℝ)^4799 := by
    have hnat : (5621219979 : ℕ)^5823*20000000000000^4799 ≤ 9942142415171^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5621219979 10000000000 9942142415171 20000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4982361993/10000000000 : ℝ)^5823 ≤ (10735312617369/25000000000000 : ℝ)^4799 := by
    have hnat : (4982361993 : ℕ)^5823*25000000000000^4799 ≤ 10735312617369^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4982361993 10000000000 10735312617369 25000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1162947427/10000000000 : ℝ), (5621219979/10000000000 : ℝ), (4982361993/10000000000 : ℝ)] ![(7348037438213/100000000000000 : ℝ), (9942142415171/20000000000000 : ℝ), (10735312617369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1162947427/10000000000 : ℝ)|^5823 ≤ (7348037438213/100000000000000 : ℝ)^4799
        have hw : |(-1162947427/10000000000 : ℝ)|=(1162947427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5621219979/10000000000 : ℝ)|^5823 ≤ (9942142415171/20000000000000 : ℝ)^4799
        have hw : |(5621219979/10000000000 : ℝ)|=(5621219979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4982361993/10000000000 : ℝ)|^5823 ≤ (10735312617369/25000000000000 : ℝ)^4799
        have hw : |(4982361993/10000000000 : ℝ)|=(4982361993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s0_1 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684159689/5000000000 : ℝ)*x 0 + (-1505180649/10000000000 : ℝ)*x 1 + (996472503/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684159689/5000000000 : ℝ)^5823 ≤ (2938135812839/6250000000000 : ℝ)^4799 := by
    have hnat : (2684159689 : ℕ)^5823*6250000000000^4799 ≤ 2938135812839^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684159689 5000000000 2938135812839 6250000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1505180649/10000000000 : ℝ)^5823 ≤ (10048571043381/100000000000000 : ℝ)^4799 := by
    have hnat : (1505180649 : ℕ)^5823*100000000000000^4799 ≤ 10048571043381^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1505180649 10000000000 10048571043381 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (996472503/2000000000 : ℝ)^5823 ≤ (21470627964193/50000000000000 : ℝ)^4799 := by
    have hnat : (996472503 : ℕ)^5823*50000000000000^4799 ≤ 21470627964193^4799*2000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996472503 2000000000 21470627964193 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684159689/5000000000 : ℝ), (-1505180649/10000000000 : ℝ), (996472503/2000000000 : ℝ)] ![(2938135812839/6250000000000 : ℝ), (10048571043381/100000000000000 : ℝ), (21470627964193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684159689/5000000000 : ℝ)|^5823 ≤ (2938135812839/6250000000000 : ℝ)^4799
        have hw : |(2684159689/5000000000 : ℝ)|=(2684159689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1505180649/10000000000 : ℝ)|^5823 ≤ (10048571043381/100000000000000 : ℝ)^4799
        have hw : |(-1505180649/10000000000 : ℝ)|=(1505180649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(996472503/2000000000 : ℝ)|^5823 ≤ (21470627964193/50000000000000 : ℝ)^4799
        have hw : |(996472503/2000000000 : ℝ)|=(996472503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s0_2 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268416079/500000000 : ℝ)*x 0 + (2491180639/5000000000 : ℝ)*x 1 + (-752589679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268416079/500000000 : ℝ)^5823 ≤ (9402039280557/20000000000000 : ℝ)^4799 := by
    have hnat : (268416079 : ℕ)^5823*20000000000000^4799 ≤ 9402039280557^4799*500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268416079 500000000 9402039280557 20000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2491180639/5000000000 : ℝ)^5823 ≤ (42941242992233/100000000000000 : ℝ)^4799 := by
    have hnat : (2491180639 : ℕ)^5823*100000000000000^4799 ≤ 42941242992233^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491180639 5000000000 42941242992233 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (752589679/5000000000 : ℝ)^5823 ≤ (10048560585639/100000000000000 : ℝ)^4799 := by
    have hnat : (752589679 : ℕ)^5823*100000000000000^4799 ≤ 10048560585639^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752589679 5000000000 10048560585639 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268416079/500000000 : ℝ), (2491180639/5000000000 : ℝ), (-752589679/5000000000 : ℝ)] ![(9402039280557/20000000000000 : ℝ), (42941242992233/100000000000000 : ℝ), (10048560585639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268416079/500000000 : ℝ)|^5823 ≤ (9402039280557/20000000000000 : ℝ)^4799
        have hw : |(268416079/500000000 : ℝ)|=(268416079/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2491180639/5000000000 : ℝ)|^5823 ≤ (42941242992233/100000000000000 : ℝ)^4799
        have hw : |(2491180639/5000000000 : ℝ)|=(2491180639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-752589679/5000000000 : ℝ)|^5823 ≤ (10048560585639/100000000000000 : ℝ)^4799
        have hw : |(-752589679/5000000000 : ℝ)|=(752589679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s0_3 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1986565857/5000000000 : ℝ)*x 0 + (746651651/2500000000 : ℝ)*x 1 + (319459051/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1986565857/5000000000 : ℝ)^5823 ≤ (32628479904187/100000000000000 : ℝ)^4799 := by
    have hnat : (1986565857 : ℕ)^5823*100000000000000^4799 ≤ 32628479904187^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986565857 5000000000 32628479904187 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (746651651/2500000000 : ℝ)^5823 ≤ (23077707716217/100000000000000 : ℝ)^4799 := by
    have hnat : (746651651 : ℕ)^5823*100000000000000^4799 ≤ 23077707716217^4799*2500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746651651 2500000000 23077707716217 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319459051/625000000 : ℝ)^5823 ≤ (11073453089641/25000000000000 : ℝ)^4799 := by
    have hnat : (319459051 : ℕ)^5823*25000000000000^4799 ≤ 11073453089641^4799*625000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319459051 625000000 11073453089641 25000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1986565857/5000000000 : ℝ), (746651651/2500000000 : ℝ), (319459051/625000000 : ℝ)] ![(32628479904187/100000000000000 : ℝ), (23077707716217/100000000000000 : ℝ), (11073453089641/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1986565857/5000000000 : ℝ)|^5823 ≤ (32628479904187/100000000000000 : ℝ)^4799
        have hw : |(1986565857/5000000000 : ℝ)|=(1986565857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(746651651/2500000000 : ℝ)|^5823 ≤ (23077707716217/100000000000000 : ℝ)^4799
        have hw : |(746651651/2500000000 : ℝ)|=(746651651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(319459051/625000000 : ℝ)|^5823 ≤ (11073453089641/25000000000000 : ℝ)^4799
        have hw : |(319459051/625000000 : ℝ)|=(319459051/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s0_4 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-291062519/2500000000 : ℝ)*x 0 + (2499279803/5000000000 : ℝ)*x 1 + (5604492401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (291062519/2500000000 : ℝ)^5823 ≤ (919753202997/12500000000000 : ℝ)^4799 := by
    have hnat : (291062519 : ℕ)^5823*12500000000000^4799 ≤ 919753202997^4799*2500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291062519 2500000000 919753202997 12500000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2499279803/5000000000 : ℝ)^5823 ≤ (8622139732831/20000000000000 : ℝ)^4799 := by
    have hnat : (2499279803 : ℕ)^5823*20000000000000^4799 ≤ 8622139732831^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2499279803 5000000000 8622139732831 20000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5604492401/10000000000 : ℝ)^5823 ≤ (9906255139451/20000000000000 : ℝ)^4799 := by
    have hnat : (5604492401 : ℕ)^5823*20000000000000^4799 ≤ 9906255139451^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5604492401 10000000000 9906255139451 20000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-291062519/2500000000 : ℝ), (2499279803/5000000000 : ℝ), (5604492401/10000000000 : ℝ)] ![(919753202997/12500000000000 : ℝ), (8622139732831/20000000000000 : ℝ), (9906255139451/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-291062519/2500000000 : ℝ)|^5823 ≤ (919753202997/12500000000000 : ℝ)^4799
        have hw : |(-291062519/2500000000 : ℝ)|=(291062519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2499279803/5000000000 : ℝ)|^5823 ≤ (8622139732831/20000000000000 : ℝ)^4799
        have hw : |(2499279803/5000000000 : ℝ)|=(2499279803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5604492401/10000000000 : ℝ)|^5823 ≤ (9906255139451/20000000000000 : ℝ)^4799
        have hw : |(5604492401/10000000000 : ℝ)|=(5604492401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s0_5 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5198089353/10000000000 : ℝ)*x 0 + (-110381143/1250000000 : ℝ)*x 1 + (1401123119/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5198089353/10000000000 : ℝ)^5823 ≤ (45207564100167/100000000000000 : ℝ)^4799 := by
    have hnat : (5198089353 : ℕ)^5823*100000000000000^4799 ≤ 45207564100167^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198089353 10000000000 45207564100167 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110381143/1250000000 : ℝ)^5823 ≤ (657644923067/12500000000000 : ℝ)^4799 := by
    have hnat : (110381143 : ℕ)^5823*12500000000000^4799 ≤ 657644923067^4799*1250000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110381143 1250000000 657644923067 12500000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1401123119/2500000000 : ℝ)^5823 ≤ (49531276501523/100000000000000 : ℝ)^4799 := by
    have hnat : (1401123119 : ℕ)^5823*100000000000000^4799 ≤ 49531276501523^4799*2500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401123119 2500000000 49531276501523 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5198089353/10000000000 : ℝ), (-110381143/1250000000 : ℝ), (1401123119/2500000000 : ℝ)] ![(45207564100167/100000000000000 : ℝ), (657644923067/12500000000000 : ℝ), (49531276501523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5198089353/10000000000 : ℝ)|^5823 ≤ (45207564100167/100000000000000 : ℝ)^4799
        have hw : |(5198089353/10000000000 : ℝ)|=(5198089353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-110381143/1250000000 : ℝ)|^5823 ≤ (657644923067/12500000000000 : ℝ)^4799
        have hw : |(-110381143/1250000000 : ℝ)|=(110381143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1401123119/2500000000 : ℝ)|^5823 ≤ (49531276501523/100000000000000 : ℝ)^4799
        have hw : |(1401123119/2500000000 : ℝ)|=(1401123119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s0_6 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039617773/2000000000 : ℝ)*x 0 + (5604492531/10000000000 : ℝ)*x 1 + (-35321991/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039617773/2000000000 : ℝ)^5823 ≤ (11301889737613/25000000000000 : ℝ)^4799 := by
    have hnat : (1039617773 : ℕ)^5823*25000000000000^4799 ≤ 11301889737613^4799*2000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039617773 2000000000 11301889737613 25000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5604492531/10000000000 : ℝ)^5823 ≤ (49531277091319/100000000000000 : ℝ)^4799 := by
    have hnat : (5604492531 : ℕ)^5823*100000000000000^4799 ≤ 49531277091319^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5604492531 10000000000 49531277091319 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35321991/400000000 : ℝ)^5823 ≤ (2630581973093/50000000000000 : ℝ)^4799 := by
    have hnat : (35321991 : ℕ)^5823*50000000000000^4799 ≤ 2630581973093^4799*400000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35321991 400000000 2630581973093 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039617773/2000000000 : ℝ), (5604492531/10000000000 : ℝ), (-35321991/400000000 : ℝ)] ![(11301889737613/25000000000000 : ℝ), (49531277091319/100000000000000 : ℝ), (2630581973093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039617773/2000000000 : ℝ)|^5823 ≤ (11301889737613/25000000000000 : ℝ)^4799
        have hw : |(1039617773/2000000000 : ℝ)|=(1039617773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5604492531/10000000000 : ℝ)|^5823 ≤ (49531277091319/100000000000000 : ℝ)^4799
        have hw : |(5604492531/10000000000 : ℝ)|=(5604492531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35321991/400000000 : ℝ)|^5823 ≤ (2630581973093/50000000000000 : ℝ)^4799
        have hw : |(-35321991/400000000 : ℝ)|=(35321991/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s0_7 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3977465039/10000000000 : ℝ)*x 0 + (252873617/500000000 : ℝ)*x 1 + (3042239623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3977465039/10000000000 : ℝ)^5823 ≤ (16335832391183/50000000000000 : ℝ)^4799 := by
    have hnat : (3977465039 : ℕ)^5823*50000000000000^4799 ≤ 16335832391183^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3977465039 10000000000 16335832391183 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (252873617/500000000 : ℝ)^5823 ≤ (21863994500611/50000000000000 : ℝ)^4799 := by
    have hnat : (252873617 : ℕ)^5823*50000000000000^4799 ≤ 21863994500611^4799*500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252873617 500000000 21863994500611 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3042239623/10000000000 : ℝ)^5823 ≤ (23600346194681/100000000000000 : ℝ)^4799 := by
    have hnat : (3042239623 : ℕ)^5823*100000000000000^4799 ≤ 23600346194681^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3042239623 10000000000 23600346194681 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3977465039/10000000000 : ℝ), (252873617/500000000 : ℝ), (3042239623/10000000000 : ℝ)] ![(16335832391183/50000000000000 : ℝ), (21863994500611/50000000000000 : ℝ), (23600346194681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3977465039/10000000000 : ℝ)|^5823 ≤ (16335832391183/50000000000000 : ℝ)^4799
        have hw : |(3977465039/10000000000 : ℝ)|=(3977465039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(252873617/500000000 : ℝ)|^5823 ≤ (21863994500611/50000000000000 : ℝ)^4799
        have hw : |(252873617/500000000 : ℝ)|=(252873617/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3042239623/10000000000 : ℝ)|^5823 ≤ (23600346194681/100000000000000 : ℝ)^4799
        have hw : |(3042239623/10000000000 : ℝ)|=(3042239623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1753_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216291693/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1711/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2583/12500 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (5807/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5807 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5807*1^1024 ≤ 0^1024*1^5807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5807/1024 : ℝ) ≤ (553761332017189021/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5807 ≤ (553761332017189021/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5807*100000000000000000000^1024 ≤ 553761332017189021^1024*5^5807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 553761332017189021 100000000000000000000 5807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (553761332017189021/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5807/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5807 := by
      have hnat : (1 : ℕ)^1024*1^5807 ≤ 1^5807*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100553761332017189021/100000000000000000000 : ℝ) ≤ (10009742771585753/10000000000000000 : ℝ) ^ (5807/1024 : ℝ) := by
    have hpowers : (100553761332017189021/100000000000000000000 : ℝ)^1024 ≤ (10009742771585753/10000000000000000 : ℝ)^5807 := by
      have hnat : (100553761332017189021 : ℕ)^1024*10000000000000000^5807 ≤ 10009742771585753^5807*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100553761332017189021 100000000000000000000 10009742771585753 10000000000000000 1024 5807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009742771585753/10000000000000000 : ℝ)) (X := (100553761332017189021/100000000000000000000 : ℝ)) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50553761332017189021/50000000000000000000 : ℝ) ≤ (5009742771585753/5000000000000000 : ℝ) ^ (5807/1024 : ℝ) := by
    have hpowers : (50553761332017189021/50000000000000000000 : ℝ)^1024 ≤ (5009742771585753/5000000000000000 : ℝ)^5807 := by
      have hnat : (50553761332017189021 : ℕ)^1024*5000000000000000^5807 ≤ 5009742771585753^5807*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50553761332017189021 50000000000000000000 5009742771585753 5000000000000000 1024 5807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5009742771585753/5000000000000000 : ℝ)) (X := (50553761332017189021/50000000000000000000 : ℝ)) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9742771585753/4000000000000000 : ℝ)*(0 : ℝ))^(5807/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9742771585753/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(553761332017189021/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9742771585753/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5807/1024 : ℝ) := by
    rw [show (1 : ℝ)+(9742771585753/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10009742771585753/10000000000000000 : ℝ) by norm_num, show 1+(553761332017189021/100000000000000000000 : ℝ)+(0 : ℝ)=(100553761332017189021/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(553761332017189021/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9742771585753/4000000000000000 : ℝ)*(2/5 : ℝ))^(5807/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9742771585753/4000000000000000 : ℝ)*(2/5 : ℝ)=(5009742771585753/5000000000000000 : ℝ) by norm_num, show 1+2*(553761332017189021/100000000000000000000 : ℝ)=(50553761332017189021/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9742771585753/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5807/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9742771585753/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9742771585753/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5807/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9742771585753/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9742771585753/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5807/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9742771585753/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1162947427/10000000000 : ℝ)*X 0 0+(5621219979/10000000000 : ℝ)*X 0 1+(4982361993/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2684159689/5000000000 : ℝ)*X 1 0+(-1505180649/10000000000 : ℝ)*X 1 1+(996472503/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((268416079/500000000 : ℝ)*X 2 0+(2491180639/5000000000 : ℝ)*X 2 1+(-752589679/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1986565857/5000000000 : ℝ)*X 0 0+(746651651/2500000000 : ℝ)*X 0 1+(319459051/625000000 : ℝ)*X 0 2+(1986565857/5000000000 : ℝ)*X 1 0+(746651651/2500000000 : ℝ)*X 1 1+(319459051/625000000 : ℝ)*X 1 2+(1986565857/5000000000 : ℝ)*X 2 0+(746651651/2500000000 : ℝ)*X 2 1+(319459051/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-291062519/2500000000 : ℝ)*X 0 0+(2499279803/5000000000 : ℝ)*X 0 1+(5604492401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5198089353/10000000000 : ℝ)*X 1 0+(-110381143/1250000000 : ℝ)*X 1 1+(1401123119/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1039617773/2000000000 : ℝ)*X 2 0+(5604492531/10000000000 : ℝ)*X 2 1+(-35321991/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3977465039/10000000000 : ℝ)*X 0 0+(252873617/500000000 : ℝ)*X 0 1+(3042239623/10000000000 : ℝ)*X 0 2+(3977465039/10000000000 : ℝ)*X 1 0+(252873617/500000000 : ℝ)*X 1 1+(3042239623/10000000000 : ℝ)*X 1 2+(3977465039/10000000000 : ℝ)*X 2 0+(252873617/500000000 : ℝ)*X 2 1+(3042239623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (51483010186779391408623/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4834167/1562500000000 : ℝ)*(base19) + (316933401/50000000000000 : ℝ)*(base23) + (135533119/100000000000000 : ℝ)*(base24) + (6108027/6250000000000 : ℝ)*(upper4) + (127559999/100000000000000 : ℝ)*(upper5) + (508986264675597/50000000000000 : ℝ)*(major0) + (508986264675597/50000000000000 : ℝ)*(major1) + (508986264675597/50000000000000 : ℝ)*(major2) + (782646590224597/50000000000000 : ℝ)*(sp0) + (782648339854879/50000000000000 : ℝ)*(sp1) + (391324054924131/25000000000000 : ℝ)*(sp2) + (235323532565301/50000000000000 : ℝ)*(sp3) + (952161813/25000000000000 : ℝ)*(sp4) + (935831319/100000000000000 : ℝ)*(sp7) + (470648000961921/100000000000000 : ℝ)*(f.failure) + (782648494548223/50000000000000 : ℝ)*(f.sum) + (299363515930459/100000000000000000000000000000 : ℝ)*base66 + (769900529230459/200000000000000000000000000000 : ℝ)*base68 + (1793333720630459/200000000000000000000000000000 : ℝ)*base70 + (1111439946630459/200000000000000000000000000000 : ℝ)*base72 + (349767899369541/100000000000000000000000000000 : ℝ)*base73 + (2305794855830459/200000000000000000000000000000 : ℝ)*base76 + (622059425830459/200000000000000000000000000000 : ℝ)*base78 + (1416190136030459/200000000000000000000000000000 : ℝ)*base80 + (542914225730459/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (121622253/10000000000000000000000 : ℝ)*base89 + (121622253/10000000000000000000000 : ℝ)*base91 + (121622253/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (246817445908018117014201/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1090100619/50000000000000 : ℝ)*(base19) + (407011023/20000000000000 : ℝ)*(base23) + (13427379/50000000000000 : ℝ)*(upper2) + (186058399/50000000000000 : ℝ)*(upper3) + (6665481/2000000000000 : ℝ)*(upper5) + (268320991297939/25000000000000 : ℝ)*(major0) + (268320991297939/25000000000000 : ℝ)*(major1) + (268320991297939/25000000000000 : ℝ)*(major2) + (9621299987/100000000000000 : ℝ)*(sp1) + (521408437/6250000000000 : ℝ)*(sp2) + (825173494073029/50000000000000 : ℝ)*(sp4) + (1650335186644833/100000000000000 : ℝ)*(sp5) + (33006732211119/2000000000000 : ℝ)*(sp6) + (248110306573761/50000000000000 : ℝ)*(sp7) + (248110306573761/50000000000000 : ℝ)*(f.failure) + (825173494073029/50000000000000 : ℝ)*(f.sum) + (30879436836933/50000000000000000000000000000 : ℝ)*base66 + (882082752136933/100000000000000000000000000000 : ℝ)*base68 + (106887764263067/100000000000000000000000000000 : ℝ)*base69 + (209684738636933/100000000000000000000000000000 : ℝ)*base72 + (71211137586933/50000000000000000000000000000 : ℝ)*base74 + (282358091236933/100000000000000000000000000000 : ℝ)*base76 + (73706036136933/100000000000000000000000000000 : ℝ)*base78 + (549265640063067/100000000000000000000000000000 : ℝ)*base79 + (210606819663067/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3932627/5000000000000000000000 : ℝ)*base90 + (3932627/5000000000000000000000 : ℝ)*base92 + (3932627/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1753_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216291693/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1711/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2583/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1753_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1753_s1_0 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1204727199/10000000000 : ℝ)*x 0 + (686989879/1250000000 : ℝ)*x 1 + (5079675439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1204727199/10000000000 : ℝ)^5823 ≤ (3834782950949/50000000000000 : ℝ)^4799 := by
    have hnat : (1204727199 : ℕ)^5823*50000000000000^4799 ≤ 3834782950949^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204727199 10000000000 3834782950949 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (686989879/1250000000 : ℝ)^5823 ≤ (6046175079729/12500000000000 : ℝ)^4799 := by
    have hnat : (686989879 : ℕ)^5823*12500000000000^4799 ≤ 6046175079729^4799*1250000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686989879 1250000000 6046175079729 12500000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5079675439/10000000000 : ℝ)^5823 ≤ (21980516723983/50000000000000 : ℝ)^4799 := by
    have hnat : (5079675439 : ℕ)^5823*50000000000000^4799 ≤ 21980516723983^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079675439 10000000000 21980516723983 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1204727199/10000000000 : ℝ), (686989879/1250000000 : ℝ), (5079675439/10000000000 : ℝ)] ![(3834782950949/50000000000000 : ℝ), (6046175079729/12500000000000 : ℝ), (21980516723983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1204727199/10000000000 : ℝ)|^5823 ≤ (3834782950949/50000000000000 : ℝ)^4799
        have hw : |(-1204727199/10000000000 : ℝ)|=(1204727199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(686989879/1250000000 : ℝ)|^5823 ≤ (6046175079729/12500000000000 : ℝ)^4799
        have hw : |(686989879/1250000000 : ℝ)|=(686989879/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5079675439/10000000000 : ℝ)|^5823 ≤ (21980516723983/50000000000000 : ℝ)^4799
        have hw : |(5079675439/10000000000 : ℝ)|=(5079675439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s1_1 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5334998739/10000000000 : ℝ)*x 0 + (-284495167/2000000000 : ℝ)*x 1 + (317479721/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5334998739/10000000000 : ℝ)^5823 ≤ (4665635925463/10000000000000 : ℝ)^4799 := by
    have hnat : (5334998739 : ℕ)^5823*10000000000000^4799 ≤ 4665635925463^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5334998739 10000000000 4665635925463 10000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284495167/2000000000 : ℝ)^5823 ≤ (9382606264851/100000000000000 : ℝ)^4799 := by
    have hnat : (284495167 : ℕ)^5823*100000000000000^4799 ≤ 9382606264851^4799*2000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284495167 2000000000 9382606264851 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317479721/625000000 : ℝ)^5823 ≤ (43961034466557/100000000000000 : ℝ)^4799 := by
    have hnat : (317479721 : ℕ)^5823*100000000000000^4799 ≤ 43961034466557^4799*625000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317479721 625000000 43961034466557 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5334998739/10000000000 : ℝ), (-284495167/2000000000 : ℝ), (317479721/625000000 : ℝ)] ![(4665635925463/10000000000000 : ℝ), (9382606264851/100000000000000 : ℝ), (43961034466557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5334998739/10000000000 : ℝ)|^5823 ≤ (4665635925463/10000000000000 : ℝ)^4799
        have hw : |(5334998739/10000000000 : ℝ)|=(5334998739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-284495167/2000000000 : ℝ)|^5823 ≤ (9382606264851/100000000000000 : ℝ)^4799
        have hw : |(-284495167/2000000000 : ℝ)|=(284495167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317479721/625000000 : ℝ)|^5823 ≤ (43961034466557/100000000000000 : ℝ)^4799
        have hw : |(317479721/625000000 : ℝ)|=(317479721/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s1_2 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2667499533/5000000000 : ℝ)*x 0 + (5079675201/10000000000 : ℝ)*x 1 + (-711237921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2667499533/5000000000 : ℝ)^5823 ≤ (46656362724557/100000000000000 : ℝ)^4799 := by
    have hnat : (2667499533 : ℕ)^5823*100000000000000^4799 ≤ 46656362724557^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2667499533 5000000000 46656362724557 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5079675201/10000000000 : ℝ)^5823 ≤ (5495128868593/12500000000000 : ℝ)^4799 := by
    have hnat : (5079675201 : ℕ)^5823*12500000000000^4799 ≤ 5495128868593^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079675201 10000000000 5495128868593 12500000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (711237921/5000000000 : ℝ)^5823 ≤ (75060850567/800000000000 : ℝ)^4799 := by
    have hnat : (711237921 : ℕ)^5823*800000000000^4799 ≤ 75060850567^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711237921 5000000000 75060850567 800000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2667499533/5000000000 : ℝ), (5079675201/10000000000 : ℝ), (-711237921/5000000000 : ℝ)] ![(46656362724557/100000000000000 : ℝ), (5495128868593/12500000000000 : ℝ), (75060850567/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2667499533/5000000000 : ℝ)|^5823 ≤ (46656362724557/100000000000000 : ℝ)^4799
        have hw : |(2667499533/5000000000 : ℝ)|=(2667499533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5079675201/10000000000 : ℝ)|^5823 ≤ (5495128868593/12500000000000 : ℝ)^4799
        have hw : |(5079675201/10000000000 : ℝ)|=(5079675201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-711237921/5000000000 : ℝ)|^5823 ≤ (75060850567/800000000000 : ℝ)^4799
        have hw : |(-711237921/5000000000 : ℝ)|=(711237921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s1_3 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (501741143/1250000000 : ℝ)*x 0 + (419220877/1250000000 : ℝ)*x 1 + (4738124581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (501741143/1250000000 : ℝ)^5823 ≤ (16517727093973/50000000000000 : ℝ)^4799 := by
    have hnat : (501741143 : ℕ)^5823*50000000000000^4799 ≤ 16517727093973^4799*1250000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501741143 1250000000 16517727093973 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (419220877/1250000000 : ℝ)^5823 ≤ (13281959491889/50000000000000 : ℝ)^4799 := by
    have hnat : (419220877 : ℕ)^5823*50000000000000^4799 ≤ 13281959491889^4799*1250000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419220877 1250000000 13281959491889 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4738124581/10000000000 : ℝ)^5823 ≤ (40400626812531/100000000000000 : ℝ)^4799 := by
    have hnat : (4738124581 : ℕ)^5823*100000000000000^4799 ≤ 40400626812531^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4738124581 10000000000 40400626812531 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(501741143/1250000000 : ℝ), (419220877/1250000000 : ℝ), (4738124581/10000000000 : ℝ)] ![(16517727093973/50000000000000 : ℝ), (13281959491889/50000000000000 : ℝ), (40400626812531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(501741143/1250000000 : ℝ)|^5823 ≤ (16517727093973/50000000000000 : ℝ)^4799
        have hw : |(501741143/1250000000 : ℝ)|=(501741143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(419220877/1250000000 : ℝ)|^5823 ≤ (13281959491889/50000000000000 : ℝ)^4799
        have hw : |(419220877/1250000000 : ℝ)|=(419220877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4738124581/10000000000 : ℝ)|^5823 ≤ (40400626812531/100000000000000 : ℝ)^4799
        have hw : |(4738124581/10000000000 : ℝ)|=(4738124581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s1_4 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-602542749/5000000000 : ℝ)*x 0 + (2543282209/5000000000 : ℝ)*x 1 + (548888373/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (602542749/5000000000 : ℝ)^5823 ≤ (1534466743921/20000000000000 : ℝ)^4799 := by
    have hnat : (602542749 : ℕ)^5823*20000000000000^4799 ≤ 1534466743921^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602542749 5000000000 1534466743921 20000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2543282209/5000000000 : ℝ)^5823 ≤ (44033384631741/100000000000000 : ℝ)^4799 := by
    have hnat : (2543282209 : ℕ)^5823*100000000000000^4799 ≤ 44033384631741^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2543282209 5000000000 44033384631741 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548888373/1000000000 : ℝ)^5823 ≤ (24147140816257/50000000000000 : ℝ)^4799 := by
    have hnat : (548888373 : ℕ)^5823*50000000000000^4799 ≤ 24147140816257^4799*1000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548888373 1000000000 24147140816257 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-602542749/5000000000 : ℝ), (2543282209/5000000000 : ℝ), (548888373/1000000000 : ℝ)] ![(1534466743921/20000000000000 : ℝ), (44033384631741/100000000000000 : ℝ), (24147140816257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-602542749/5000000000 : ℝ)|^5823 ≤ (1534466743921/20000000000000 : ℝ)^4799
        have hw : |(-602542749/5000000000 : ℝ)|=(602542749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2543282209/5000000000 : ℝ)|^5823 ≤ (44033384631741/100000000000000 : ℝ)^4799
        have hw : |(2543282209/5000000000 : ℝ)|=(2543282209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(548888373/1000000000 : ℝ)|^5823 ≤ (24147140816257/50000000000000 : ℝ)^4799
        have hw : |(548888373/1000000000 : ℝ)|=(548888373/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s1_5 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224735439/10000000000 : ℝ)*x 0 + (-506633817/5000000000 : ℝ)*x 1 + (548888371/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224735439/10000000000 : ℝ)^5823 ≤ (11372226426911/25000000000000 : ℝ)^4799 := by
    have hnat : (5224735439 : ℕ)^5823*25000000000000^4799 ≤ 11372226426911^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224735439 10000000000 11372226426911 25000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506633817/5000000000 : ℝ)^5823 ≤ (1554203215103/25000000000000 : ℝ)^4799 := by
    have hnat : (506633817 : ℕ)^5823*25000000000000^4799 ≤ 1554203215103^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506633817 5000000000 1554203215103 25000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548888371/1000000000 : ℝ)^5823 ≤ (9658856283799/20000000000000 : ℝ)^4799 := by
    have hnat : (548888371 : ℕ)^5823*20000000000000^4799 ≤ 9658856283799^4799*1000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548888371 1000000000 9658856283799 20000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224735439/10000000000 : ℝ), (-506633817/5000000000 : ℝ), (548888371/1000000000 : ℝ)] ![(11372226426911/25000000000000 : ℝ), (1554203215103/25000000000000 : ℝ), (9658856283799/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224735439/10000000000 : ℝ)|^5823 ≤ (11372226426911/25000000000000 : ℝ)^4799
        have hw : |(5224735439/10000000000 : ℝ)|=(5224735439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-506633817/5000000000 : ℝ)|^5823 ≤ (1554203215103/25000000000000 : ℝ)^4799
        have hw : |(-506633817/5000000000 : ℝ)|=(506633817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(548888371/1000000000 : ℝ)|^5823 ≤ (9658856283799/20000000000000 : ℝ)^4799
        have hw : |(548888371/1000000000 : ℝ)|=(548888371/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s1_6 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (653091931/1250000000 : ℝ)*x 0 + (5488883591/10000000000 : ℝ)*x 1 + (-63329237/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653091931/1250000000 : ℝ)^5823 ≤ (22744452901361/50000000000000 : ℝ)^4799 := by
    have hnat : (653091931 : ℕ)^5823*50000000000000^4799 ≤ 22744452901361^4799*1250000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653091931 1250000000 22744452901361 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5488883591/10000000000 : ℝ)^5823 ≤ (48294280148553/100000000000000 : ℝ)^4799 := by
    have hnat : (5488883591 : ℕ)^5823*100000000000000^4799 ≤ 48294280148553^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488883591 10000000000 48294280148553 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63329237/625000000 : ℝ)^5823 ≤ (3108407018327/50000000000000 : ℝ)^4799 := by
    have hnat : (63329237 : ℕ)^5823*50000000000000^4799 ≤ 3108407018327^4799*625000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63329237 625000000 3108407018327 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653091931/1250000000 : ℝ), (5488883591/10000000000 : ℝ), (-63329237/625000000 : ℝ)] ![(22744452901361/50000000000000 : ℝ), (48294280148553/100000000000000 : ℝ), (3108407018327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653091931/1250000000 : ℝ)|^5823 ≤ (22744452901361/50000000000000 : ℝ)^4799
        have hw : |(653091931/1250000000 : ℝ)|=(653091931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5488883591/10000000000 : ℝ)|^5823 ≤ (48294280148553/100000000000000 : ℝ)^4799
        have hw : |(5488883591/10000000000 : ℝ)|=(5488883591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-63329237/625000000 : ℝ)|^5823 ≤ (3108407018327/50000000000000 : ℝ)^4799
        have hw : |(-63329237/625000000 : ℝ)|=(63329237/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s1_7 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (200755979/500000000 : ℝ)*x 0 + (1178802921/2500000000 : ℝ)*x 1 + (844291523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (200755979/500000000 : ℝ)^5823 ≤ (3304734267017/10000000000000 : ℝ)^4799 := by
    have hnat : (200755979 : ℕ)^5823*10000000000000^4799 ≤ 3304734267017^4799*500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200755979 500000000 3304734267017 10000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1178802921/2500000000 : ℝ)^5823 ≤ (40163689607353/100000000000000 : ℝ)^4799 := by
    have hnat : (1178802921 : ℕ)^5823*100000000000000^4799 ≤ 40163689607353^4799*2500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178802921 2500000000 40163689607353 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (844291523/2500000000 : ℝ)^5823 ≤ (5357793543081/20000000000000 : ℝ)^4799 := by
    have hnat : (844291523 : ℕ)^5823*20000000000000^4799 ≤ 5357793543081^4799*2500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844291523 2500000000 5357793543081 20000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(200755979/500000000 : ℝ), (1178802921/2500000000 : ℝ), (844291523/2500000000 : ℝ)] ![(3304734267017/10000000000000 : ℝ), (40163689607353/100000000000000 : ℝ), (5357793543081/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(200755979/500000000 : ℝ)|^5823 ≤ (3304734267017/10000000000000 : ℝ)^4799
        have hw : |(200755979/500000000 : ℝ)|=(200755979/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1178802921/2500000000 : ℝ)|^5823 ≤ (40163689607353/100000000000000 : ℝ)^4799
        have hw : |(1178802921/2500000000 : ℝ)|=(1178802921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(844291523/2500000000 : ℝ)|^5823 ≤ (5357793543081/20000000000000 : ℝ)^4799
        have hw : |(844291523/2500000000 : ℝ)|=(844291523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1753_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216291693/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2583/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1711/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (4513/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17979/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2583/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1711/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2583/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1711/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2583/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1711/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2583/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1711/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2583/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1711/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2583/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1711/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1711/25000 : ℝ) ^ (5807/1024 : ℝ) ≤ (99362222041/400000000000000000 : ℝ) := by
    have hpowers : (1711/25000 : ℝ)^5807 ≤ (99362222041/400000000000000000 : ℝ)^1024 := by
      have hnat : (1711 : ℕ)^5807*400000000000000000^1024 ≤ 99362222041^1024*25000^5807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1711 25000 99362222041 400000000000000000 5807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1711/25000 : ℝ)) (X := (99362222041/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2583/12500 : ℝ) ^ (5807/1024 : ℝ) ≤ (163516049135887/1250000000000000000 : ℝ) := by
    have hpowers : (2583/12500 : ℝ)^5807 ≤ (163516049135887/1250000000000000000 : ℝ)^1024 := by
      have hnat : (2583 : ℕ)^5807*1250000000000000000^1024 ≤ 163516049135887^1024*12500^5807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2583 12500 163516049135887 1250000000000000000 5807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2583/12500 : ℝ)) (X := (163516049135887/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (200000099362222041/200000000000000000 : ℝ) ≤ (400000035042843/400000000000000 : ℝ) ^ (5807/1024 : ℝ) := by
    have hpowers : (200000099362222041/200000000000000000 : ℝ)^1024 ≤ (400000035042843/400000000000000 : ℝ)^5807 := by
      have hnat : (200000099362222041 : ℕ)^1024*400000000000000^5807 ≤ 400000035042843^5807*200000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        200000099362222041 200000000000000000 400000035042843 400000000000000 1024 5807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400000035042843/400000000000000 : ℝ)) (X := (200000099362222041/200000000000000000 : ℝ)) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10001310612448638121/10000000000000000000 : ℝ) ≤ (5000115549742989/5000000000000000 : ℝ) ^ (5807/1024 : ℝ) := by
    have hpowers : (10001310612448638121/10000000000000000000 : ℝ)^1024 ≤ (5000115549742989/5000000000000000 : ℝ)^5807 := by
      have hnat : (10001310612448638121 : ℕ)^1024*5000000000000000^5807 ≤ 5000115549742989^5807*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001310612448638121 10000000000000000000 5000115549742989 5000000000000000 1024 5807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000115549742989/5000000000000000 : ℝ)) (X := (10001310612448638121/10000000000000000000 : ℝ)) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (625163516049135887/625000000000000000 : ℝ) ≤ (10000461322900881/10000000000000000 : ℝ) ^ (5807/1024 : ℝ) := by
    have hpowers : (625163516049135887/625000000000000000 : ℝ)^1024 ≤ (10000461322900881/10000000000000000 : ℝ)^5807 := by
      have hnat : (625163516049135887 : ℕ)^1024*10000000000000000^5807 ≤ 10000461322900881^5807*625000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625163516049135887 625000000000000000 10000461322900881 10000000000000000 1024 5807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000461322900881/10000000000000000 : ℝ)) (X := (625163516049135887/625000000000000000 : ℝ)) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(99362222041/400000000000000000 : ℝ) ≤ ((34549215202299766059/34550000000000000000 : ℝ)+2*(230223414903/1382000000000000 : ℝ)*(1711/25000 : ℝ))^(5807/1024 : ℝ) := by
    rw [show (34549215202299766059/34550000000000000000 : ℝ)+2*(230223414903/1382000000000000 : ℝ)*(1711/25000 : ℝ)=(400000035042843/400000000000000 : ℝ) by norm_num, show 1+2*(99362222041/400000000000000000 : ℝ)=(200000099362222041/200000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(163516049135887/1250000000000000000 : ℝ)+(99362222041/400000000000000000 : ℝ) ≤ ((34549215202299766059/34550000000000000000 : ℝ)+(230223414903/1382000000000000 : ℝ)*((2583/12500 : ℝ)+(1711/25000 : ℝ)))^(5807/1024 : ℝ) := by
    rw [show (34549215202299766059/34550000000000000000 : ℝ)+(230223414903/1382000000000000 : ℝ)*((2583/12500 : ℝ)+(1711/25000 : ℝ))=(5000115549742989/5000000000000000 : ℝ) by norm_num, show 1+(163516049135887/1250000000000000000 : ℝ)+(99362222041/400000000000000000 : ℝ)=(10001310612448638121/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(163516049135887/1250000000000000000 : ℝ) ≤ ((34549215202299766059/34550000000000000000 : ℝ)+2*(230223414903/1382000000000000 : ℝ)*(2583/12500 : ℝ))^(5807/1024 : ℝ) := by
    rw [show (34549215202299766059/34550000000000000000 : ℝ)+2*(230223414903/1382000000000000 : ℝ)*(2583/12500 : ℝ)=(10000461322900881/10000000000000000 : ℝ) by norm_num, show 1+2*(163516049135887/1250000000000000000 : ℝ)=(625163516049135887/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34549215202299766059/34550000000000000000 : ℝ)*(X 1 0+X 2 0)+(230223414903/1382000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5807/1024 : ℝ)) (lo := (1711/25000 : ℝ)) (hi := (2583/12500 : ℝ)) (c := (34549215202299766059/34550000000000000000 : ℝ)) (alpha := (230223414903/1382000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34549215202299766059/34550000000000000000 : ℝ)*(X 0 1+X 2 1)+(230223414903/1382000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5807/1024 : ℝ)) (lo := (1711/25000 : ℝ)) (hi := (2583/12500 : ℝ)) (c := (34549215202299766059/34550000000000000000 : ℝ)) (alpha := (230223414903/1382000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34549215202299766059/34550000000000000000 : ℝ)*(X 0 2+X 1 2)+(230223414903/1382000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5807/1024 : ℝ)) (lo := (1711/25000 : ℝ)) (hi := (2583/12500 : ℝ)) (c := (34549215202299766059/34550000000000000000 : ℝ)) (alpha := (230223414903/1382000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1204727199/10000000000 : ℝ)*X 0 0+(686989879/1250000000 : ℝ)*X 0 1+(5079675439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5334998739/10000000000 : ℝ)*X 1 0+(-284495167/2000000000 : ℝ)*X 1 1+(317479721/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2667499533/5000000000 : ℝ)*X 2 0+(5079675201/10000000000 : ℝ)*X 2 1+(-711237921/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((501741143/1250000000 : ℝ)*X 0 0+(419220877/1250000000 : ℝ)*X 0 1+(4738124581/10000000000 : ℝ)*X 0 2+(501741143/1250000000 : ℝ)*X 1 0+(419220877/1250000000 : ℝ)*X 1 1+(4738124581/10000000000 : ℝ)*X 1 2+(501741143/1250000000 : ℝ)*X 2 0+(419220877/1250000000 : ℝ)*X 2 1+(4738124581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-602542749/5000000000 : ℝ)*X 0 0+(2543282209/5000000000 : ℝ)*X 0 1+(548888373/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5224735439/10000000000 : ℝ)*X 1 0+(-506633817/5000000000 : ℝ)*X 1 1+(548888371/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((653091931/1250000000 : ℝ)*X 2 0+(5488883591/10000000000 : ℝ)*X 2 1+(-63329237/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((200755979/500000000 : ℝ)*X 0 0+(1178802921/2500000000 : ℝ)*X 0 1+(844291523/2500000000 : ℝ)*X 0 2+(200755979/500000000 : ℝ)*X 1 0+(1178802921/2500000000 : ℝ)*X 1 1+(844291523/2500000000 : ℝ)*X 1 2+(200755979/500000000 : ℝ)*X 2 0+(1178802921/2500000000 : ℝ)*X 2 1+(844291523/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5501642862821158302558831891/431875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1866152821/100000000000000 : ℝ)*(base19) + (1869861603/100000000000000 : ℝ)*(base23) + (15316403/20000000000000 : ℝ)*(lower2) + (21835517/6250000000000 : ℝ)*(upper3) + (255374789/100000000000000 : ℝ)*(upper5) + (390604303673317/25000000000000 : ℝ)*(major0) + (390604303673317/25000000000000 : ℝ)*(major1) + (390604303673317/25000000000000 : ℝ)*(major2) + (240245373603713/10000000000000 : ℝ)*(sp0) + (600616585087219/25000000000000 : ℝ)*(sp1) + (1201233168320047/50000000000000 : ℝ)*(sp2) + (722360844577173/100000000000000 : ℝ)*(sp3) + (7235232283/50000000000000 : ℝ)*(sp4) + (2476837657/50000000000000 : ℝ)*(sp7) + (722365798252487/100000000000000 : ℝ)*(f.failure) + (2402468206501697/100000000000000 : ℝ)*(f.sum) + (32071234539401/17275000000000000000000000000 : ℝ)*base65 + (341487883576822703/863750000000000000000000000000000 : ℝ)*base67 + (6631282250990572703/863750000000000000000000000000000 : ℝ)*base69 + (3787738181253177297/863750000000000000000000000000000 : ℝ)*base72 + (11775614032849/17275000000000000000000000000 : ℝ)*base74 + (2476354283958072703/863750000000000000000000000000000 : ℝ)*base75 + (714053538196822703/863750000000000000000000000000000 : ℝ)*base77 + (2062361315030677297/863750000000000000000000000000000 : ℝ)*base80 + (1427750449419/4318750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (54690491/10000000000000000000000 : ℝ)*base89 + (54690491/10000000000000000000000 : ℝ)*base91 + (54690491/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (59730893257570077587283/8637500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1055801143/100000000000000 : ℝ)*(base19) + (273839403/25000000000000 : ℝ)*(base23) + (9048079/25000000000000 : ℝ)*(upper2) + (31008931/20000000000000 : ℝ)*(upper3) + (252556149/100000000000000 : ℝ)*(upper5) + (404118420345449/25000000000000 : ℝ)*(major0) + (404118420345449/25000000000000 : ℝ)*(major1) + (404118420345449/25000000000000 : ℝ)*(major2) + (7728788443/100000000000000 : ℝ)*(sp1) + (3058943513/50000000000000 : ℝ)*(sp2) + (1242794471252419/50000000000000 : ℝ)*(sp4) + (1242790078957627/50000000000000 : ℝ)*(sp5) + (2485581729260201/100000000000000 : ℝ)*(sp6) + (747358189748783/100000000000000 : ℝ)*(sp7) + (747358189748783/100000000000000 : ℝ)*(f.failure) + (1242794471252419/50000000000000 : ℝ)*(f.sum) + (25352279794953/17275000000000000000000000000 : ℝ)*base66 + (11454715222456490491/863750000000000000000000000000000 : ℝ)*base67 + (6374900482806490491/863750000000000000000000000000000 : ℝ)*base69 + (1263222841789759509/863750000000000000000000000000000 : ℝ)*base72 + (47763170012961/8637500000000000000000000000 : ℝ)*base73 + (3405562792403509509/863750000000000000000000000000000 : ℝ)*base76 + (614169030253509509/863750000000000000000000000000000 : ℝ)*base78 + (8374194265577740491/863750000000000000000000000000000 : ℝ)*base79 + (23263078194353/17275000000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (80240381/10000000000000000000000 : ℝ)*base90 + (80240381/10000000000000000000000 : ℝ)*base92 + (80240381/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1753_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216291693/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2583/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1711/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4513/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17979/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1753_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1753_s2_0 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-120562357/1000000000 : ℝ)*x 0 + (5493039339/10000000000 : ℝ)*x 1 + (1270486057/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (120562357/1000000000 : ℝ)^5823 ≤ (7676490592481/100000000000000 : ℝ)^4799 := by
    have hnat : (120562357 : ℕ)^5823*100000000000000^4799 ≤ 7676490592481^4799*1000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120562357 1000000000 7676490592481 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5493039339/10000000000 : ℝ)^5823 ≤ (48338650410621/100000000000000 : ℝ)^4799 := by
    have hnat : (5493039339 : ℕ)^5823*100000000000000^4799 ≤ 48338650410621^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493039339 10000000000 48338650410621 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1270486057/2500000000 : ℝ)^5823 ≤ (21992429494433/50000000000000 : ℝ)^4799 := by
    have hnat : (1270486057 : ℕ)^5823*50000000000000^4799 ≤ 21992429494433^4799*2500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270486057 2500000000 21992429494433 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-120562357/1000000000 : ℝ), (5493039339/10000000000 : ℝ), (1270486057/2500000000 : ℝ)] ![(7676490592481/100000000000000 : ℝ), (48338650410621/100000000000000 : ℝ), (21992429494433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-120562357/1000000000 : ℝ)|^5823 ≤ (7676490592481/100000000000000 : ℝ)^4799
        have hw : |(-120562357/1000000000 : ℝ)|=(120562357/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5493039339/10000000000 : ℝ)|^5823 ≤ (48338650410621/100000000000000 : ℝ)^4799
        have hw : |(5493039339/10000000000 : ℝ)|=(5493039339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1270486057/2500000000 : ℝ)|^5823 ≤ (21992429494433/50000000000000 : ℝ)^4799
        have hw : |(1270486057/2500000000 : ℝ)|=(1270486057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s2_1 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2667099/5000000 : ℝ)*x 0 + (-710280229/5000000000 : ℝ)*x 1 + (5081944193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2667099/5000000 : ℝ)^5823 ≤ (23323931215613/50000000000000 : ℝ)^4799 := by
    have hnat : (2667099 : ℕ)^5823*50000000000000^4799 ≤ 23323931215613^4799*5000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2667099 5000000 23323931215613 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (710280229/5000000000 : ℝ)^5823 ≤ (1170909866951/12500000000000 : ℝ)^4799 := by
    have hnat : (710280229 : ℕ)^5823*12500000000000^4799 ≤ 1170909866951^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710280229 5000000000 1170909866951 12500000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5081944193/10000000000 : ℝ)^5823 ≤ (21992429310649/50000000000000 : ℝ)^4799 := by
    have hnat : (5081944193 : ℕ)^5823*50000000000000^4799 ≤ 21992429310649^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081944193 10000000000 21992429310649 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2667099/5000000 : ℝ), (-710280229/5000000000 : ℝ), (5081944193/10000000000 : ℝ)] ![(23323931215613/50000000000000 : ℝ), (1170909866951/12500000000000 : ℝ), (21992429310649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2667099/5000000 : ℝ)|^5823 ≤ (23323931215613/50000000000000 : ℝ)^4799
        have hw : |(2667099/5000000 : ℝ)|=(2667099/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-710280229/5000000000 : ℝ)|^5823 ≤ (1170909866951/12500000000000 : ℝ)^4799
        have hw : |(-710280229/5000000000 : ℝ)|=(710280229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5081944193/10000000000 : ℝ)|^5823 ≤ (21992429310649/50000000000000 : ℝ)^4799
        have hw : |(5081944193/10000000000 : ℝ)|=(5081944193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s2_2 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1333549491/2500000000 : ℝ)*x 0 + (254097211/500000000 : ℝ)*x 1 + (-142056047/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1333549491/2500000000 : ℝ)^5823 ≤ (11661965512307/25000000000000 : ℝ)^4799 := by
    have hnat : (1333549491 : ℕ)^5823*25000000000000^4799 ≤ 11661965512307^4799*2500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1333549491 2500000000 11661965512307 25000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (254097211/500000000 : ℝ)^5823 ≤ (879697178097/2000000000000 : ℝ)^4799 := by
    have hnat : (254097211 : ℕ)^5823*2000000000000^4799 ≤ 879697178097^4799*500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254097211 500000000 879697178097 2000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (142056047/1000000000 : ℝ)^5823 ≤ (9367279031621/100000000000000 : ℝ)^4799 := by
    have hnat : (142056047 : ℕ)^5823*100000000000000^4799 ≤ 9367279031621^4799*1000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142056047 1000000000 9367279031621 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1333549491/2500000000 : ℝ), (254097211/500000000 : ℝ), (-142056047/1000000000 : ℝ)] ![(11661965512307/25000000000000 : ℝ), (879697178097/2000000000000 : ℝ), (9367279031621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1333549491/2500000000 : ℝ)|^5823 ≤ (11661965512307/25000000000000 : ℝ)^4799
        have hw : |(1333549491/2500000000 : ℝ)|=(1333549491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(254097211/500000000 : ℝ)|^5823 ≤ (879697178097/2000000000000 : ℝ)^4799
        have hw : |(254097211/500000000 : ℝ)|=(254097211/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-142056047/1000000000 : ℝ)|^5823 ≤ (9367279031621/100000000000000 : ℝ)^4799
        have hw : |(-142056047/1000000000 : ℝ)|=(142056047/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s2_3 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4014663819/10000000000 : ℝ)*x 0 + (420284389/1250000000 : ℝ)*x 1 + (2364754151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4014663819/10000000000 : ℝ)^5823 ≤ (6608558210029/20000000000000 : ℝ)^4799 := by
    have hnat : (4014663819 : ℕ)^5823*20000000000000^4799 ≤ 6608558210029^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4014663819 10000000000 6608558210029 20000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (420284389/1250000000 : ℝ)^5823 ≤ (26645709910759/100000000000000 : ℝ)^4799 := by
    have hnat : (420284389 : ℕ)^5823*100000000000000^4799 ≤ 26645709910759^4799*1250000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420284389 1250000000 26645709910759 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2364754151/5000000000 : ℝ)^5823 ≤ (20155749513771/50000000000000 : ℝ)^4799 := by
    have hnat : (2364754151 : ℕ)^5823*50000000000000^4799 ≤ 20155749513771^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2364754151 5000000000 20155749513771 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4014663819/10000000000 : ℝ), (420284389/1250000000 : ℝ), (2364754151/5000000000 : ℝ)] ![(6608558210029/20000000000000 : ℝ), (26645709910759/100000000000000 : ℝ), (20155749513771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4014663819/10000000000 : ℝ)|^5823 ≤ (6608558210029/20000000000000 : ℝ)^4799
        have hw : |(4014663819/10000000000 : ℝ)|=(4014663819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(420284389/1250000000 : ℝ)|^5823 ≤ (26645709910759/100000000000000 : ℝ)^4799
        have hw : |(420284389/1250000000 : ℝ)|=(420284389/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2364754151/5000000000 : ℝ)|^5823 ≤ (20155749513771/50000000000000 : ℝ)^4799
        have hw : |(2364754151/5000000000 : ℝ)|=(2364754151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s2_4 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1205968559/10000000000 : ℝ)*x 0 + (1272166117/2500000000 : ℝ)*x 1 + (21944713/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1205968559/10000000000 : ℝ)^5823 ≤ (7679156011777/100000000000000 : ℝ)^4799 := by
    have hnat : (1205968559 : ℕ)^5823*100000000000000^4799 ≤ 7679156011777^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205968559 10000000000 7679156011777 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1272166117/2500000000 : ℝ)^5823 ≤ (22027722234959/50000000000000 : ℝ)^4799 := by
    have hnat : (1272166117 : ℕ)^5823*50000000000000^4799 ≤ 22027722234959^4799*2500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272166117 2500000000 22027722234959 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21944713/40000000 : ℝ)^5823 ≤ (1508293734481/3125000000000 : ℝ)^4799 := by
    have hnat : (21944713 : ℕ)^5823*3125000000000^4799 ≤ 1508293734481^4799*40000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21944713 40000000 1508293734481 3125000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1205968559/10000000000 : ℝ), (1272166117/2500000000 : ℝ), (21944713/40000000 : ℝ)] ![(7679156011777/100000000000000 : ℝ), (22027722234959/50000000000000 : ℝ), (1508293734481/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1205968559/10000000000 : ℝ)|^5823 ≤ (7679156011777/100000000000000 : ℝ)^4799
        have hw : |(-1205968559/10000000000 : ℝ)|=(1205968559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1272166117/2500000000 : ℝ)|^5823 ≤ (22027722234959/50000000000000 : ℝ)^4799
        have hw : |(1272166117/2500000000 : ℝ)|=(1272166117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21944713/40000000 : ℝ)|^5823 ≤ (1508293734481/3125000000000 : ℝ)^4799
        have hw : |(21944713/40000000 : ℝ)|=(21944713/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s2_5 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (653164131/1250000000 : ℝ)*x 0 + (-50816327/500000000 : ℝ)*x 1 + (5486178277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653164131/1250000000 : ℝ)^5823 ≤ (5686875970649/12500000000000 : ℝ)^4799 := by
    have hnat : (653164131 : ℕ)^5823*12500000000000^4799 ≤ 5686875970649^4799*1250000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653164131 1250000000 5686875970649 12500000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50816327/500000000 : ℝ)^5823 ≤ (6239592431313/100000000000000 : ℝ)^4799 := by
    have hnat : (50816327 : ℕ)^5823*100000000000000^4799 ≤ 6239592431313^4799*500000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50816327 500000000 6239592431313 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5486178277/10000000000 : ℝ)^5823 ≤ (24132699895807/50000000000000 : ℝ)^4799 := by
    have hnat : (5486178277 : ℕ)^5823*50000000000000^4799 ≤ 24132699895807^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486178277 10000000000 24132699895807 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653164131/1250000000 : ℝ), (-50816327/500000000 : ℝ), (5486178277/10000000000 : ℝ)] ![(5686875970649/12500000000000 : ℝ), (6239592431313/100000000000000 : ℝ), (24132699895807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653164131/1250000000 : ℝ)|^5823 ≤ (5686875970649/12500000000000 : ℝ)^4799
        have hw : |(653164131/1250000000 : ℝ)|=(653164131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-50816327/500000000 : ℝ)|^5823 ≤ (6239592431313/100000000000000 : ℝ)^4799
        have hw : |(-50816327/500000000 : ℝ)|=(50816327/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5486178277/10000000000 : ℝ)|^5823 ≤ (24132699895807/50000000000000 : ℝ)^4799
        have hw : |(5486178277/10000000000 : ℝ)|=(5486178277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s2_6 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612656509/5000000000 : ℝ)*x 0 + (5486178343/10000000000 : ℝ)*x 1 + (-1016326487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612656509/5000000000 : ℝ)^5823 ≤ (45495007448259/100000000000000 : ℝ)^4799 := by
    have hnat : (2612656509 : ℕ)^5823*100000000000000^4799 ≤ 45495007448259^4799*5000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612656509 5000000000 45495007448259 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5486178343/10000000000 : ℝ)^5823 ≤ (24132700248077/50000000000000 : ℝ)^4799 := by
    have hnat : (5486178343 : ℕ)^5823*50000000000000^4799 ≤ 24132700248077^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486178343 10000000000 24132700248077 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016326487/10000000000 : ℝ)^5823 ≤ (6239592036497/100000000000000 : ℝ)^4799 := by
    have hnat : (1016326487 : ℕ)^5823*100000000000000^4799 ≤ 6239592036497^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016326487 10000000000 6239592036497 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612656509/5000000000 : ℝ), (5486178343/10000000000 : ℝ), (-1016326487/10000000000 : ℝ)] ![(45495007448259/100000000000000 : ℝ), (24132700248077/50000000000000 : ℝ), (6239592036497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612656509/5000000000 : ℝ)|^5823 ≤ (45495007448259/100000000000000 : ℝ)^4799
        have hw : |(2612656509/5000000000 : ℝ)|=(2612656509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5486178343/10000000000 : ℝ)|^5823 ≤ (24132700248077/50000000000000 : ℝ)^4799
        have hw : |(5486178343/10000000000 : ℝ)|=(5486178343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1016326487/10000000000 : ℝ)|^5823 ≤ (6239592036497/100000000000000 : ℝ)^4799
        have hw : |(-1016326487/10000000000 : ℝ)|=(1016326487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1753_s2_7 (p : ℝ) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (501976367/1250000000 : ℝ)*x 0 + (4707158211/10000000000 : ℝ)*x 1 + (3385093087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (501976367/1250000000 : ℝ)^5823 ≤ (33054247354271/100000000000000 : ℝ)^4799 := by
    have hnat : (501976367 : ℕ)^5823*100000000000000^4799 ≤ 33054247354271^4799*1250000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501976367 1250000000 33054247354271 100000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4707158211/10000000000 : ℝ)^5823 ≤ (4008046869477/10000000000000 : ℝ)^4799 := by
    have hnat : (4707158211 : ℕ)^5823*10000000000000^4799 ≤ 4008046869477^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4707158211 10000000000 4008046869477 10000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3385093087/10000000000 : ℝ)^5823 ≤ (13432641968493/50000000000000 : ℝ)^4799 := by
    have hnat : (3385093087 : ℕ)^5823*50000000000000^4799 ≤ 13432641968493^4799*10000000000^5823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3385093087 10000000000 13432641968493 50000000000000 5823 4799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5823/1024 : ℝ)) 5823 4799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(501976367/1250000000 : ℝ), (4707158211/10000000000 : ℝ), (3385093087/10000000000 : ℝ)] ![(33054247354271/100000000000000 : ℝ), (4008046869477/10000000000000 : ℝ), (13432641968493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(501976367/1250000000 : ℝ)|^5823 ≤ (33054247354271/100000000000000 : ℝ)^4799
        have hw : |(501976367/1250000000 : ℝ)|=(501976367/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4707158211/10000000000 : ℝ)|^5823 ≤ (4008046869477/10000000000000 : ℝ)^4799
        have hw : |(4707158211/10000000000 : ℝ)|=(4707158211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3385093087/10000000000 : ℝ)|^5823 ≤ (13432641968493/50000000000000 : ℝ)^4799
        have hw : |(3385093087/10000000000 : ℝ)|=(3385093087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1753_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216291693/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17979/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4513/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9077/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8959/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17979/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4513/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17979/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4513/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17979/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4513/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17979/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4513/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17979/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4513/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17979/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4513/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4513/50000 : ℝ) ^ (5807/1024 : ℝ) ≤ (119321881909611/100000000000000000000 : ℝ) := by
    have hpowers : (4513/50000 : ℝ)^5807 ≤ (119321881909611/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4513 : ℕ)^5807*100000000000000000000^1024 ≤ 119321881909611^1024*50000^5807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4513 50000 119321881909611 100000000000000000000 5807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4513/50000 : ℝ)) (X := (119321881909611/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17979/100000 : ℝ) ^ (5807/1024 : ℝ) ≤ (2970441655674831/50000000000000000000 : ℝ) := by
    have hpowers : (17979/100000 : ℝ)^5807 ≤ (2970441655674831/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17979 : ℕ)^5807*50000000000000000000^1024 ≤ 2970441655674831^1024*100000^5807 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17979 100000 2970441655674831 50000000000000000000 5807 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17979/100000 : ℝ)) (X := (2970441655674831/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000119321881909611/50000000000000000000 : ℝ) ≤ (10000004208213777/10000000000000000 : ℝ) ^ (5807/1024 : ℝ) := by
    have hpowers : (50000119321881909611/50000000000000000000 : ℝ)^1024 ≤ (10000004208213777/10000000000000000 : ℝ)^5807 := by
      have hnat : (50000119321881909611 : ℕ)^1024*10000000000000000^5807 ≤ 10000004208213777^5807*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000119321881909611 50000000000000000000 10000004208213777 10000000000000000 1024 5807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000004208213777/10000000000000000 : ℝ)) (X := (50000119321881909611/50000000000000000000 : ℝ)) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100006060205193259273/100000000000000000000 : ℝ) ≤ (2000021372465109/2000000000000000 : ℝ) ^ (5807/1024 : ℝ) := by
    have hpowers : (100006060205193259273/100000000000000000000 : ℝ)^1024 ≤ (2000021372465109/2000000000000000 : ℝ)^5807 := by
      have hnat : (100006060205193259273 : ℕ)^1024*2000000000000000^5807 ≤ 2000021372465109^5807*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100006060205193259273 100000000000000000000 2000021372465109 2000000000000000 1024 5807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000021372465109/2000000000000000 : ℝ)) (X := (100006060205193259273/100000000000000000000 : ℝ)) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25002970441655674831/25000000000000000000 : ℝ) ≤ (10000209516437313/10000000000000000 : ℝ) ^ (5807/1024 : ℝ) := by
    have hpowers : (25002970441655674831/25000000000000000000 : ℝ)^1024 ≤ (10000209516437313/10000000000000000 : ℝ)^5807 := by
      have hnat : (25002970441655674831 : ℕ)^1024*10000000000000000^5807 ≤ 10000209516437313^5807*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002970441655674831 25000000000000000000 10000209516437313 10000000000000000 1024 5807 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000209516437313/10000000000000000 : ℝ)) (X := (25002970441655674831/25000000000000000000 : ℝ)) (by norm_num) 5807 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(119321881909611/100000000000000000000 : ℝ) ≤ ((17905636912822461909/17906000000000000000 : ℝ)+2*(12831763971/111912500000000 : ℝ)*(4513/50000 : ℝ))^(5807/1024 : ℝ) := by
    rw [show (17905636912822461909/17906000000000000000 : ℝ)+2*(12831763971/111912500000000 : ℝ)*(4513/50000 : ℝ)=(10000004208213777/10000000000000000 : ℝ) by norm_num, show 1+2*(119321881909611/100000000000000000000 : ℝ)=(50000119321881909611/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2970441655674831/50000000000000000000 : ℝ)+(119321881909611/100000000000000000000 : ℝ) ≤ ((17905636912822461909/17906000000000000000 : ℝ)+(12831763971/111912500000000 : ℝ)*((17979/100000 : ℝ)+(4513/50000 : ℝ)))^(5807/1024 : ℝ) := by
    rw [show (17905636912822461909/17906000000000000000 : ℝ)+(12831763971/111912500000000 : ℝ)*((17979/100000 : ℝ)+(4513/50000 : ℝ))=(2000021372465109/2000000000000000 : ℝ) by norm_num, show 1+(2970441655674831/50000000000000000000 : ℝ)+(119321881909611/100000000000000000000 : ℝ)=(100006060205193259273/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2970441655674831/50000000000000000000 : ℝ) ≤ ((17905636912822461909/17906000000000000000 : ℝ)+2*(12831763971/111912500000000 : ℝ)*(17979/100000 : ℝ))^(5807/1024 : ℝ) := by
    rw [show (17905636912822461909/17906000000000000000 : ℝ)+2*(12831763971/111912500000000 : ℝ)*(17979/100000 : ℝ)=(10000209516437313/10000000000000000 : ℝ) by norm_num, show 1+2*(2970441655674831/50000000000000000000 : ℝ)=(25002970441655674831/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17905636912822461909/17906000000000000000 : ℝ)*(X 1 0+X 2 0)+(12831763971/111912500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5807/1024 : ℝ)) (lo := (4513/50000 : ℝ)) (hi := (17979/100000 : ℝ)) (c := (17905636912822461909/17906000000000000000 : ℝ)) (alpha := (12831763971/111912500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17905636912822461909/17906000000000000000 : ℝ)*(X 0 1+X 2 1)+(12831763971/111912500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5807/1024 : ℝ)) (lo := (4513/50000 : ℝ)) (hi := (17979/100000 : ℝ)) (c := (17905636912822461909/17906000000000000000 : ℝ)) (alpha := (12831763971/111912500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17905636912822461909/17906000000000000000 : ℝ)*(X 0 2+X 1 2)+(12831763971/111912500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5807/1024 : ℝ)) (lo := (4513/50000 : ℝ)) (hi := (17979/100000 : ℝ)) (c := (17905636912822461909/17906000000000000000 : ℝ)) (alpha := (12831763971/111912500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-120562357/1000000000 : ℝ)*X 0 0+(5493039339/10000000000 : ℝ)*X 0 1+(1270486057/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2667099/5000000 : ℝ)*X 1 0+(-710280229/5000000000 : ℝ)*X 1 1+(5081944193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1333549491/2500000000 : ℝ)*X 2 0+(254097211/500000000 : ℝ)*X 2 1+(-142056047/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4014663819/10000000000 : ℝ)*X 0 0+(420284389/1250000000 : ℝ)*X 0 1+(2364754151/5000000000 : ℝ)*X 0 2+(4014663819/10000000000 : ℝ)*X 1 0+(420284389/1250000000 : ℝ)*X 1 1+(2364754151/5000000000 : ℝ)*X 1 2+(4014663819/10000000000 : ℝ)*X 2 0+(420284389/1250000000 : ℝ)*X 2 1+(2364754151/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1205968559/10000000000 : ℝ)*X 0 0+(1272166117/2500000000 : ℝ)*X 0 1+(21944713/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((653164131/1250000000 : ℝ)*X 1 0+(-50816327/500000000 : ℝ)*X 1 1+(5486178277/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2612656509/5000000000 : ℝ)*X 2 0+(5486178343/10000000000 : ℝ)*X 2 1+(-1016326487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((501976367/1250000000 : ℝ)*X 0 0+(4707158211/10000000000 : ℝ)*X 0 1+(3385093087/10000000000 : ℝ)*X 0 2+(501976367/1250000000 : ℝ)*X 1 0+(4707158211/10000000000 : ℝ)*X 1 1+(3385093087/10000000000 : ℝ)*X 1 2+(501976367/1250000000 : ℝ)*X 2 0+(4707158211/10000000000 : ℝ)*X 2 1+(3385093087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1753_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1042184606220635282216924571/223825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (174603319/25000000000000 : ℝ)*(base19) + (155763457/25000000000000 : ℝ)*(base23) + (6288217/20000000000000 : ℝ)*(lower2) + (103720963/100000000000000 : ℝ)*(upper3) + (10678287/20000000000000 : ℝ)*(upper5) + (790986560884573/50000000000000 : ℝ)*(major0) + (790986560884573/50000000000000 : ℝ)*(major1) + (790986560884573/50000000000000 : ℝ)*(major2) + (76016659955683/3125000000000 : ℝ)*(sp0) + (1216269070416233/50000000000000 : ℝ)*(sp1) + (486507643238383/20000000000000 : ℝ)*(sp2) + (731405526178809/100000000000000 : ℝ)*(sp3) + (2860331943/50000000000000 : ℝ)*(sp4) + (344581097/20000000000000 : ℝ)*(sp7) + (365703624542147/50000000000000 : ℝ)*(f.failure) + (1216269419622871/50000000000000 : ℝ)*(f.sum) + (6646022260677/44765000000000000000000000000 : ℝ)*base66 + (2381133585317990143/895300000000000000000000000000000 : ℝ)*base68 + (1591638040390209857/895300000000000000000000000000000 : ℝ)*base69 + (5324287973564790143/895300000000000000000000000000000 : ℝ)*base72 + (76992884778847/44765000000000000000000000000 : ℝ)*base74 + (4851086935240790143/895300000000000000000000000000000 : ℝ)*base76 + (2060017960182790143/895300000000000000000000000000000 : ℝ)*base78 + (7651178682818390143/895300000000000000000000000000000 : ℝ)*base80 + (106888531873933/44765000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (24484871/5000000000000000000000 : ℝ)*base89 + (24484871/5000000000000000000000 : ℝ)*base91 + (24484871/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9276432190265460706869704763/895300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1366039933/100000000000000 : ℝ)*(base19) + (721614129/50000000000000 : ℝ)*(base23) + (382496573/100000000000000 : ℝ)*(lower1) + (60225421/25000000000000 : ℝ)*(upper3) + (3521659/10000000000000 : ℝ)*(lower4) + (42185939/20000000000000 : ℝ)*(upper5) + (1636007717861623/100000000000000 : ℝ)*(major0) + (1636007717861623/100000000000000 : ℝ)*(major1) + (1636007717861623/100000000000000 : ℝ)*(major2) + (290756353/25000000000000 : ℝ)*(sp2) + (62890639034709/2500000000000 : ℝ)*(sp4) + (2515624195348427/100000000000000 : ℝ)*(sp5) + (251562295513469/10000000000000 : ℝ)*(sp6) + (756389528959683/100000000000000 : ℝ)*(sp7) + (756389528959683/100000000000000 : ℝ)*(f.failure) + (62890639034709/2500000000000 : ℝ)*(f.sum) + (27822463883657/5595625000000000000000000000 : ℝ)*base66 + (22765189053786101693/1790600000000000000000000000000000 : ℝ)*base68 + (19927234575002901693/1790600000000000000000000000000000 : ℝ)*base70 + (59033915947190701693/1790600000000000000000000000000000 : ℝ)*base72 + (46569751290281/44765000000000000000000000000 : ℝ)*base74 + (99104612584580301693/1790600000000000000000000000000000 : ℝ)*base76 + (12230640319925901693/1790600000000000000000000000000000 : ℝ)*base78 + (17163735346384101693/1790600000000000000000000000000000 : ℝ)*base80 + (136939507684051/44765000000000000000000000000 : ℝ)*base82 + (64813319/10000000000000000000000 : ℝ)*base89 + (64813319/10000000000000000000000 : ℝ)*base91 + (64813319/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1753_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216291693/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17979/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4513/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9077/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8959/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1753_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1753_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216291693/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9077/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8959/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1753_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1753_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1753_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5807/1024 : ℝ) ≤ p) (hpb : p ≤ (5823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (216291693/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9077/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8959/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1753_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
