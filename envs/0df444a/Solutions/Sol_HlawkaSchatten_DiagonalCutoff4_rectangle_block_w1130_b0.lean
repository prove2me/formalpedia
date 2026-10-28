-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1130_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:26:42.87139+00:00
-- url     : https://prove2.me/submissions/8fa90b4e-120b-452c-b3f4-0ad30cf221c3

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
theorem support_rectangle_w1130_s0_0 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-118475897/625000000 : ℝ)*x 0 + (75713849/125000000 : ℝ)*x 1 + (2389476409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (118475897/625000000 : ℝ)^8323 ≤ (137700657271/1250000000000 : ℝ)^6275 := by
    have hnat : (118475897 : ℕ)^8323*1250000000000^6275 ≤ 137700657271^6275*625000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118475897 625000000 137700657271 1250000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75713849/125000000 : ℝ)^8323 ≤ (51428310949071/100000000000000 : ℝ)^6275 := by
    have hnat : (75713849 : ℕ)^8323*100000000000000^6275 ≤ 51428310949071^6275*125000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75713849 125000000 51428310949071 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2389476409/5000000000 : ℝ)^8323 ≤ (18777818230649/50000000000000 : ℝ)^6275 := by
    have hnat : (2389476409 : ℕ)^8323*50000000000000^6275 ≤ 18777818230649^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2389476409 5000000000 18777818230649 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-118475897/625000000 : ℝ), (75713849/125000000 : ℝ), (2389476409/5000000000 : ℝ)] ![(137700657271/1250000000000 : ℝ), (51428310949071/100000000000000 : ℝ), (18777818230649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-118475897/625000000 : ℝ)|^8323 ≤ (137700657271/1250000000000 : ℝ)^6275
        have hw : |(-118475897/625000000 : ℝ)|=(118475897/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(75713849/125000000 : ℝ)|^8323 ≤ (51428310949071/100000000000000 : ℝ)^6275
        have hw : |(75713849/125000000 : ℝ)|=(75713849/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2389476409/5000000000 : ℝ)|^8323 ≤ (18777818230649/50000000000000 : ℝ)^6275
        have hw : |(2389476409/5000000000 : ℝ)|=(2389476409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s0_1 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5517469631/10000000000 : ℝ)*x 0 + (-262946997/1000000000 : ℝ)*x 1 + (4778952673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5517469631/10000000000 : ℝ)^8323 ≤ (2272063479443/5000000000000 : ℝ)^6275 := by
    have hnat : (5517469631 : ℕ)^8323*5000000000000^6275 ≤ 2272063479443^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517469631 10000000000 2272063479443 5000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262946997/1000000000 : ℝ)^8323 ≤ (2125386932003/12500000000000 : ℝ)^6275 := by
    have hnat : (262946997 : ℕ)^8323*12500000000000^6275 ≤ 2125386932003^6275*1000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262946997 1000000000 2125386932003 12500000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4778952673/10000000000 : ℝ)^8323 ≤ (9388908737477/25000000000000 : ℝ)^6275 := by
    have hnat : (4778952673 : ℕ)^8323*25000000000000^6275 ≤ 9388908737477^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4778952673 10000000000 9388908737477 25000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5517469631/10000000000 : ℝ), (-262946997/1000000000 : ℝ), (4778952673/10000000000 : ℝ)] ![(2272063479443/5000000000000 : ℝ), (2125386932003/12500000000000 : ℝ), (9388908737477/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5517469631/10000000000 : ℝ)|^8323 ≤ (2272063479443/5000000000000 : ℝ)^6275
        have hw : |(5517469631/10000000000 : ℝ)|=(5517469631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-262946997/1000000000 : ℝ)|^8323 ≤ (2125386932003/12500000000000 : ℝ)^6275
        have hw : |(-262946997/1000000000 : ℝ)|=(262946997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4778952673/10000000000 : ℝ)|^8323 ≤ (9388908737477/25000000000000 : ℝ)^6275
        have hw : |(4778952673/10000000000 : ℝ)|=(4778952673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s0_2 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1103493967/2000000000 : ℝ)*x 0 + (4778952579/10000000000 : ℝ)*x 1 + (-20542733/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103493967/2000000000 : ℝ)^8323 ≤ (4544127181733/10000000000000 : ℝ)^6275 := by
    have hnat : (1103493967 : ℕ)^8323*10000000000000^6275 ≤ 4544127181733^6275*2000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103493967 2000000000 4544127181733 10000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4778952579/10000000000 : ℝ)^8323 ≤ (3755563397011/10000000000000 : ℝ)^6275 := by
    have hnat : (4778952579 : ℕ)^8323*10000000000000^6275 ≤ 3755563397011^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4778952579 10000000000 3755563397011 10000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20542733/78125000 : ℝ)^8323 ≤ (17003094203809/100000000000000 : ℝ)^6275 := by
    have hnat : (20542733 : ℕ)^8323*100000000000000^6275 ≤ 17003094203809^6275*78125000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20542733 78125000 17003094203809 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103493967/2000000000 : ℝ), (4778952579/10000000000 : ℝ), (-20542733/78125000 : ℝ)] ![(4544127181733/10000000000000 : ℝ), (3755563397011/10000000000000 : ℝ), (17003094203809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103493967/2000000000 : ℝ)|^8323 ≤ (4544127181733/10000000000000 : ℝ)^6275
        have hw : |(1103493967/2000000000 : ℝ)|=(1103493967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4778952579/10000000000 : ℝ)|^8323 ≤ (3755563397011/10000000000000 : ℝ)^6275
        have hw : |(4778952579/10000000000 : ℝ)|=(4778952579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-20542733/78125000 : ℝ)|^8323 ≤ (17003094203809/100000000000000 : ℝ)^6275
        have hw : |(-20542733/78125000 : ℝ)|=(20542733/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s0_3 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (168078517/400000000 : ℝ)*x 0 + (3121640951/10000000000 : ℝ)*x 1 + (1131702773/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168078517/400000000 : ℝ)^8323 ≤ (15831666222841/50000000000000 : ℝ)^6275 := by
    have hnat : (168078517 : ℕ)^8323*50000000000000^6275 ≤ 15831666222841^6275*400000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168078517 400000000 15831666222841 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3121640951/10000000000 : ℝ)^8323 ≤ (10674128840227/50000000000000 : ℝ)^6275 := by
    have hnat : (3121640951 : ℕ)^8323*50000000000000^6275 ≤ 10674128840227^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3121640951 10000000000 10674128840227 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131702773/2000000000 : ℝ)^8323 ≤ (9397681971227/20000000000000 : ℝ)^6275 := by
    have hnat : (1131702773 : ℕ)^8323*20000000000000^6275 ≤ 9397681971227^6275*2000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131702773 2000000000 9397681971227 20000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168078517/400000000 : ℝ), (3121640951/10000000000 : ℝ), (1131702773/2000000000 : ℝ)] ![(15831666222841/50000000000000 : ℝ), (10674128840227/50000000000000 : ℝ), (9397681971227/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168078517/400000000 : ℝ)|^8323 ≤ (15831666222841/50000000000000 : ℝ)^6275
        have hw : |(168078517/400000000 : ℝ)|=(168078517/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3121640951/10000000000 : ℝ)|^8323 ≤ (10674128840227/50000000000000 : ℝ)^6275
        have hw : |(3121640951/10000000000 : ℝ)|=(3121640951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131702773/2000000000 : ℝ)|^8323 ≤ (9397681971227/20000000000000 : ℝ)^6275
        have hw : |(1131702773/2000000000 : ℝ)|=(1131702773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s0_4 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-475198871/2500000000 : ℝ)*x 0 + (481193133/1000000000 : ℝ)*x 1 + (3011485363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (475198871/2500000000 : ℝ)^8323 ≤ (2211201318421/20000000000000 : ℝ)^6275 := by
    have hnat : (475198871 : ℕ)^8323*20000000000000^6275 ≤ 2211201318421^6275*2500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475198871 2500000000 2211201318421 20000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (481193133/1000000000 : ℝ)^8323 ≤ (2368735656777/6250000000000 : ℝ)^6275 := by
    have hnat : (481193133 : ℕ)^8323*6250000000000^6275 ≤ 2368735656777^6275*1000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481193133 1000000000 2368735656777 6250000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3011485363/5000000000 : ℝ)^8323 ≤ (51044222876969/100000000000000 : ℝ)^6275 := by
    have hnat : (3011485363 : ℕ)^8323*100000000000000^6275 ≤ 51044222876969^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3011485363 5000000000 51044222876969 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-475198871/2500000000 : ℝ), (481193133/1000000000 : ℝ), (3011485363/5000000000 : ℝ)] ![(2211201318421/20000000000000 : ℝ), (2368735656777/6250000000000 : ℝ), (51044222876969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-475198871/2500000000 : ℝ)|^8323 ≤ (2211201318421/20000000000000 : ℝ)^6275
        have hw : |(-475198871/2500000000 : ℝ)|=(475198871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(481193133/1000000000 : ℝ)|^8323 ≤ (2368735656777/6250000000000 : ℝ)^6275
        have hw : |(481193133/1000000000 : ℝ)|=(481193133/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3011485363/5000000000 : ℝ)|^8323 ≤ (51044222876969/100000000000000 : ℝ)^6275
        have hw : |(3011485363/5000000000 : ℝ)|=(3011485363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s0_5 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (64627823/125000000 : ℝ)*x 0 + (-1385451973/10000000000 : ℝ)*x 1 + (6022970643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64627823/125000000 : ℝ)^8323 ≤ (41687545390943/100000000000000 : ℝ)^6275 := by
    have hnat : (64627823 : ℕ)^8323*100000000000000^6275 ≤ 41687545390943^6275*125000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64627823 125000000 41687545390943 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1385451973/10000000000 : ℝ)^8323 ≤ (7268232658451/100000000000000 : ℝ)^6275 := by
    have hnat : (1385451973 : ℕ)^8323*100000000000000^6275 ≤ 7268232658451^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385451973 10000000000 7268232658451 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6022970643/10000000000 : ℝ)^8323 ≤ (12761055485993/25000000000000 : ℝ)^6275 := by
    have hnat : (6022970643 : ℕ)^8323*25000000000000^6275 ≤ 12761055485993^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6022970643 10000000000 12761055485993 25000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(64627823/125000000 : ℝ), (-1385451973/10000000000 : ℝ), (6022970643/10000000000 : ℝ)] ![(41687545390943/100000000000000 : ℝ), (7268232658451/100000000000000 : ℝ), (12761055485993/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(64627823/125000000 : ℝ)|^8323 ≤ (41687545390943/100000000000000 : ℝ)^6275
        have hw : |(64627823/125000000 : ℝ)|=(64627823/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1385451973/10000000000 : ℝ)|^8323 ≤ (7268232658451/100000000000000 : ℝ)^6275
        have hw : |(-1385451973/10000000000 : ℝ)|=(1385451973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6022970643/10000000000 : ℝ)|^8323 ≤ (12761055485993/25000000000000 : ℝ)^6275
        have hw : |(6022970643/10000000000 : ℝ)|=(6022970643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s0_6 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5170225863/10000000000 : ℝ)*x 0 + (3011485319/5000000000 : ℝ)*x 1 + (-1385451943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5170225863/10000000000 : ℝ)^8323 ≤ (20843772818459/50000000000000 : ℝ)^6275 := by
    have hnat : (5170225863 : ℕ)^8323*50000000000000^6275 ≤ 20843772818459^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170225863 10000000000 20843772818459 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3011485319/5000000000 : ℝ)^8323 ≤ (51044221887767/100000000000000 : ℝ)^6275 := by
    have hnat : (3011485319 : ℕ)^8323*100000000000000^6275 ≤ 51044221887767^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3011485319 5000000000 51044221887767 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1385451943/10000000000 : ℝ)^8323 ≤ (3634116224851/50000000000000 : ℝ)^6275 := by
    have hnat : (1385451943 : ℕ)^8323*50000000000000^6275 ≤ 3634116224851^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385451943 10000000000 3634116224851 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5170225863/10000000000 : ℝ), (3011485319/5000000000 : ℝ), (-1385451943/10000000000 : ℝ)] ![(20843772818459/50000000000000 : ℝ), (51044221887767/100000000000000 : ℝ), (3634116224851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5170225863/10000000000 : ℝ)|^8323 ≤ (20843772818459/50000000000000 : ℝ)^6275
        have hw : |(5170225863/10000000000 : ℝ)|=(5170225863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3011485319/5000000000 : ℝ)|^8323 ≤ (51044221887767/100000000000000 : ℝ)^6275
        have hw : |(3011485319/5000000000 : ℝ)|=(3011485319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1385451943/10000000000 : ℝ)|^8323 ≤ (3634116224851/50000000000000 : ℝ)^6275
        have hw : |(-1385451943/10000000000 : ℝ)|=(1385451943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s0_7 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (421224641/1000000000 : ℝ)*x 0 + (5593057931/10000000000 : ℝ)*x 1 + (159469813/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421224641/1000000000 : ℝ)^8323 ≤ (15883077004411/50000000000000 : ℝ)^6275 := by
    have hnat : (421224641 : ℕ)^8323*50000000000000^6275 ≤ 15883077004411^6275*1000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421224641 1000000000 15883077004411 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5593057931/10000000000 : ℝ)^8323 ≤ (46268826985671/100000000000000 : ℝ)^6275 := by
    have hnat : (5593057931 : ℕ)^8323*100000000000000^6275 ≤ 46268826985671^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5593057931 10000000000 46268826985671 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (159469813/500000000 : ℝ)^8323 ≤ (10982509496759/50000000000000 : ℝ)^6275 := by
    have hnat : (159469813 : ℕ)^8323*50000000000000^6275 ≤ 10982509496759^6275*500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159469813 500000000 10982509496759 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(421224641/1000000000 : ℝ), (5593057931/10000000000 : ℝ), (159469813/500000000 : ℝ)] ![(15883077004411/50000000000000 : ℝ), (46268826985671/100000000000000 : ℝ), (10982509496759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(421224641/1000000000 : ℝ)|^8323 ≤ (15883077004411/50000000000000 : ℝ)^6275
        have hw : |(421224641/1000000000 : ℝ)|=(421224641/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5593057931/10000000000 : ℝ)|^8323 ≤ (46268826985671/100000000000000 : ℝ)^6275
        have hw : |(5593057931/10000000000 : ℝ)|=(5593057931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(159469813/500000000 : ℝ)|^8323 ≤ (10982509496759/50000000000000 : ℝ)^6275
        have hw : |(159469813/500000000 : ℝ)|=(159469813/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1130_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (91/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27861/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4161/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4161 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4161*1^1024 ≤ 0^1024*1^4161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4161 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4161/1024 : ℝ) ≤ (2415350165310674137/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4161 ≤ (2415350165310674137/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4161*100000000000000000000^1024 ≤ 2415350165310674137^1024*5^4161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2415350165310674137 100000000000000000000 4161 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2415350165310674137/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4161 := by
      have hnat : (1 : ℕ)^1024*1^4161 ≤ 1^4161*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102415350165310674137/100000000000000000000 : ℝ) ≤ (2514726703166597/2500000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (102415350165310674137/100000000000000000000 : ℝ)^1024 ≤ (2514726703166597/2500000000000000 : ℝ)^4161 := by
      have hnat : (102415350165310674137 : ℕ)^1024*2500000000000000^4161 ≤ 2514726703166597^4161*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102415350165310674137 100000000000000000000 2514726703166597 2500000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514726703166597/2500000000000000 : ℝ)) (X := (102415350165310674137/100000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52415350165310674137/50000000000000000000 : ℝ) ≤ (1264726703166597/1250000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (52415350165310674137/50000000000000000000 : ℝ)^1024 ≤ (1264726703166597/1250000000000000 : ℝ)^4161 := by
      have hnat : (52415350165310674137 : ℕ)^1024*1250000000000000^4161 ≤ 1264726703166597^4161*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52415350165310674137 50000000000000000000 1264726703166597 1250000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1264726703166597/1250000000000000 : ℝ)) (X := (52415350165310674137/50000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14726703166597/1000000000000000 : ℝ)*(0 : ℝ))^(4161/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14726703166597/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2415350165310674137/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14726703166597/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4161/1024 : ℝ) := by
    rw [show (1 : ℝ)+(14726703166597/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2514726703166597/2500000000000000 : ℝ) by norm_num, show 1+(2415350165310674137/100000000000000000000 : ℝ)+(0 : ℝ)=(102415350165310674137/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2415350165310674137/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14726703166597/1000000000000000 : ℝ)*(2/5 : ℝ))^(4161/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(14726703166597/1000000000000000 : ℝ)*(2/5 : ℝ)=(1264726703166597/1250000000000000 : ℝ) by norm_num, show 1+2*(2415350165310674137/100000000000000000000 : ℝ)=(52415350165310674137/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14726703166597/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14726703166597/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14726703166597/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14726703166597/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14726703166597/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14726703166597/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-118475897/625000000 : ℝ)*X 0 0+(75713849/125000000 : ℝ)*X 0 1+(2389476409/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5517469631/10000000000 : ℝ)*X 1 0+(-262946997/1000000000 : ℝ)*X 1 1+(4778952673/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1103493967/2000000000 : ℝ)*X 2 0+(4778952579/10000000000 : ℝ)*X 2 1+(-20542733/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((168078517/400000000 : ℝ)*X 0 0+(3121640951/10000000000 : ℝ)*X 0 1+(1131702773/2000000000 : ℝ)*X 0 2+(168078517/400000000 : ℝ)*X 1 0+(3121640951/10000000000 : ℝ)*X 1 1+(1131702773/2000000000 : ℝ)*X 1 2+(168078517/400000000 : ℝ)*X 2 0+(3121640951/10000000000 : ℝ)*X 2 1+(1131702773/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-475198871/2500000000 : ℝ)*X 0 0+(481193133/1000000000 : ℝ)*X 0 1+(3011485363/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((64627823/125000000 : ℝ)*X 1 0+(-1385451973/10000000000 : ℝ)*X 1 1+(6022970643/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5170225863/10000000000 : ℝ)*X 2 0+(3011485319/5000000000 : ℝ)*X 2 1+(-1385451943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((421224641/1000000000 : ℝ)*X 0 0+(5593057931/10000000000 : ℝ)*X 0 1+(159469813/500000000 : ℝ)*X 0 2+(421224641/1000000000 : ℝ)*X 1 0+(5593057931/10000000000 : ℝ)*X 1 1+(159469813/500000000 : ℝ)*X 1 2+(421224641/1000000000 : ℝ)*X 2 0+(5593057931/10000000000 : ℝ)*X 2 1+(159469813/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (231553951839376980436377/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7456219/12500000000000 : ℝ)*(base1) + (135066043/12500000000000 : ℝ)*(base19) + (256602067/25000000000000 : ℝ)*(base23) + (10380933/12500000000000 : ℝ)*(base24) + (9287803/4000000000000 : ℝ)*(upper3) + (588286321268247/100000000000000 : ℝ)*(major0) + (588286321268247/100000000000000 : ℝ)*(major1) + (588286321268247/100000000000000 : ℝ)*(major2) + (39119055699619/5000000000000 : ℝ)*(sp0) + (195595580468821/25000000000000 : ℝ)*(sp1) + (97797786618487/12500000000000 : ℝ)*(sp2) + (197093587538459/50000000000000 : ℝ)*(sp3) + (2348061001/100000000000000 : ℝ)*(sp4) + (185103689/10000000000000 : ℝ)*(sp7) + (9854727144089/2500000000000 : ℝ)*(f.failure) + (195595850600907/25000000000000 : ℝ)*(f.sum) + (93604673154541/50000000000000000000000000000 : ℝ)*base66 + (275918513345459/100000000000000000000000000000 : ℝ)*base67 + (461764336454541/100000000000000000000000000000 : ℝ)*base70 + (335280941745459/100000000000000000000000000000 : ℝ)*base71 + (138262139254541/50000000000000000000000000000 : ℝ)*base74 + (605470606945459/100000000000000000000000000000 : ℝ)*base75 + (38559246145459/100000000000000000000000000000 : ℝ)*base77 + (483807227945459/100000000000000000000000000000 : ℝ)*base79 + (531646491154541/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (114803/250000000000000000000 : ℝ)*base89 + (114803/250000000000000000000 : ℝ)*base91 + (114803/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10022297979280154726403/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2675733/5000000000000 : ℝ)*(base1) + (982006927/100000000000000 : ℝ)*(base19) + (61556643/6250000000000 : ℝ)*(base23) + (105200721/100000000000000 : ℝ)*(upper3) + (116011629/100000000000000 : ℝ)*(upper5) + (155221134383667/25000000000000 : ℝ)*(major0) + (155221134383667/25000000000000 : ℝ)*(major1) + (155221134383667/25000000000000 : ℝ)*(major2) + (1979561251/100000000000000 : ℝ)*(sp1) + (984018203/50000000000000 : ℝ)*(sp2) + (33029481606393/4000000000000 : ℝ)*(sp4) + (412867012538493/50000000000000 : ℝ)*(sp5) + (82573403370247/10000000000000 : ℝ)*(sp6) + (208015950639433/50000000000000 : ℝ)*(sp7) + (416031954793527/100000000000000 : ℝ)*(f.failure) + (206434246661291/25000000000000 : ℝ)*(f.sum) + (30795557271199/12500000000000000000000000000 : ℝ)*base65 + (61064729371199/25000000000000000000000000000 : ℝ)*base67 + (42058285978801/25000000000000000000000000000 : ℝ)*base70 + (131765874746199/25000000000000000000000000000 : ℝ)*base71 + (33369061796199/12500000000000000000000000000 : ℝ)*base73 + (158183889746199/25000000000000000000000000000 : ℝ)*base75 + (76155674771199/25000000000000000000000000000 : ℝ)*base77 + (132743487271199/25000000000000000000000000000 : ℝ)*base79 + (5014449196199/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (31494429/10000000000000000000000 : ℝ)*base89 + (31494429/10000000000000000000000 : ℝ)*base91 + (31494429/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1130_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (91/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27861/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1130_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1130_s1_0 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1050573799/5000000000 : ℝ)*x 0 + (5704723979/10000000000 : ℝ)*x 1 + (624968709/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050573799/5000000000 : ℝ)^8323 ≤ (2525536528039/20000000000000 : ℝ)^6275 := by
    have hnat : (1050573799 : ℕ)^8323*20000000000000^6275 ≤ 2525536528039^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050573799 5000000000 2525536528039 20000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5704723979/10000000000 : ℝ)^8323 ≤ (23749028089783/50000000000000 : ℝ)^6275 := by
    have hnat : (5704723979 : ℕ)^8323*50000000000000^6275 ≤ 23749028089783^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5704723979 10000000000 23749028089783 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (624968709/1250000000 : ℝ)^8323 ≤ (7974852233097/20000000000000 : ℝ)^6275 := by
    have hnat : (624968709 : ℕ)^8323*20000000000000^6275 ≤ 7974852233097^6275*1250000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624968709 1250000000 7974852233097 20000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1050573799/5000000000 : ℝ), (5704723979/10000000000 : ℝ), (624968709/1250000000 : ℝ)] ![(2525536528039/20000000000000 : ℝ), (23749028089783/50000000000000 : ℝ), (7974852233097/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1050573799/5000000000 : ℝ)|^8323 ≤ (2525536528039/20000000000000 : ℝ)^6275
        have hw : |(-1050573799/5000000000 : ℝ)|=(1050573799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5704723979/10000000000 : ℝ)|^8323 ≤ (23749028089783/50000000000000 : ℝ)^6275
        have hw : |(5704723979/10000000000 : ℝ)|=(5704723979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(624968709/1250000000 : ℝ)|^8323 ≤ (7974852233097/20000000000000 : ℝ)^6275
        have hw : |(624968709/1250000000 : ℝ)|=(624968709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s1_1 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (135494529/250000000 : ℝ)*x 0 + (-496364749/2000000000 : ℝ)*x 1 + (4999749239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135494529/250000000 : ℝ)^8323 ≤ (1775089147051/4000000000000 : ℝ)^6275 := by
    have hnat : (135494529 : ℕ)^8323*4000000000000^6275 ≤ 1775089147051^6275*250000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135494529 250000000 1775089147051 4000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (496364749/2000000000 : ℝ)^8323 ≤ (984282170277/6250000000000 : ℝ)^6275 := by
    have hnat : (496364749 : ℕ)^8323*6250000000000^6275 ≤ 984282170277^6275*2000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496364749 2000000000 984282170277 6250000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4999749239/10000000000 : ℝ)^8323 ≤ (39874256585137/100000000000000 : ℝ)^6275 := by
    have hnat : (4999749239 : ℕ)^8323*100000000000000^6275 ≤ 39874256585137^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999749239 10000000000 39874256585137 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135494529/250000000 : ℝ), (-496364749/2000000000 : ℝ), (4999749239/10000000000 : ℝ)] ![(1775089147051/4000000000000 : ℝ), (984282170277/6250000000000 : ℝ), (39874256585137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135494529/250000000 : ℝ)|^8323 ≤ (1775089147051/4000000000000 : ℝ)^6275
        have hw : |(135494529/250000000 : ℝ)|=(135494529/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-496364749/2000000000 : ℝ)|^8323 ≤ (984282170277/6250000000000 : ℝ)^6275
        have hw : |(-496364749/2000000000 : ℝ)|=(496364749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4999749239/10000000000 : ℝ)|^8323 ≤ (39874256585137/100000000000000 : ℝ)^6275
        have hw : |(4999749239/10000000000 : ℝ)|=(4999749239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s1_2 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (33873643/62500000 : ℝ)*x 0 + (1249936923/2500000000 : ℝ)*x 1 + (-248182347/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33873643/62500000 : ℝ)^8323 ≤ (44377247356111/100000000000000 : ℝ)^6275 := by
    have hnat : (33873643 : ℕ)^8323*100000000000000^6275 ≤ 44377247356111^6275*62500000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33873643 62500000 44377247356111 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1249936923/2500000000 : ℝ)^8323 ≤ (39874240220709/100000000000000 : ℝ)^6275 := by
    have hnat : (1249936923 : ℕ)^8323*100000000000000^6275 ≤ 39874240220709^6275*2500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249936923 2500000000 39874240220709 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (248182347/1000000000 : ℝ)^8323 ≤ (15748512409877/100000000000000 : ℝ)^6275 := by
    have hnat : (248182347 : ℕ)^8323*100000000000000^6275 ≤ 15748512409877^6275*1000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248182347 1000000000 15748512409877 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33873643/62500000 : ℝ), (1249936923/2500000000 : ℝ), (-248182347/1000000000 : ℝ)] ![(44377247356111/100000000000000 : ℝ), (39874240220709/100000000000000 : ℝ), (15748512409877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33873643/62500000 : ℝ)|^8323 ≤ (44377247356111/100000000000000 : ℝ)^6275
        have hw : |(33873643/62500000 : ℝ)|=(33873643/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1249936923/2500000000 : ℝ)|^8323 ≤ (39874240220709/100000000000000 : ℝ)^6275
        have hw : |(1249936923/2500000000 : ℝ)|=(1249936923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-248182347/1000000000 : ℝ)|^8323 ≤ (15748512409877/100000000000000 : ℝ)^6275
        have hw : |(-248182347/1000000000 : ℝ)|=(248182347/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s1_3 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2159226943/5000000000 : ℝ)*x 0 + (3674785593/10000000000 : ℝ)*x 1 + (1268502813/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159226943/5000000000 : ℝ)^8323 ≤ (32832861712633/100000000000000 : ℝ)^6275 := by
    have hnat : (2159226943 : ℕ)^8323*100000000000000^6275 ≤ 32832861712633^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159226943 5000000000 32832861712633 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3674785593/10000000000 : ℝ)^8323 ≤ (26505427742089/100000000000000 : ℝ)^6275 := by
    have hnat : (3674785593 : ℕ)^8323*100000000000000^6275 ≤ 26505427742089^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3674785593 10000000000 26505427742089 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1268502813/2500000000 : ℝ)^8323 ≤ (20330855267567/50000000000000 : ℝ)^6275 := by
    have hnat : (1268502813 : ℕ)^8323*50000000000000^6275 ≤ 20330855267567^6275*2500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268502813 2500000000 20330855267567 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159226943/5000000000 : ℝ), (3674785593/10000000000 : ℝ), (1268502813/2500000000 : ℝ)] ![(32832861712633/100000000000000 : ℝ), (26505427742089/100000000000000 : ℝ), (20330855267567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159226943/5000000000 : ℝ)|^8323 ≤ (32832861712633/100000000000000 : ℝ)^6275
        have hw : |(2159226943/5000000000 : ℝ)|=(2159226943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3674785593/10000000000 : ℝ)|^8323 ≤ (26505427742089/100000000000000 : ℝ)^6275
        have hw : |(3674785593/10000000000 : ℝ)|=(3674785593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1268502813/2500000000 : ℝ)|^8323 ≤ (20330855267567/50000000000000 : ℝ)^6275
        have hw : |(1268502813/2500000000 : ℝ)|=(1268502813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s1_4 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-525492699/2500000000 : ℝ)*x 0 + (3913609/7812500 : ℝ)*x 1 + (2847430827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525492699/2500000000 : ℝ)^8323 ≤ (6317122539991/50000000000000 : ℝ)^6275 := by
    have hnat : (525492699 : ℕ)^8323*50000000000000^6275 ≤ 6317122539991^6275*2500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525492699 2500000000 6317122539991 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3913609/7812500 : ℝ)^8323 ≤ (39976582734059/100000000000000 : ℝ)^6275 := by
    have hnat : (3913609 : ℕ)^8323*100000000000000^6275 ≤ 39976582734059^6275*7812500^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3913609 7812500 39976582734059 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2847430827/5000000000 : ℝ)^8323 ≤ (23694586087129/50000000000000 : ℝ)^6275 := by
    have hnat : (2847430827 : ℕ)^8323*50000000000000^6275 ≤ 23694586087129^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2847430827 5000000000 23694586087129 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-525492699/2500000000 : ℝ), (3913609/7812500 : ℝ), (2847430827/5000000000 : ℝ)] ![(6317122539991/50000000000000 : ℝ), (39976582734059/100000000000000 : ℝ), (23694586087129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-525492699/2500000000 : ℝ)|^8323 ≤ (6317122539991/50000000000000 : ℝ)^6275
        have hw : |(-525492699/2500000000 : ℝ)|=(525492699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3913609/7812500 : ℝ)|^8323 ≤ (39976582734059/100000000000000 : ℝ)^6275
        have hw : |(3913609/7812500 : ℝ)|=(3913609/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2847430827/5000000000 : ℝ)|^8323 ≤ (23694586087129/50000000000000 : ℝ)^6275
        have hw : |(2847430827/5000000000 : ℝ)|=(2847430827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s1_5 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2619573821/5000000000 : ℝ)*x 0 + (-71468439/400000000 : ℝ)*x 1 + (569486139/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2619573821/5000000000 : ℝ)^8323 ≤ (21213116248121/50000000000000 : ℝ)^6275 := by
    have hnat : (2619573821 : ℕ)^8323*50000000000000^6275 ≤ 21213116248121^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619573821 5000000000 21213116248121 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71468439/400000000 : ℝ)^8323 ≤ (5092299116453/50000000000000 : ℝ)^6275 := by
    have hnat : (71468439 : ℕ)^8323*50000000000000^6275 ≤ 5092299116453^6275*400000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71468439 400000000 5092299116453 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (569486139/1000000000 : ℝ)^8323 ≤ (370227884847/781250000000 : ℝ)^6275 := by
    have hnat : (569486139 : ℕ)^8323*781250000000^6275 ≤ 370227884847^6275*1000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569486139 1000000000 370227884847 781250000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2619573821/5000000000 : ℝ), (-71468439/400000000 : ℝ), (569486139/1000000000 : ℝ)] ![(21213116248121/50000000000000 : ℝ), (5092299116453/50000000000000 : ℝ), (370227884847/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2619573821/5000000000 : ℝ)|^8323 ≤ (21213116248121/50000000000000 : ℝ)^6275
        have hw : |(2619573821/5000000000 : ℝ)|=(2619573821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-71468439/400000000 : ℝ)|^8323 ≤ (5092299116453/50000000000000 : ℝ)^6275
        have hw : |(-71468439/400000000 : ℝ)|=(71468439/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(569486139/1000000000 : ℝ)|^8323 ≤ (370227884847/781250000000 : ℝ)^6275
        have hw : |(569486139/1000000000 : ℝ)|=(569486139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s1_6 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5239147687/10000000000 : ℝ)*x 0 + (2847430781/5000000000 : ℝ)*x 1 + (-89335533/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5239147687/10000000000 : ℝ)^8323 ≤ (21213116489791/50000000000000 : ℝ)^6275 := by
    have hnat : (5239147687 : ℕ)^8323*50000000000000^6275 ≤ 21213116489791^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239147687 10000000000 21213116489791 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2847430781/5000000000 : ℝ)^8323 ≤ (11847292789707/25000000000000 : ℝ)^6275 := by
    have hnat : (2847430781 : ℕ)^8323*25000000000000^6275 ≤ 11847292789707^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2847430781 5000000000 11847292789707 25000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89335533/500000000 : ℝ)^8323 ≤ (254614896283/2500000000000 : ℝ)^6275 := by
    have hnat : (89335533 : ℕ)^8323*2500000000000^6275 ≤ 254614896283^6275*500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89335533 500000000 254614896283 2500000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5239147687/10000000000 : ℝ), (2847430781/5000000000 : ℝ), (-89335533/500000000 : ℝ)] ![(21213116489791/50000000000000 : ℝ), (11847292789707/25000000000000 : ℝ), (254614896283/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5239147687/10000000000 : ℝ)|^8323 ≤ (21213116489791/50000000000000 : ℝ)^6275
        have hw : |(5239147687/10000000000 : ℝ)|=(5239147687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2847430781/5000000000 : ℝ)|^8323 ≤ (11847292789707/25000000000000 : ℝ)^6275
        have hw : |(2847430781/5000000000 : ℝ)|=(2847430781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-89335533/500000000 : ℝ)|^8323 ≤ (254614896283/2500000000000 : ℝ)^6275
        have hw : |(-89335533/500000000 : ℝ)|=(89335533/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s1_7 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4320084753/10000000000 : ℝ)*x 0 + (5054819479/10000000000 : ℝ)*x 1 + (230897447/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320084753/10000000000 : ℝ)^8323 ≤ (6569861782137/20000000000000 : ℝ)^6275 := by
    have hnat : (4320084753 : ℕ)^8323*20000000000000^6275 ≤ 6569861782137^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320084753 10000000000 6569861782137 20000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5054819479/10000000000 : ℝ)^8323 ≤ (40457843452221/100000000000000 : ℝ)^6275 := by
    have hnat : (5054819479 : ℕ)^8323*100000000000000^6275 ≤ 40457843452221^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5054819479 10000000000 40457843452221 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (230897447/625000000 : ℝ)^8323 ≤ (26692847621609/100000000000000 : ℝ)^6275 := by
    have hnat : (230897447 : ℕ)^8323*100000000000000^6275 ≤ 26692847621609^6275*625000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230897447 625000000 26692847621609 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320084753/10000000000 : ℝ), (5054819479/10000000000 : ℝ), (230897447/625000000 : ℝ)] ![(6569861782137/20000000000000 : ℝ), (40457843452221/100000000000000 : ℝ), (26692847621609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320084753/10000000000 : ℝ)|^8323 ≤ (6569861782137/20000000000000 : ℝ)^6275
        have hw : |(4320084753/10000000000 : ℝ)|=(4320084753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5054819479/10000000000 : ℝ)|^8323 ≤ (40457843452221/100000000000000 : ℝ)^6275
        have hw : |(5054819479/10000000000 : ℝ)|=(5054819479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(230897447/625000000 : ℝ)|^8323 ≤ (26692847621609/100000000000000 : ℝ)^6275
        have hw : |(230897447/625000000 : ℝ)|=(230897447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1130_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27861/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2791/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5123/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27861/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (91/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27861/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (91/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27861/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (91/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27861/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (91/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27861/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (91/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27861/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (91/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (91/25000 : ℝ) ^ (4161/1024 : ℝ) ≤ (2458230653/20000000000000000000 : ℝ) := by
    have hpowers : (91/25000 : ℝ)^4161 ≤ (2458230653/20000000000000000000 : ℝ)^1024 := by
      have hnat : (91 : ℕ)^4161*20000000000000000000^1024 ≤ 2458230653^1024*25000^4161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91 25000 2458230653 20000000000000000000 4161 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91/25000 : ℝ)) (X := (2458230653/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27861/100000 : ℝ) ^ (4161/1024 : ℝ) ≤ (277796713687503137/50000000000000000000 : ℝ) := by
    have hpowers : (27861/100000 : ℝ)^4161 ≤ (277796713687503137/50000000000000000000 : ℝ)^1024 := by
      have hnat : (27861 : ℕ)^4161*50000000000000000000^1024 ≤ 277796713687503137^1024*100000^4161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27861 100000 277796713687503137 50000000000000000000 4161 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27861/100000 : ℝ)) (X := (277796713687503137/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000002458230653/10000000000000000000 : ℝ) ≤ (5000000000302479/5000000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (10000000002458230653/10000000000000000000 : ℝ)^1024 ≤ (5000000000302479/5000000000000000 : ℝ)^4161 := by
      have hnat : (10000000002458230653 : ℕ)^1024*5000000000000000^4161 ≤ 5000000000302479^4161*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000002458230653 10000000000000000000 5000000000302479 5000000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000302479/5000000000000000 : ℝ)) (X := (10000000002458230653/10000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100555593439666159539/100000000000000000000 : ℝ) ≤ (500682215836017/500000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (100555593439666159539/100000000000000000000 : ℝ)^1024 ≤ (500682215836017/500000000000000 : ℝ)^4161 := by
      have hnat : (100555593439666159539 : ℕ)^1024*500000000000000^4161 ≤ 500682215836017^4161*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100555593439666159539 100000000000000000000 500682215836017 500000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500682215836017/500000000000000 : ℝ)) (X := (100555593439666159539/100000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25277796713687503137/25000000000000000000 : ℝ) ≤ (5013644316417861/5000000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (25277796713687503137/25000000000000000000 : ℝ)^1024 ≤ (5013644316417861/5000000000000000 : ℝ)^4161 := by
      have hnat : (25277796713687503137 : ℕ)^1024*5000000000000000^4161 ≤ 5013644316417861^4161*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25277796713687503137 25000000000000000000 5013644316417861 5000000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013644316417861/5000000000000000 : ℝ)) (X := (25277796713687503137/25000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2458230653/20000000000000000000 : ℝ) ≤ ((27496006695450253203/27497000000000000000 : ℝ)+2*(6822158057691/1374850000000000 : ℝ)*(91/25000 : ℝ))^(4161/1024 : ℝ) := by
    rw [show (27496006695450253203/27497000000000000000 : ℝ)+2*(6822158057691/1374850000000000 : ℝ)*(91/25000 : ℝ)=(5000000000302479/5000000000000000 : ℝ) by norm_num, show 1+2*(2458230653/20000000000000000000 : ℝ)=(10000000002458230653/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(277796713687503137/50000000000000000000 : ℝ)+(2458230653/20000000000000000000 : ℝ) ≤ ((27496006695450253203/27497000000000000000 : ℝ)+(6822158057691/1374850000000000 : ℝ)*((27861/100000 : ℝ)+(91/25000 : ℝ)))^(4161/1024 : ℝ) := by
    rw [show (27496006695450253203/27497000000000000000 : ℝ)+(6822158057691/1374850000000000 : ℝ)*((27861/100000 : ℝ)+(91/25000 : ℝ))=(500682215836017/500000000000000 : ℝ) by norm_num, show 1+(277796713687503137/50000000000000000000 : ℝ)+(2458230653/20000000000000000000 : ℝ)=(100555593439666159539/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(277796713687503137/50000000000000000000 : ℝ) ≤ ((27496006695450253203/27497000000000000000 : ℝ)+2*(6822158057691/1374850000000000 : ℝ)*(27861/100000 : ℝ))^(4161/1024 : ℝ) := by
    rw [show (27496006695450253203/27497000000000000000 : ℝ)+2*(6822158057691/1374850000000000 : ℝ)*(27861/100000 : ℝ)=(5013644316417861/5000000000000000 : ℝ) by norm_num, show 1+2*(277796713687503137/50000000000000000000 : ℝ)=(25277796713687503137/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27496006695450253203/27497000000000000000 : ℝ)*(X 1 0+X 2 0)+(6822158057691/1374850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (91/25000 : ℝ)) (hi := (27861/100000 : ℝ)) (c := (27496006695450253203/27497000000000000000 : ℝ)) (alpha := (6822158057691/1374850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27496006695450253203/27497000000000000000 : ℝ)*(X 0 1+X 2 1)+(6822158057691/1374850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (91/25000 : ℝ)) (hi := (27861/100000 : ℝ)) (c := (27496006695450253203/27497000000000000000 : ℝ)) (alpha := (6822158057691/1374850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27496006695450253203/27497000000000000000 : ℝ)*(X 0 2+X 1 2)+(6822158057691/1374850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (91/25000 : ℝ)) (hi := (27861/100000 : ℝ)) (c := (27496006695450253203/27497000000000000000 : ℝ)) (alpha := (6822158057691/1374850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1050573799/5000000000 : ℝ)*X 0 0+(5704723979/10000000000 : ℝ)*X 0 1+(624968709/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((135494529/250000000 : ℝ)*X 1 0+(-496364749/2000000000 : ℝ)*X 1 1+(4999749239/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((33873643/62500000 : ℝ)*X 2 0+(1249936923/2500000000 : ℝ)*X 2 1+(-248182347/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2159226943/5000000000 : ℝ)*X 0 0+(3674785593/10000000000 : ℝ)*X 0 1+(1268502813/2500000000 : ℝ)*X 0 2+(2159226943/5000000000 : ℝ)*X 1 0+(3674785593/10000000000 : ℝ)*X 1 1+(1268502813/2500000000 : ℝ)*X 1 2+(2159226943/5000000000 : ℝ)*X 2 0+(3674785593/10000000000 : ℝ)*X 2 1+(1268502813/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-525492699/2500000000 : ℝ)*X 0 0+(3913609/7812500 : ℝ)*X 0 1+(2847430827/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2619573821/5000000000 : ℝ)*X 1 0+(-71468439/400000000 : ℝ)*X 1 1+(569486139/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5239147687/10000000000 : ℝ)*X 2 0+(2847430781/5000000000 : ℝ)*X 2 1+(-89335533/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4320084753/10000000000 : ℝ)*X 0 0+(5054819479/10000000000 : ℝ)*X 0 1+(230897447/625000000 : ℝ)*X 0 2+(4320084753/10000000000 : ℝ)*X 1 0+(5054819479/10000000000 : ℝ)*X 1 1+(230897447/625000000 : ℝ)*X 1 2+(4320084753/10000000000 : ℝ)*X 2 0+(5054819479/10000000000 : ℝ)*X 2 1+(230897447/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4565880139708588179233069679/687425000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (416563157/100000000000000 : ℝ)*(base1) + (550901111/50000000000000 : ℝ)*(base19) + (768492389/50000000000000 : ℝ)*(base23) + (14985263/100000000000000 : ℝ)*(base24) + (175239261/100000000000000 : ℝ)*(upper5) + (533294780109769/50000000000000 : ℝ)*(major0) + (533294780109769/50000000000000 : ℝ)*(major1) + (533294780109769/50000000000000 : ℝ)*(major2) + (709246363739337/50000000000000 : ℝ)*(sp0) + (56739810201303/4000000000000 : ℝ)*(sp1) + (354623701216189/25000000000000 : ℝ)*(sp2) + (357340850241311/50000000000000 : ℝ)*(sp3) + (50573991/1250000000000 : ℝ)*(sp4) + (85031667/20000000000000 : ℝ)*(sp7) + (142936508440823/20000000000000 : ℝ)*(f.failure) + (1418496356834797/100000000000000 : ℝ)*(f.sum) + (197767405122241/137485000000000000000000000000 : ℝ)*base65 + (4529199178239970107/1374850000000000000000000000000000 : ℝ)*base67 + (1686645995658220107/1374850000000000000000000000000000 : ℝ)*base69 + (5950018320921529893/1374850000000000000000000000000000 : ℝ)*base72 + (227652811929389/34371250000000000000000000000 : ℝ)*base73 + (2777346978739770107/1374850000000000000000000000000000 : ℝ)*base75 + (6105225522379529893/1374850000000000000000000000000000 : ℝ)*base78 + (641297013545870107/1374850000000000000000000000000000 : ℝ)*base79 + (100754417875919/34371250000000000000000000000 : ℝ)*base81 + (16093021/2000000000000000000000 : ℝ)*base89 + (16093021/2000000000000000000000 : ℝ)*base91 + (16093021/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2772451635453165275583878823/343712500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (97650889/100000000000000 : ℝ)*(base1) + (1787056067/100000000000000 : ℝ)*(base19) + (1821021873/100000000000000 : ℝ)*(base23) + (174038863/100000000000000 : ℝ)*(upper3) + (45352699/25000000000000 : ℝ)*(upper5) + (548489529670847/50000000000000 : ℝ)*(major0) + (548489529670847/50000000000000 : ℝ)*(major1) + (548489529670847/50000000000000 : ℝ)*(major2) + (7210166373/100000000000000 : ℝ)*(sp1) + (978974939/12500000000000 : ℝ)*(sp2) + (1458912516570531/100000000000000 : ℝ)*(sp4) + (1458903421697203/100000000000000 : ℝ)*(sp5) + (1458902766098257/100000000000000 : ℝ)*(sp6) + (29401813329589/4000000000000 : ℝ)*(sp7) + (367522715445307/50000000000000 : ℝ)*(f.failure) + (729456209459821/50000000000000 : ℝ)*(f.sum) + (349648813896657/137485000000000000000000000000 : ℝ)*base66 + (1967656791217262941/1374850000000000000000000000000000 : ℝ)*base67 + (1271439047945887059/1374850000000000000000000000000000 : ℝ)*base70 + (9446791347402337059/1374850000000000000000000000000000 : ℝ)*base72 + (387604432501583/137485000000000000000000000000 : ℝ)*base73 + (14370341729964437059/1374850000000000000000000000000000 : ℝ)*base76 + (7136848274060387059/1374850000000000000000000000000000 : ℝ)*base78 + (2686291049740037059/1374850000000000000000000000000000 : ℝ)*base80 + (17680148348901/17185625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (55580489/5000000000000000000000 : ℝ)*base89 + (55580489/5000000000000000000000 : ℝ)*base91 + (55580489/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1130_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27861/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2791/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5123/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1130_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1130_s2_0 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2155024907/10000000000 : ℝ)*x 0 + (220524479/400000000 : ℝ)*x 1 + (5157114271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155024907/10000000000 : ℝ)^8323 ≤ (2611789153667/20000000000000 : ℝ)^6275 := by
    have hnat : (2155024907 : ℕ)^8323*20000000000000^6275 ≤ 2611789153667^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155024907 10000000000 2611789153667 20000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220524479/400000000 : ℝ)^8323 ≤ (9078734648287/20000000000000 : ℝ)^6275 := by
    have hnat : (220524479 : ℕ)^8323*20000000000000^6275 ≤ 9078734648287^6275*400000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220524479 400000000 9078734648287 20000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5157114271/10000000000 : ℝ)^8323 ≤ (1298355655467/3125000000000 : ℝ)^6275 := by
    have hnat : (5157114271 : ℕ)^8323*3125000000000^6275 ≤ 1298355655467^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5157114271 10000000000 1298355655467 3125000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2155024907/10000000000 : ℝ), (220524479/400000000 : ℝ), (5157114271/10000000000 : ℝ)] ![(2611789153667/20000000000000 : ℝ), (9078734648287/20000000000000 : ℝ), (1298355655467/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2155024907/10000000000 : ℝ)|^8323 ≤ (2611789153667/20000000000000 : ℝ)^6275
        have hw : |(-2155024907/10000000000 : ℝ)|=(2155024907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(220524479/400000000 : ℝ)|^8323 ≤ (9078734648287/20000000000000 : ℝ)^6275
        have hw : |(220524479/400000000 : ℝ)|=(220524479/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5157114271/10000000000 : ℝ)|^8323 ≤ (1298355655467/3125000000000 : ℝ)^6275
        have hw : |(5157114271/10000000000 : ℝ)|=(5157114271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s2_1 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5374382721/10000000000 : ℝ)*x 0 + (-2340195817/10000000000 : ℝ)*x 1 + (2578557993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374382721/10000000000 : ℝ)^8323 ≤ (43884860093007/100000000000000 : ℝ)^6275 := by
    have hnat : (5374382721 : ℕ)^8323*100000000000000^6275 ≤ 43884860093007^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374382721 10000000000 43884860093007 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2340195817/10000000000 : ℝ)^8323 ≤ (7283870293301/50000000000000 : ℝ)^6275 := by
    have hnat : (2340195817 : ℕ)^8323*50000000000000^6275 ≤ 7283870293301^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2340195817 10000000000 7283870293301 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2578557993/5000000000 : ℝ)^8323 ≤ (10386849825231/25000000000000 : ℝ)^6275 := by
    have hnat : (2578557993 : ℕ)^8323*25000000000000^6275 ≤ 10386849825231^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2578557993 5000000000 10386849825231 25000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374382721/10000000000 : ℝ), (-2340195817/10000000000 : ℝ), (2578557993/5000000000 : ℝ)] ![(43884860093007/100000000000000 : ℝ), (7283870293301/50000000000000 : ℝ), (10386849825231/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374382721/10000000000 : ℝ)|^8323 ≤ (43884860093007/100000000000000 : ℝ)^6275
        have hw : |(5374382721/10000000000 : ℝ)|=(5374382721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2340195817/10000000000 : ℝ)|^8323 ≤ (7283870293301/50000000000000 : ℝ)^6275
        have hw : |(-2340195817/10000000000 : ℝ)|=(2340195817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2578557993/5000000000 : ℝ)|^8323 ≤ (10386849825231/25000000000000 : ℝ)^6275
        have hw : |(2578557993/5000000000 : ℝ)|=(2578557993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s2_2 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (671797831/1250000000 : ℝ)*x 0 + (1031423199/2000000000 : ℝ)*x 1 + (-1170097951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671797831/1250000000 : ℝ)^8323 ≤ (21942429651187/50000000000000 : ℝ)^6275 := by
    have hnat : (671797831 : ℕ)^8323*50000000000000^6275 ≤ 21942429651187^6275*1250000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671797831 1250000000 21942429651187 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031423199/2000000000 : ℝ)^8323 ≤ (8309479879419/20000000000000 : ℝ)^6275 := by
    have hnat : (1031423199 : ℕ)^8323*20000000000000^6275 ≤ 8309479879419^6275*2000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031423199 2000000000 8309479879419 20000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1170097951/5000000000 : ℝ)^8323 ≤ (14567741288421/100000000000000 : ℝ)^6275 := by
    have hnat : (1170097951 : ℕ)^8323*100000000000000^6275 ≤ 14567741288421^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170097951 5000000000 14567741288421 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671797831/1250000000 : ℝ), (1031423199/2000000000 : ℝ), (-1170097951/5000000000 : ℝ)] ![(21942429651187/50000000000000 : ℝ), (8309479879419/20000000000000 : ℝ), (14567741288421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671797831/1250000000 : ℝ)|^8323 ≤ (21942429651187/50000000000000 : ℝ)^6275
        have hw : |(671797831/1250000000 : ℝ)|=(671797831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031423199/2000000000 : ℝ)|^8323 ≤ (8309479879419/20000000000000 : ℝ)^6275
        have hw : |(1031423199/2000000000 : ℝ)|=(1031423199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1170097951/5000000000 : ℝ)|^8323 ≤ (14567741288421/100000000000000 : ℝ)^6275
        have hw : |(-1170097951/5000000000 : ℝ)|=(1170097951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s2_3 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088846399/2500000000 : ℝ)*x 0 + (1004083973/2500000000 : ℝ)*x 1 + (1180728321/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088846399/2500000000 : ℝ)^8323 ≤ (33205811658053/100000000000000 : ℝ)^6275 := by
    have hnat : (1088846399 : ℕ)^8323*100000000000000^6275 ≤ 33205811658053^6275*2500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088846399 2500000000 33205811658053 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004083973/2500000000 : ℝ)^8323 ≤ (745538811717/2500000000000 : ℝ)^6275 := by
    have hnat : (1004083973 : ℕ)^8323*2500000000000^6275 ≤ 745538811717^6275*2500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004083973 2500000000 745538811717 2500000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1180728321/2500000000 : ℝ)^8323 ≤ (18486317929081/50000000000000 : ℝ)^6275 := by
    have hnat : (1180728321 : ℕ)^8323*50000000000000^6275 ≤ 18486317929081^6275*2500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1180728321 2500000000 18486317929081 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088846399/2500000000 : ℝ), (1004083973/2500000000 : ℝ), (1180728321/2500000000 : ℝ)] ![(33205811658053/100000000000000 : ℝ), (745538811717/2500000000000 : ℝ), (18486317929081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088846399/2500000000 : ℝ)|^8323 ≤ (33205811658053/100000000000000 : ℝ)^6275
        have hw : |(1088846399/2500000000 : ℝ)|=(1088846399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004083973/2500000000 : ℝ)|^8323 ≤ (745538811717/2500000000000 : ℝ)^6275
        have hw : |(1004083973/2500000000 : ℝ)|=(1004083973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1180728321/2500000000 : ℝ)|^8323 ≤ (18486317929081/50000000000000 : ℝ)^6275
        have hw : |(1180728321/2500000000 : ℝ)|=(1180728321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s2_4 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2155130919/10000000000 : ℝ)*x 0 + (257979501/500000000 : ℝ)*x 1 + (5510611183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155130919/10000000000 : ℝ)^8323 ≤ (13059797848593/100000000000000 : ℝ)^6275 := by
    have hnat : (2155130919 : ℕ)^8323*100000000000000^6275 ≤ 13059797848593^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155130919 10000000000 13059797848593 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257979501/500000000 : ℝ)^8323 ≤ (41573838163493/100000000000000 : ℝ)^6275 := by
    have hnat : (257979501 : ℕ)^8323*100000000000000^6275 ≤ 41573838163493^6275*500000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257979501 500000000 41573838163493 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5510611183/10000000000 : ℝ)^8323 ≤ (45366363971051/100000000000000 : ℝ)^6275 := by
    have hnat : (5510611183 : ℕ)^8323*100000000000000^6275 ≤ 45366363971051^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510611183 10000000000 45366363971051 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2155130919/10000000000 : ℝ), (257979501/500000000 : ℝ), (5510611183/10000000000 : ℝ)] ![(13059797848593/100000000000000 : ℝ), (41573838163493/100000000000000 : ℝ), (45366363971051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2155130919/10000000000 : ℝ)|^8323 ≤ (13059797848593/100000000000000 : ℝ)^6275
        have hw : |(-2155130919/10000000000 : ℝ)|=(2155130919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(257979501/500000000 : ℝ)|^8323 ≤ (41573838163493/100000000000000 : ℝ)^6275
        have hw : |(257979501/500000000 : ℝ)|=(257979501/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5510611183/10000000000 : ℝ)|^8323 ≤ (45366363971051/100000000000000 : ℝ)^6275
        have hw : |(5510611183/10000000000 : ℝ)|=(5510611183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s2_5 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1056825849/2000000000 : ℝ)*x 0 + (-1986698839/10000000000 : ℝ)*x 1 + (68882647/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056825849/2000000000 : ℝ)^8323 ≤ (42910050257851/100000000000000 : ℝ)^6275 := by
    have hnat : (1056825849 : ℕ)^8323*100000000000000^6275 ≤ 42910050257851^6275*2000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056825849 2000000000 42910050257851 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1986698839/10000000000 : ℝ)^8323 ≤ (2930894865521/25000000000000 : ℝ)^6275 := by
    have hnat : (1986698839 : ℕ)^8323*25000000000000^6275 ≤ 2930894865521^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986698839 10000000000 2930894865521 25000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68882647/125000000 : ℝ)^8323 ≤ (2835398141973/6250000000000 : ℝ)^6275 := by
    have hnat : (68882647 : ℕ)^8323*6250000000000^6275 ≤ 2835398141973^6275*125000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68882647 125000000 2835398141973 6250000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056825849/2000000000 : ℝ), (-1986698839/10000000000 : ℝ), (68882647/125000000 : ℝ)] ![(42910050257851/100000000000000 : ℝ), (2930894865521/25000000000000 : ℝ), (2835398141973/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056825849/2000000000 : ℝ)|^8323 ≤ (42910050257851/100000000000000 : ℝ)^6275
        have hw : |(1056825849/2000000000 : ℝ)|=(1056825849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1986698839/10000000000 : ℝ)|^8323 ≤ (2930894865521/25000000000000 : ℝ)^6275
        have hw : |(-1986698839/10000000000 : ℝ)|=(1986698839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68882647/125000000 : ℝ)|^8323 ≤ (2835398141973/6250000000000 : ℝ)^6275
        have hw : |(68882647/125000000 : ℝ)|=(68882647/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s2_6 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5284127953/10000000000 : ℝ)*x 0 + (5510611617/10000000000 : ℝ)*x 1 + (-397340163/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284127953/10000000000 : ℝ)^8323 ≤ (1340938635683/3125000000000 : ℝ)^6275 := by
    have hnat : (5284127953 : ℕ)^8323*3125000000000^6275 ≤ 1340938635683^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284127953 10000000000 1340938635683 3125000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5510611617/10000000000 : ℝ)^8323 ≤ (5670796088761/12500000000000 : ℝ)^6275 := by
    have hnat : (5510611617 : ℕ)^8323*12500000000000^6275 ≤ 5670796088761^6275*10000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510611617 10000000000 5670796088761 12500000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397340163/2000000000 : ℝ)^8323 ≤ (2930898732051/25000000000000 : ℝ)^6275 := by
    have hnat : (397340163 : ℕ)^8323*25000000000000^6275 ≤ 2930898732051^6275*2000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397340163 2000000000 2930898732051 25000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284127953/10000000000 : ℝ), (5510611617/10000000000 : ℝ), (-397340163/2000000000 : ℝ)] ![(1340938635683/3125000000000 : ℝ), (5670796088761/12500000000000 : ℝ), (2930898732051/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284127953/10000000000 : ℝ)|^8323 ≤ (1340938635683/3125000000000 : ℝ)^6275
        have hw : |(5284127953/10000000000 : ℝ)|=(5284127953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5510611617/10000000000 : ℝ)|^8323 ≤ (5670796088761/12500000000000 : ℝ)^6275
        have hw : |(5510611617/10000000000 : ℝ)|=(5510611617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-397340163/2000000000 : ℝ)|^8323 ≤ (2930898732051/25000000000000 : ℝ)^6275
        have hw : |(-397340163/2000000000 : ℝ)|=(397340163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1130_s2_7 (p : ℝ) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177797727/5000000000 : ℝ)*x 0 + (943600167/2000000000 : ℝ)*x 1 + (804259559/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177797727/5000000000 : ℝ)^8323 ≤ (8301983459979/25000000000000 : ℝ)^6275 := by
    have hnat : (2177797727 : ℕ)^8323*25000000000000^6275 ≤ 8301983459979^6275*5000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177797727 5000000000 8301983459979 25000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (943600167/2000000000 : ℝ)^8323 ≤ (36921636944883/100000000000000 : ℝ)^6275 := by
    have hnat : (943600167 : ℕ)^8323*100000000000000^6275 ≤ 36921636944883^6275*2000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943600167 2000000000 36921636944883 100000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (804259559/2000000000 : ℝ)^8323 ≤ (14935214601451/50000000000000 : ℝ)^6275 := by
    have hnat : (804259559 : ℕ)^8323*50000000000000^6275 ≤ 14935214601451^6275*2000000000^8323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804259559 2000000000 14935214601451 50000000000000 8323 6275 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8323/2048 : ℝ)) 8323 6275 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177797727/5000000000 : ℝ), (943600167/2000000000 : ℝ), (804259559/2000000000 : ℝ)] ![(8301983459979/25000000000000 : ℝ), (36921636944883/100000000000000 : ℝ), (14935214601451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177797727/5000000000 : ℝ)|^8323 ≤ (8301983459979/25000000000000 : ℝ)^6275
        have hw : |(2177797727/5000000000 : ℝ)|=(2177797727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(943600167/2000000000 : ℝ)|^8323 ≤ (36921636944883/100000000000000 : ℝ)^6275
        have hw : |(943600167/2000000000 : ℝ)|=(943600167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(804259559/2000000000 : ℝ)|^8323 ≤ (14935214601451/50000000000000 : ℝ)^6275
        have hw : |(804259559/2000000000 : ℝ)|=(804259559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1130_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5123/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2791/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1803/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16539/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5123/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2791/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5123/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2791/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5123/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2791/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5123/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2791/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5123/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2791/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5123/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2791/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2791/50000 : ℝ) ^ (4161/1024 : ℝ) ≤ (808369380802427/100000000000000000000 : ℝ) := by
    have hpowers : (2791/50000 : ℝ)^4161 ≤ (808369380802427/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2791 : ℕ)^4161*100000000000000000000^1024 ≤ 808369380802427^1024*50000^4161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2791 50000 808369380802427 100000000000000000000 4161 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2791/50000 : ℝ)) (X := (808369380802427/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5123/25000 : ℝ) ^ (4161/1024 : ℝ) ≤ (79727681326100891/50000000000000000000 : ℝ) := by
    have hpowers : (5123/25000 : ℝ)^4161 ≤ (79727681326100891/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5123 : ℕ)^4161*50000000000000000000^1024 ≤ 79727681326100891^1024*25000^4161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5123 25000 79727681326100891 50000000000000000000 4161 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5123/25000 : ℝ)) (X := (79727681326100891/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000808369380802427/50000000000000000000 : ℝ) ≤ (2500009946709941/2500000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (50000808369380802427/50000000000000000000 : ℝ)^1024 ≤ (2500009946709941/2500000000000000 : ℝ)^4161 := by
      have hnat : (50000808369380802427 : ℕ)^1024*2500000000000000^4161 ≤ 2500009946709941^4161*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000808369380802427 50000000000000000000 2500009946709941 2500000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500009946709941/2500000000000000 : ℝ)) (X := (50000808369380802427/50000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100160263732033004209/100000000000000000000 : ℝ) ≤ (10003941624909503/10000000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (100160263732033004209/100000000000000000000 : ℝ)^1024 ≤ (10003941624909503/10000000000000000 : ℝ)^4161 := by
      have hnat : (100160263732033004209 : ℕ)^1024*10000000000000000^4161 ≤ 10003941624909503^4161*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100160263732033004209 100000000000000000000 10003941624909503 10000000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003941624909503/10000000000000000 : ℝ)) (X := (100160263732033004209/100000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25079727681326100891/25000000000000000000 : ℝ) ≤ (5003921731489621/5000000000000000 : ℝ) ^ (4161/1024 : ℝ) := by
    have hpowers : (25079727681326100891/25000000000000000000 : ℝ)^1024 ≤ (5003921731489621/5000000000000000 : ℝ)^4161 := by
      have hnat : (25079727681326100891 : ℕ)^1024*5000000000000000^4161 ≤ 5003921731489621^4161*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25079727681326100891 25000000000000000000 5003921731489621 5000000000000000 1024 4161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003921731489621/5000000000000000 : ℝ)) (X := (25079727681326100891/25000000000000000000 : ℝ)) (by norm_num) 4161 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(808369380802427/100000000000000000000 : ℝ) ≤ ((12421419425130859587/12425000000000000000 : ℝ)+2*(1300612689913/497000000000000 : ℝ)*(2791/50000 : ℝ))^(4161/1024 : ℝ) := by
    rw [show (12421419425130859587/12425000000000000000 : ℝ)+2*(1300612689913/497000000000000 : ℝ)*(2791/50000 : ℝ)=(2500009946709941/2500000000000000 : ℝ) by norm_num, show 1+2*(808369380802427/100000000000000000000 : ℝ)=(50000808369380802427/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(79727681326100891/50000000000000000000 : ℝ)+(808369380802427/100000000000000000000 : ℝ) ≤ ((12421419425130859587/12425000000000000000 : ℝ)+(1300612689913/497000000000000 : ℝ)*((5123/25000 : ℝ)+(2791/50000 : ℝ)))^(4161/1024 : ℝ) := by
    rw [show (12421419425130859587/12425000000000000000 : ℝ)+(1300612689913/497000000000000 : ℝ)*((5123/25000 : ℝ)+(2791/50000 : ℝ))=(10003941624909503/10000000000000000 : ℝ) by norm_num, show 1+(79727681326100891/50000000000000000000 : ℝ)+(808369380802427/100000000000000000000 : ℝ)=(100160263732033004209/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(79727681326100891/50000000000000000000 : ℝ) ≤ ((12421419425130859587/12425000000000000000 : ℝ)+2*(1300612689913/497000000000000 : ℝ)*(5123/25000 : ℝ))^(4161/1024 : ℝ) := by
    rw [show (12421419425130859587/12425000000000000000 : ℝ)+2*(1300612689913/497000000000000 : ℝ)*(5123/25000 : ℝ)=(5003921731489621/5000000000000000 : ℝ) by norm_num, show 1+2*(79727681326100891/50000000000000000000 : ℝ)=(25079727681326100891/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12421419425130859587/12425000000000000000 : ℝ)*(X 1 0+X 2 0)+(1300612689913/497000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (2791/50000 : ℝ)) (hi := (5123/25000 : ℝ)) (c := (12421419425130859587/12425000000000000000 : ℝ)) (alpha := (1300612689913/497000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12421419425130859587/12425000000000000000 : ℝ)*(X 0 1+X 2 1)+(1300612689913/497000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (2791/50000 : ℝ)) (hi := (5123/25000 : ℝ)) (c := (12421419425130859587/12425000000000000000 : ℝ)) (alpha := (1300612689913/497000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12421419425130859587/12425000000000000000 : ℝ)*(X 0 2+X 1 2)+(1300612689913/497000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4161/1024 : ℝ)) (lo := (2791/50000 : ℝ)) (hi := (5123/25000 : ℝ)) (c := (12421419425130859587/12425000000000000000 : ℝ)) (alpha := (1300612689913/497000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2155024907/10000000000 : ℝ)*X 0 0+(220524479/400000000 : ℝ)*X 0 1+(5157114271/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5374382721/10000000000 : ℝ)*X 1 0+(-2340195817/10000000000 : ℝ)*X 1 1+(2578557993/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((671797831/1250000000 : ℝ)*X 2 0+(1031423199/2000000000 : ℝ)*X 2 1+(-1170097951/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088846399/2500000000 : ℝ)*X 0 0+(1004083973/2500000000 : ℝ)*X 0 1+(1180728321/2500000000 : ℝ)*X 0 2+(1088846399/2500000000 : ℝ)*X 1 0+(1004083973/2500000000 : ℝ)*X 1 1+(1180728321/2500000000 : ℝ)*X 1 2+(1088846399/2500000000 : ℝ)*X 2 0+(1004083973/2500000000 : ℝ)*X 2 1+(1180728321/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2155130919/10000000000 : ℝ)*X 0 0+(257979501/500000000 : ℝ)*X 0 1+(5510611183/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1056825849/2000000000 : ℝ)*X 1 0+(-1986698839/10000000000 : ℝ)*X 1 1+(68882647/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5284127953/10000000000 : ℝ)*X 2 0+(5510611617/10000000000 : ℝ)*X 2 1+(-397340163/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177797727/5000000000 : ℝ)*X 0 0+(943600167/2000000000 : ℝ)*X 0 1+(804259559/2000000000 : ℝ)*X 0 2+(2177797727/5000000000 : ℝ)*X 1 0+(943600167/2000000000 : ℝ)*X 1 1+(804259559/2000000000 : ℝ)*X 1 2+(2177797727/5000000000 : ℝ)*X 2 0+(943600167/2000000000 : ℝ)*X 2 1+(804259559/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1130_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (263332974923110688796511977/22187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (305224929/20000000000000 : ℝ)*(base19) + (306093301/25000000000000 : ℝ)*(base23) + (342566699/100000000000000 : ℝ)*(upper3) + (141666647/100000000000000 : ℝ)*(upper4) + (39806653/50000000000000 : ℝ)*(upper5) + (1056087862996599/50000000000000 : ℝ)*(major0) + (1056087862996599/50000000000000 : ℝ)*(major1) + (1056087862996599/50000000000000 : ℝ)*(major2) + (280903473094443/10000000000000 : ℝ)*(sp0) + (280905805005757/10000000000000 : ℝ)*(sp1) + (2809058351809011/100000000000000 : ℝ)*(sp2) + (1415281042075823/100000000000000 : ℝ)*(sp3) + (4969047557/20000000000000 : ℝ)*(sp4) + (2087622147/20000000000000 : ℝ)*(sp7) + (707645740093279/50000000000000 : ℝ)*(f.failure) + (351132447022777/12500000000000 : ℝ)*(f.sum) + (9107824913181/6212500000000000000000000000 : ℝ)*base65 + (2333643885015969613/621250000000000000000000000000000 : ℝ)*base67 + (6192586467667780387/621250000000000000000000000000000 : ℝ)*base70 + (2788210971695280387/621250000000000000000000000000000 : ℝ)*base72 + (1646926721241/388281250000000000000000000 : ℝ)*base73 + (3018746850161530387/621250000000000000000000000000000 : ℝ)*base76 + (3325712221102780387/621250000000000000000000000000000 : ℝ)*base78 + (2454811951877780387/621250000000000000000000000000000 : ℝ)*base80 + (3421828049561/1553125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3166933/5000000000000000000000 : ℝ)*base89 + (3166933/5000000000000000000000 : ℝ)*base91 + (3166933/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33078429938390800853283/3106250000000000000000000000 : ℝ) := by norm_num
    linear_combination (4880651/250000000000 : ℝ)*(base19) + (712557083/50000000000000 : ℝ)*(base23) + (233083227/100000000000000 : ℝ)*(upper2) + (134338763/100000000000000 : ℝ)*(upper3) + (60023399/20000000000000 : ℝ)*(upper5) + (1071038977944837/50000000000000 : ℝ)*(major0) + (1071038977944837/50000000000000 : ℝ)*(major1) + (1071038977944837/50000000000000 : ℝ)*(major2) + (25643420649/100000000000000 : ℝ)*(sp1) + (9736338773/100000000000000 : ℝ)*(sp2) + (1424413844587589/50000000000000 : ℝ)*(sp4) + (284880009349413/10000000000000 : ℝ)*(sp5) + (2225637912283/78125000000 : ℝ)*(sp6) + (717663933818889/50000000000000 : ℝ)*(sp7) + (717663933818889/50000000000000 : ℝ)*(f.failure) + (1424413844587589/50000000000000 : ℝ)*(f.sum) + (7883532598569/12425000000000000000000000000 : ℝ)*base66 + (189638866329372681/621250000000000000000000000000000 : ℝ)*base68 + (4969937500773127319/621250000000000000000000000000000 : ℝ)*base69 + (3202969001450622681/621250000000000000000000000000000 : ℝ)*base72 + (6397873283103/6212500000000000000000000000 : ℝ)*base73 + (3095906968798127319/621250000000000000000000000000000 : ℝ)*base75 + (6045528100156872681/621250000000000000000000000000000 : ℝ)*base78 + (1779902146751877319/621250000000000000000000000000000 : ℝ)*base79 + (50391791953981/12425000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (20085597/5000000000000000000000 : ℝ)*base90 + (20085597/5000000000000000000000 : ℝ)*base92 + (20085597/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1130_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5123/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2791/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1803/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16539/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1130_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1130_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1803/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16539/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1130_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1130_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1130_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4161/1024 : ℝ) ≤ p) (hpb : p ≤ (8323/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149239627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1803/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16539/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1130_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
