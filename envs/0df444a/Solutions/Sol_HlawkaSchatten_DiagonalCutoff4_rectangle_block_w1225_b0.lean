-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1225_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:12:27.395558+00:00
-- url     : https://prove2.me/submissions/377af6a7-b9ec-47df-abfe-697141fdc1c3

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
theorem support_rectangle_w1225_s0_0 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-116613557/625000000 : ℝ)*x 0 + (3017672497/5000000000 : ℝ)*x 1 + (4790878949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (116613557/625000000 : ℝ)^4209 ≤ (5437737896091/50000000000000 : ℝ)^3185 := by
    have hnat : (116613557 : ℕ)^4209*50000000000000^3185 ≤ 5437737896091^3185*625000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116613557 625000000 5437737896091 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3017672497/5000000000 : ℝ)^4209 ≤ (6413665257983/12500000000000 : ℝ)^3185 := by
    have hnat : (3017672497 : ℕ)^4209*12500000000000^3185 ≤ 6413665257983^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3017672497 5000000000 6413665257983 12500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4790878949/10000000000 : ℝ)^4209 ≤ (37815202125949/100000000000000 : ℝ)^3185 := by
    have hnat : (4790878949 : ℕ)^4209*100000000000000^3185 ≤ 37815202125949^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4790878949 10000000000 37815202125949 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-116613557/625000000 : ℝ), (3017672497/5000000000 : ℝ), (4790878949/10000000000 : ℝ)] ![(5437737896091/50000000000000 : ℝ), (6413665257983/12500000000000 : ℝ), (37815202125949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-116613557/625000000 : ℝ)|^4209 ≤ (5437737896091/50000000000000 : ℝ)^3185
        have hw : |(-116613557/625000000 : ℝ)|=(116613557/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3017672497/5000000000 : ℝ)|^4209 ≤ (6413665257983/12500000000000 : ℝ)^3185
        have hw : |(3017672497/5000000000 : ℝ)|=(3017672497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4790878949/10000000000 : ℝ)|^4209 ≤ (37815202125949/100000000000000 : ℝ)^3185
        have hw : |(4790878949/10000000000 : ℝ)|=(4790878949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s0_1 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5512117249/10000000000 : ℝ)*x 0 + (-2577708871/10000000000 : ℝ)*x 1 + (958175781/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5512117249/10000000000 : ℝ)^4209 ≤ (45514575881979/100000000000000 : ℝ)^3185 := by
    have hnat : (5512117249 : ℕ)^4209*100000000000000^3185 ≤ 45514575881979^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512117249 10000000000 45514575881979 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2577708871/10000000000 : ℝ)^4209 ≤ (8335111218913/50000000000000 : ℝ)^3185 := by
    have hnat : (2577708871 : ℕ)^4209*50000000000000^3185 ≤ 8335111218913^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2577708871 10000000000 8335111218913 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (958175781/2000000000 : ℝ)^4209 ≤ (3781520166699/10000000000000 : ℝ)^3185 := by
    have hnat : (958175781 : ℕ)^4209*10000000000000^3185 ≤ 3781520166699^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958175781 2000000000 3781520166699 10000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5512117249/10000000000 : ℝ), (-2577708871/10000000000 : ℝ), (958175781/2000000000 : ℝ)] ![(45514575881979/100000000000000 : ℝ), (8335111218913/50000000000000 : ℝ), (3781520166699/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5512117249/10000000000 : ℝ)|^4209 ≤ (45514575881979/100000000000000 : ℝ)^3185
        have hw : |(5512117249/10000000000 : ℝ)|=(5512117249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2577708871/10000000000 : ℝ)|^4209 ≤ (8335111218913/50000000000000 : ℝ)^3185
        have hw : |(-2577708871/10000000000 : ℝ)|=(2577708871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(958175781/2000000000 : ℝ)|^4209 ≤ (3781520166699/10000000000000 : ℝ)^3185
        have hw : |(958175781/2000000000 : ℝ)|=(958175781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s0_2 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (689014651/1250000000 : ℝ)*x 0 + (958175791/2000000000 : ℝ)*x 1 + (-1288854431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689014651/1250000000 : ℝ)^4209 ≤ (4551457543459/10000000000000 : ℝ)^3185 := by
    have hnat : (689014651 : ℕ)^4209*10000000000000^3185 ≤ 4551457543459^3185*1250000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689014651 1250000000 4551457543459 10000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (958175791/2000000000 : ℝ)^4209 ≤ (18907601094267/50000000000000 : ℝ)^3185 := by
    have hnat : (958175791 : ℕ)^4209*50000000000000^3185 ≤ 18907601094267^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958175791 2000000000 18907601094267 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1288854431/5000000000 : ℝ)^4209 ≤ (16670222360909/100000000000000 : ℝ)^3185 := by
    have hnat : (1288854431 : ℕ)^4209*100000000000000^3185 ≤ 16670222360909^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288854431 5000000000 16670222360909 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(689014651/1250000000 : ℝ), (958175791/2000000000 : ℝ), (-1288854431/5000000000 : ℝ)] ![(4551457543459/10000000000000 : ℝ), (18907601094267/50000000000000 : ℝ), (16670222360909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(689014651/1250000000 : ℝ)|^4209 ≤ (4551457543459/10000000000000 : ℝ)^3185
        have hw : |(689014651/1250000000 : ℝ)|=(689014651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(958175791/2000000000 : ℝ)|^4209 ≤ (18907601094267/50000000000000 : ℝ)^3185
        have hw : |(958175791/2000000000 : ℝ)|=(958175791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1288854431/5000000000 : ℝ)|^4209 ≤ (16670222360909/100000000000000 : ℝ)^3185
        have hw : |(-1288854431/5000000000 : ℝ)|=(1288854431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s0_3 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4194360003/10000000000 : ℝ)*x 0 + (1558770569/5000000000 : ℝ)*x 1 + (352109009/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4194360003/10000000000 : ℝ)^4209 ≤ (15860616550809/50000000000000 : ℝ)^3185 := by
    have hnat : (4194360003 : ℕ)^4209*50000000000000^3185 ≤ 15860616550809^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4194360003 10000000000 15860616550809 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1558770569/5000000000 : ℝ)^4209 ≤ (21432322574149/100000000000000 : ℝ)^3185 := by
    have hnat : (1558770569 : ℕ)^4209*100000000000000^3185 ≤ 21432322574149^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1558770569 5000000000 21432322574149 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352109009/625000000 : ℝ)^4209 ≤ (46846444315617/100000000000000 : ℝ)^3185 := by
    have hnat : (352109009 : ℕ)^4209*100000000000000^3185 ≤ 46846444315617^3185*625000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352109009 625000000 46846444315617 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4194360003/10000000000 : ℝ), (1558770569/5000000000 : ℝ), (352109009/625000000 : ℝ)] ![(15860616550809/50000000000000 : ℝ), (21432322574149/100000000000000 : ℝ), (46846444315617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4194360003/10000000000 : ℝ)|^4209 ≤ (15860616550809/50000000000000 : ℝ)^3185
        have hw : |(4194360003/10000000000 : ℝ)|=(4194360003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1558770569/5000000000 : ℝ)|^4209 ≤ (21432322574149/100000000000000 : ℝ)^3185
        have hw : |(1558770569/5000000000 : ℝ)|=(1558770569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(352109009/625000000 : ℝ)|^4209 ≤ (46846444315617/100000000000000 : ℝ)^3185
        have hw : |(352109009/625000000 : ℝ)|=(352109009/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s0_4 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-18707227/100000000 : ℝ)*x 0 + (2411467843/5000000000 : ℝ)*x 1 + (750269467/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18707227/100000000 : ℝ)^4209 ≤ (10913280067853/100000000000000 : ℝ)^3185 := by
    have hnat : (18707227 : ℕ)^4209*100000000000000^3185 ≤ 10913280067853^3185*100000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18707227 100000000 10913280067853 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2411467843/5000000000 : ℝ)^4209 ≤ (38149941051997/100000000000000 : ℝ)^3185 := by
    have hnat : (2411467843 : ℕ)^4209*100000000000000^3185 ≤ 38149941051997^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2411467843 5000000000 38149941051997 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (750269467/1250000000 : ℝ)^4209 ≤ (50936778864513/100000000000000 : ℝ)^3185 := by
    have hnat : (750269467 : ℕ)^4209*100000000000000^3185 ≤ 50936778864513^3185*1250000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750269467 1250000000 50936778864513 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18707227/100000000 : ℝ), (2411467843/5000000000 : ℝ), (750269467/1250000000 : ℝ)] ![(10913280067853/100000000000000 : ℝ), (38149941051997/100000000000000 : ℝ), (50936778864513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18707227/100000000 : ℝ)|^4209 ≤ (10913280067853/100000000000000 : ℝ)^3185
        have hw : |(-18707227/100000000 : ℝ)|=(18707227/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2411467843/5000000000 : ℝ)|^4209 ≤ (38149941051997/100000000000000 : ℝ)^3185
        have hw : |(2411467843/5000000000 : ℝ)|=(2411467843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(750269467/1250000000 : ℝ)|^4209 ≤ (50936778864513/100000000000000 : ℝ)^3185
        have hw : |(750269467/1250000000 : ℝ)|=(750269467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s0_5 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5173588487/10000000000 : ℝ)*x 0 + (-341608107/2500000000 : ℝ)*x 1 + (6002155659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173588487/10000000000 : ℝ)^4209 ≤ (261609774737/625000000000 : ℝ)^3185 := by
    have hnat : (5173588487 : ℕ)^4209*625000000000^3185 ≤ 261609774737^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173588487 10000000000 261609774737 625000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341608107/2500000000 : ℝ)^4209 ≤ (7205658025731/100000000000000 : ℝ)^3185 := by
    have hnat : (341608107 : ℕ)^4209*100000000000000^3185 ≤ 7205658025731^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341608107 2500000000 7205658025731 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6002155659/10000000000 : ℝ)^4209 ≤ (50936778000969/100000000000000 : ℝ)^3185 := by
    have hnat : (6002155659 : ℕ)^4209*100000000000000^3185 ≤ 50936778000969^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6002155659 10000000000 50936778000969 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173588487/10000000000 : ℝ), (-341608107/2500000000 : ℝ), (6002155659/10000000000 : ℝ)] ![(261609774737/625000000000 : ℝ), (7205658025731/100000000000000 : ℝ), (50936778000969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173588487/10000000000 : ℝ)|^4209 ≤ (261609774737/625000000000 : ℝ)^3185
        have hw : |(5173588487/10000000000 : ℝ)|=(5173588487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-341608107/2500000000 : ℝ)|^4209 ≤ (7205658025731/100000000000000 : ℝ)^3185
        have hw : |(-341608107/2500000000 : ℝ)|=(341608107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6002155659/10000000000 : ℝ)|^4209 ≤ (50936778000969/100000000000000 : ℝ)^3185
        have hw : |(6002155659/10000000000 : ℝ)|=(6002155659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s0_6 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5173588461/10000000000 : ℝ)*x 0 + (3001077869/5000000000 : ℝ)*x 1 + (-68321617/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173588461/10000000000 : ℝ)^4209 ≤ (10464390919983/25000000000000 : ℝ)^3185 := by
    have hnat : (5173588461 : ℕ)^4209*25000000000000^3185 ≤ 10464390919983^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173588461 10000000000 10464390919983 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3001077869/5000000000 : ℝ)^4209 ≤ (50936778886943/100000000000000 : ℝ)^3185 := by
    have hnat : (3001077869 : ℕ)^4209*100000000000000^3185 ≤ 50936778886943^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3001077869 5000000000 50936778886943 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68321617/500000000 : ℝ)^4209 ≤ (7205657412481/100000000000000 : ℝ)^3185 := by
    have hnat : (68321617 : ℕ)^4209*100000000000000^3185 ≤ 7205657412481^3185*500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68321617 500000000 7205657412481 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173588461/10000000000 : ℝ), (3001077869/5000000000 : ℝ), (-68321617/500000000 : ℝ)] ![(10464390919983/25000000000000 : ℝ), (50936778886943/100000000000000 : ℝ), (7205657412481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173588461/10000000000 : ℝ)|^4209 ≤ (10464390919983/25000000000000 : ℝ)^3185
        have hw : |(5173588461/10000000000 : ℝ)|=(5173588461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3001077869/5000000000 : ℝ)|^4209 ≤ (50936778886943/100000000000000 : ℝ)^3185
        have hw : |(3001077869/5000000000 : ℝ)|=(3001077869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-68321617/500000000 : ℝ)|^4209 ≤ (7205657412481/100000000000000 : ℝ)^3185
        have hw : |(-68321617/500000000 : ℝ)|=(68321617/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s0_7 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2102139403/5000000000 : ℝ)*x 0 + (1113785549/2000000000 : ℝ)*x 1 + (3184647407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102139403/5000000000 : ℝ)^4209 ≤ (6364080518741/20000000000000 : ℝ)^3185 := by
    have hnat : (2102139403 : ℕ)^4209*20000000000000^3185 ≤ 6364080518741^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102139403 5000000000 6364080518741 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1113785549/2000000000 : ℝ)^4209 ≤ (5766939085527/12500000000000 : ℝ)^3185 := by
    have hnat : (1113785549 : ℕ)^4209*12500000000000^3185 ≤ 5766939085527^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113785549 2000000000 5766939085527 12500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3184647407/10000000000 : ℝ)^4209 ≤ (2204408470243/10000000000000 : ℝ)^3185 := by
    have hnat : (3184647407 : ℕ)^4209*10000000000000^3185 ≤ 2204408470243^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3184647407 10000000000 2204408470243 10000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2102139403/5000000000 : ℝ), (1113785549/2000000000 : ℝ), (3184647407/10000000000 : ℝ)] ![(6364080518741/20000000000000 : ℝ), (5766939085527/12500000000000 : ℝ), (2204408470243/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2102139403/5000000000 : ℝ)|^4209 ≤ (6364080518741/20000000000000 : ℝ)^3185
        have hw : |(2102139403/5000000000 : ℝ)|=(2102139403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1113785549/2000000000 : ℝ)|^4209 ≤ (5766939085527/12500000000000 : ℝ)^3185
        have hw : |(1113785549/2000000000 : ℝ)|=(1113785549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3184647407/10000000000 : ℝ)|^4209 ≤ (2204408470243/10000000000000 : ℝ)^3185
        have hw : |(3184647407/10000000000 : ℝ)|=(3184647407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1225_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3/400 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11/40 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8417/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8417 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8417*1^2048 ≤ 0^2048*1^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8417/2048 : ℝ) ≤ (1157419978506678971/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8417 ≤ (1157419978506678971/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8417*50000000000000000000^2048 ≤ 1157419978506678971^2048*5^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1157419978506678971 50000000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1157419978506678971/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8417 := by
      have hnat : (1 : ℕ)^2048*1^8417 ≤ 1^8417*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51157419978506678971/50000000000000000000 : ℝ) ≤ (1256979663695697/1250000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (51157419978506678971/50000000000000000000 : ℝ)^2048 ≤ (1256979663695697/1250000000000000 : ℝ)^8417 := by
      have hnat : (51157419978506678971 : ℕ)^2048*1250000000000000^8417 ≤ 1256979663695697^8417*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51157419978506678971 50000000000000000000 1256979663695697 1250000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1256979663695697/1250000000000000 : ℝ)) (X := (51157419978506678971/50000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26157419978506678971/25000000000000000000 : ℝ) ≤ (631979663695697/625000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (26157419978506678971/25000000000000000000 : ℝ)^2048 ≤ (631979663695697/625000000000000 : ℝ)^8417 := by
      have hnat : (26157419978506678971 : ℕ)^2048*625000000000000^8417 ≤ 631979663695697^8417*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26157419978506678971 25000000000000000000 631979663695697 625000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (631979663695697/625000000000000 : ℝ)) (X := (26157419978506678971/25000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(6979663695697/500000000000000 : ℝ)*(0 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(6979663695697/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1157419978506678971/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(6979663695697/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8417/2048 : ℝ) := by
    rw [show (1 : ℝ)+(6979663695697/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1256979663695697/1250000000000000 : ℝ) by norm_num, show 1+(1157419978506678971/50000000000000000000 : ℝ)+(0 : ℝ)=(51157419978506678971/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1157419978506678971/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(6979663695697/500000000000000 : ℝ)*(2/5 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(6979663695697/500000000000000 : ℝ)*(2/5 : ℝ)=(631979663695697/625000000000000 : ℝ) by norm_num, show 1+2*(1157419978506678971/50000000000000000000 : ℝ)=(26157419978506678971/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(6979663695697/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6979663695697/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(6979663695697/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6979663695697/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(6979663695697/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6979663695697/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-116613557/625000000 : ℝ)*X 0 0+(3017672497/5000000000 : ℝ)*X 0 1+(4790878949/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5512117249/10000000000 : ℝ)*X 1 0+(-2577708871/10000000000 : ℝ)*X 1 1+(958175781/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((689014651/1250000000 : ℝ)*X 2 0+(958175791/2000000000 : ℝ)*X 2 1+(-1288854431/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4194360003/10000000000 : ℝ)*X 0 0+(1558770569/5000000000 : ℝ)*X 0 1+(352109009/625000000 : ℝ)*X 0 2+(4194360003/10000000000 : ℝ)*X 1 0+(1558770569/5000000000 : ℝ)*X 1 1+(352109009/625000000 : ℝ)*X 1 2+(4194360003/10000000000 : ℝ)*X 2 0+(1558770569/5000000000 : ℝ)*X 2 1+(352109009/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-18707227/100000000 : ℝ)*X 0 0+(2411467843/5000000000 : ℝ)*X 0 1+(750269467/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5173588487/10000000000 : ℝ)*X 1 0+(-341608107/2500000000 : ℝ)*X 1 1+(6002155659/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5173588461/10000000000 : ℝ)*X 2 0+(3001077869/5000000000 : ℝ)*X 2 1+(-68321617/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2102139403/5000000000 : ℝ)*X 0 0+(1113785549/2000000000 : ℝ)*X 0 1+(3184647407/10000000000 : ℝ)*X 0 2+(2102139403/5000000000 : ℝ)*X 1 0+(1113785549/2000000000 : ℝ)*X 1 1+(3184647407/10000000000 : ℝ)*X 1 2+(2102139403/5000000000 : ℝ)*X 2 0+(1113785549/2000000000 : ℝ)*X 2 1+(3184647407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8273683458431076954351/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77447549/100000000000000 : ℝ)*(base1) + (1616403251/100000000000000 : ℝ)*(base19) + (1500315737/100000000000000 : ℝ)*(base23) + (110110471/100000000000000 : ℝ)*(base24) + (366890219/100000000000000 : ℝ)*(upper3) + (60049771276713/10000000000000 : ℝ)*(major0) + (60049771276713/10000000000000 : ℝ)*(major1) + (60049771276713/10000000000000 : ℝ)*(major2) + (401781475120647/50000000000000 : ℝ)*(sp0) + (803564843299259/100000000000000 : ℝ)*(sp1) + (401782424638151/50000000000000 : ℝ)*(sp2) + (397425858215027/100000000000000 : ℝ)*(sp3) + (717381753/20000000000000 : ℝ)*(sp4) + (702384401/25000000000000 : ℝ)*(sp7) + (397428745200181/100000000000000 : ℝ)*(f.failure) + (803566459702511/100000000000000 : ℝ)*(f.sum) + (4617723711461/2500000000000000000000000000 : ℝ)*base65 + (35023745743961/5000000000000000000000000000 : ℝ)*base67 + (50464660593961/5000000000000000000000000000 : ℝ)*base69 + (37303592423961/5000000000000000000000000000 : ℝ)*base71 + (5648921611461/2500000000000000000000000000 : ℝ)*base73 + (38981233848961/5000000000000000000000000000 : ℝ)*base75 + (22313660798961/5000000000000000000000000000 : ℝ)*base77 + (23761973823961/5000000000000000000000000000 : ℝ)*base79 + (6841473423961/2500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (6680063/2500000000000000000000 : ℝ)*base89 + (6680063/2500000000000000000000 : ℝ)*base91 + (6680063/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29606614527727824117033/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49848047/100000000000000 : ℝ)*(base1) + (343066133/25000000000000 : ℝ)*(base19) + (341703471/25000000000000 : ℝ)*(base23) + (153932891/100000000000000 : ℝ)*(upper3) + (7199959/4000000000000 : ℝ)*(upper5) + (126743220283879/20000000000000 : ℝ)*(major0) + (126743220283879/20000000000000 : ℝ)*(major1) + (126743220283879/20000000000000 : ℝ)*(major2) + (2957439683/100000000000000 : ℝ)*(sp1) + (2939270097/100000000000000 : ℝ)*(sp2) + (424009154801107/50000000000000 : ℝ)*(sp4) + (26500435314061/3125000000000 : ℝ)*(sp5) + (848013953670187/100000000000000 : ℝ)*(sp6) + (20970684792957/5000000000000 : ℝ)*(sp7) + (419413745707187/100000000000000 : ℝ)*(f.failure) + (848018259754167/100000000000000 : ℝ)*(f.sum) + (5057965568663/5000000000000000000000000000 : ℝ)*base65 + (50644129728663/10000000000000000000000000000 : ℝ)*base67 + (23108115928663/10000000000000000000000000000 : ℝ)*base69 + (49805795458663/10000000000000000000000000000 : ℝ)*base71 + (8031271013663/5000000000000000000000000000 : ℝ)*base73 + (53051456138663/10000000000000000000000000000 : ℝ)*base75 + (8276328538663/10000000000000000000000000000 : ℝ)*base77 + (4100698641337/10000000000000000000000000000 : ℝ)*base80 + (6020903161337/5000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (12715399/2500000000000000000000 : ℝ)*base90 + (12715399/2500000000000000000000 : ℝ)*base92 + (12715399/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1225_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3/400 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11/40 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1225_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1225_s1_0 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-516115959/2500000000 : ℝ)*x 0 + (5679896821/10000000000 : ℝ)*x 1 + (1003834087/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516115959/2500000000 : ℝ)^4209 ≤ (6215598938457/50000000000000 : ℝ)^3185 := by
    have hnat : (516115959 : ℕ)^4209*50000000000000^3185 ≤ 6215598938457^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516115959 2500000000 6215598938457 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5679896821/10000000000 : ℝ)^4209 ≤ (23677136016141/50000000000000 : ℝ)^3185 := by
    have hnat : (5679896821 : ℕ)^4209*50000000000000^3185 ≤ 23677136016141^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5679896821 10000000000 23677136016141 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003834087/2000000000 : ℝ)^4209 ≤ (78544004041/195312500000 : ℝ)^3185 := by
    have hnat : (1003834087 : ℕ)^4209*195312500000^3185 ≤ 78544004041^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003834087 2000000000 78544004041 195312500000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-516115959/2500000000 : ℝ), (5679896821/10000000000 : ℝ), (1003834087/2000000000 : ℝ)] ![(6215598938457/50000000000000 : ℝ), (23677136016141/50000000000000 : ℝ), (78544004041/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-516115959/2500000000 : ℝ)|^4209 ≤ (6215598938457/50000000000000 : ℝ)^3185
        have hw : |(-516115959/2500000000 : ℝ)|=(516115959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5679896821/10000000000 : ℝ)|^4209 ≤ (23677136016141/50000000000000 : ℝ)^3185
        have hw : |(5679896821/10000000000 : ℝ)|=(5679896821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1003834087/2000000000 : ℝ)|^4209 ≤ (78544004041/195312500000 : ℝ)^3185
        have hw : |(1003834087/2000000000 : ℝ)|=(1003834087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s1_1 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2707291503/5000000000 : ℝ)*x 0 + (-120977897/500000000 : ℝ)*x 1 + (5019170459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2707291503/5000000000 : ℝ)^4209 ≤ (44453328643199/100000000000000 : ℝ)^3185 := by
    have hnat : (2707291503 : ℕ)^4209*100000000000000^3185 ≤ 44453328643199^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707291503 5000000000 44453328643199 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (120977897/500000000 : ℝ)^4209 ≤ (3833035257573/25000000000000 : ℝ)^3185 := by
    have hnat : (120977897 : ℕ)^4209*25000000000000^3185 ≤ 3833035257573^3185*500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120977897 500000000 3833035257573 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5019170459/10000000000 : ℝ)^4209 ≤ (10053632580777/25000000000000 : ℝ)^3185 := by
    have hnat : (5019170459 : ℕ)^4209*25000000000000^3185 ≤ 10053632580777^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5019170459 10000000000 10053632580777 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2707291503/5000000000 : ℝ), (-120977897/500000000 : ℝ), (5019170459/10000000000 : ℝ)] ![(44453328643199/100000000000000 : ℝ), (3833035257573/25000000000000 : ℝ), (10053632580777/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2707291503/5000000000 : ℝ)|^4209 ≤ (44453328643199/100000000000000 : ℝ)^3185
        have hw : |(2707291503/5000000000 : ℝ)|=(2707291503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-120977897/500000000 : ℝ)|^4209 ≤ (3833035257573/25000000000000 : ℝ)^3185
        have hw : |(-120977897/500000000 : ℝ)|=(120977897/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5019170459/10000000000 : ℝ)|^4209 ≤ (10053632580777/25000000000000 : ℝ)^3185
        have hw : |(5019170459/10000000000 : ℝ)|=(5019170459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s1_2 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2707291523/5000000000 : ℝ)*x 0 + (5019170449/10000000000 : ℝ)*x 1 + (-24195579/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2707291523/5000000000 : ℝ)^4209 ≤ (22226664538589/50000000000000 : ℝ)^3185 := by
    have hnat : (2707291523 : ℕ)^4209*50000000000000^3185 ≤ 22226664538589^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707291523 5000000000 22226664538589 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5019170449/10000000000 : ℝ)^4209 ≤ (20107265108613/50000000000000 : ℝ)^3185 := by
    have hnat : (5019170449 : ℕ)^4209*50000000000000^3185 ≤ 20107265108613^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5019170449 10000000000 20107265108613 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24195579/100000000 : ℝ)^4209 ≤ (1533214069533/10000000000000 : ℝ)^3185 := by
    have hnat : (24195579 : ℕ)^4209*10000000000000^3185 ≤ 1533214069533^3185*100000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24195579 100000000 1533214069533 10000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2707291523/5000000000 : ℝ), (5019170449/10000000000 : ℝ), (-24195579/100000000 : ℝ)] ![(22226664538589/50000000000000 : ℝ), (20107265108613/50000000000000 : ℝ), (1533214069533/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2707291523/5000000000 : ℝ)|^4209 ≤ (22226664538589/50000000000000 : ℝ)^3185
        have hw : |(2707291523/5000000000 : ℝ)|=(2707291523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5019170449/10000000000 : ℝ)|^4209 ≤ (20107265108613/50000000000000 : ℝ)^3185
        have hw : |(5019170449/10000000000 : ℝ)|=(5019170449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-24195579/100000000 : ℝ)|^4209 ≤ (1533214069533/10000000000000 : ℝ)^3185
        have hw : |(-24195579/100000000 : ℝ)|=(24195579/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s1_3 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8620657/20000000 : ℝ)*x 0 + (369236577/1000000000 : ℝ)*x 1 + (628537277/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8620657/20000000 : ℝ)^4209 ≤ (3288538055879/10000000000000 : ℝ)^3185 := by
    have hnat : (8620657 : ℕ)^4209*10000000000000^3185 ≤ 3288538055879^3185*20000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8620657 20000000 3288538055879 10000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (369236577/1000000000 : ℝ)^4209 ≤ (13401707348671/50000000000000 : ℝ)^3185 := by
    have hnat : (369236577 : ℕ)^4209*50000000000000^3185 ≤ 13401707348671^3185*1000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369236577 1000000000 13401707348671 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (628537277/1250000000 : ℝ)^4209 ≤ (8062240945567/20000000000000 : ℝ)^3185 := by
    have hnat : (628537277 : ℕ)^4209*20000000000000^3185 ≤ 8062240945567^3185*1250000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628537277 1250000000 8062240945567 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8620657/20000000 : ℝ), (369236577/1000000000 : ℝ), (628537277/1250000000 : ℝ)] ![(3288538055879/10000000000000 : ℝ), (13401707348671/50000000000000 : ℝ), (8062240945567/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8620657/20000000 : ℝ)|^4209 ≤ (3288538055879/10000000000000 : ℝ)^3185
        have hw : |(8620657/20000000 : ℝ)|=(8620657/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(369236577/1000000000 : ℝ)|^4209 ≤ (13401707348671/50000000000000 : ℝ)^3185
        have hw : |(369236577/1000000000 : ℝ)|=(369236577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(628537277/1250000000 : ℝ)|^4209 ≤ (8062240945567/20000000000000 : ℝ)^3185
        have hw : |(628537277/1250000000 : ℝ)|=(628537277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s1_4 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-258144527/1250000000 : ℝ)*x 0 + (1005580913/2000000000 : ℝ)*x 1 + (88609351/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258144527/1250000000 : ℝ)^4209 ≤ (6218353884641/50000000000000 : ℝ)^3185 := by
    have hnat : (258144527 : ℕ)^4209*50000000000000^3185 ≤ 6218353884641^3185*1250000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258144527 1250000000 6218353884641 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005580913/2000000000 : ℝ)^4209 ≤ (5038379288073/12500000000000 : ℝ)^3185 := by
    have hnat : (1005580913 : ℕ)^4209*12500000000000^3185 ≤ 5038379288073^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005580913 2000000000 5038379288073 12500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88609351/156250000 : ℝ)^4209 ≤ (23628128960527/50000000000000 : ℝ)^3185 := by
    have hnat : (88609351 : ℕ)^4209*50000000000000^3185 ≤ 23628128960527^3185*156250000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88609351 156250000 23628128960527 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-258144527/1250000000 : ℝ), (1005580913/2000000000 : ℝ), (88609351/156250000 : ℝ)] ![(6218353884641/50000000000000 : ℝ), (5038379288073/12500000000000 : ℝ), (23628128960527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-258144527/1250000000 : ℝ)|^4209 ≤ (6218353884641/50000000000000 : ℝ)^3185
        have hw : |(-258144527/1250000000 : ℝ)|=(258144527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005580913/2000000000 : ℝ)|^4209 ≤ (5038379288073/12500000000000 : ℝ)^3185
        have hw : |(1005580913/2000000000 : ℝ)|=(1005580913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(88609351/156250000 : ℝ)|^4209 ≤ (23628128960527/50000000000000 : ℝ)^3185
        have hw : |(88609351/156250000 : ℝ)|=(88609351/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s1_5 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5244497973/10000000000 : ℝ)*x 0 + (-1767736327/10000000000 : ℝ)*x 1 + (708873891/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5244497973/10000000000 : ℝ)^4209 ≤ (4261738055993/10000000000000 : ℝ)^3185 := by
    have hnat : (5244497973 : ℕ)^4209*10000000000000^3185 ≤ 4261738055993^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244497973 10000000000 4261738055993 10000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1767736327/10000000000 : ℝ)^4209 ≤ (10126442295037/100000000000000 : ℝ)^3185 := by
    have hnat : (1767736327 : ℕ)^4209*100000000000000^3185 ≤ 10126442295037^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1767736327 10000000000 10126442295037 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (708873891/1250000000 : ℝ)^4209 ≤ (9451235427293/20000000000000 : ℝ)^3185 := by
    have hnat : (708873891 : ℕ)^4209*20000000000000^3185 ≤ 9451235427293^3185*1250000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708873891 1250000000 9451235427293 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5244497973/10000000000 : ℝ), (-1767736327/10000000000 : ℝ), (708873891/1250000000 : ℝ)] ![(4261738055993/10000000000000 : ℝ), (10126442295037/100000000000000 : ℝ), (9451235427293/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5244497973/10000000000 : ℝ)|^4209 ≤ (4261738055993/10000000000000 : ℝ)^3185
        have hw : |(5244497973/10000000000 : ℝ)|=(5244497973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1767736327/10000000000 : ℝ)|^4209 ≤ (10126442295037/100000000000000 : ℝ)^3185
        have hw : |(-1767736327/10000000000 : ℝ)|=(1767736327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(708873891/1250000000 : ℝ)|^4209 ≤ (9451235427293/20000000000000 : ℝ)^3185
        have hw : |(708873891/1250000000 : ℝ)|=(708873891/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s1_6 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (524449803/1000000000 : ℝ)*x 0 + (1417747913/2500000000 : ℝ)*x 1 + (-1767735483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524449803/1000000000 : ℝ)^4209 ≤ (42617381172037/100000000000000 : ℝ)^3185 := by
    have hnat : (524449803 : ℕ)^4209*100000000000000^3185 ≤ 42617381172037^3185*1000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524449803 1000000000 42617381172037 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1417747913/2500000000 : ℝ)^4209 ≤ (5907022863349/12500000000000 : ℝ)^3185 := by
    have hnat : (1417747913 : ℕ)^4209*12500000000000^3185 ≤ 5907022863349^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1417747913 2500000000 5907022863349 12500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1767735483/10000000000 : ℝ)^4209 ≤ (5063217952883/50000000000000 : ℝ)^3185 := by
    have hnat : (1767735483 : ℕ)^4209*50000000000000^3185 ≤ 5063217952883^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1767735483 10000000000 5063217952883 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524449803/1000000000 : ℝ), (1417747913/2500000000 : ℝ), (-1767735483/10000000000 : ℝ)] ![(42617381172037/100000000000000 : ℝ), (5907022863349/12500000000000 : ℝ), (5063217952883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524449803/1000000000 : ℝ)|^4209 ≤ (42617381172037/100000000000000 : ℝ)^3185
        have hw : |(524449803/1000000000 : ℝ)|=(524449803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1417747913/2500000000 : ℝ)|^4209 ≤ (5907022863349/12500000000000 : ℝ)^3185
        have hw : |(1417747913/2500000000 : ℝ)|=(1417747913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1767735483/10000000000 : ℝ)|^4209 ≤ (5063217952883/50000000000000 : ℝ)^3185
        have hw : |(-1767735483/10000000000 : ℝ)|=(1767735483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s1_7 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4311736101/10000000000 : ℝ)*x 0 + (626328919/1250000000 : ℝ)*x 1 + (115949129/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311736101/10000000000 : ℝ)^4209 ≤ (32899573236943/100000000000000 : ℝ)^3185 := by
    have hnat : (4311736101 : ℕ)^4209*100000000000000^3185 ≤ 32899573236943^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311736101 10000000000 32899573236943 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (626328919/1250000000 : ℝ)^4209 ≤ (20062070809177/50000000000000 : ℝ)^3185 := by
    have hnat : (626328919 : ℕ)^4209*50000000000000^3185 ≤ 20062070809177^3185*1250000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626328919 1250000000 20062070809177 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (115949129/312500000 : ℝ)^4209 ≤ (13488142567439/50000000000000 : ℝ)^3185 := by
    have hnat : (115949129 : ℕ)^4209*50000000000000^3185 ≤ 13488142567439^3185*312500000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115949129 312500000 13488142567439 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311736101/10000000000 : ℝ), (626328919/1250000000 : ℝ), (115949129/312500000 : ℝ)] ![(32899573236943/100000000000000 : ℝ), (20062070809177/50000000000000 : ℝ), (13488142567439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311736101/10000000000 : ℝ)|^4209 ≤ (32899573236943/100000000000000 : ℝ)^3185
        have hw : |(4311736101/10000000000 : ℝ)|=(4311736101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(626328919/1250000000 : ℝ)|^4209 ≤ (20062070809177/50000000000000 : ℝ)^3185
        have hw : |(626328919/1250000000 : ℝ)|=(626328919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(115949129/312500000 : ℝ)|^4209 ≤ (13488142567439/50000000000000 : ℝ)^3185
        have hw : |(115949129/312500000 : ℝ)|=(115949129/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1225_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11/40 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3/400 : ℝ)*pair X i i ≤ pair X i h) :
    (6101/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20071/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11/40 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3/400 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11/40 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3/400 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11/40 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3/400 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11/40 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3/400 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11/40 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3/400 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11/40 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3/400 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3/400 : ℝ) ^ (8417/2048 : ℝ) ≤ (92419223619/50000000000000000000 : ℝ) := by
    have hpowers : (3/400 : ℝ)^8417 ≤ (92419223619/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3 : ℕ)^8417*50000000000000000000^2048 ≤ 92419223619^2048*400^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 400 92419223619 50000000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3/400 : ℝ)) (X := (92419223619/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (11/40 : ℝ) ^ (8417/2048 : ℝ) ≤ (496288286918940329/100000000000000000000 : ℝ) := by
    have hpowers : (11/40 : ℝ)^8417 ≤ (496288286918940329/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11 : ℕ)^8417*100000000000000000000^2048 ≤ 496288286918940329^2048*40^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11 40 496288286918940329 100000000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11/40 : ℝ)) (X := (496288286918940329/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000092419223619/25000000000000000000 : ℝ) ≤ (10000000008994871/10000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (25000000092419223619/25000000000000000000 : ℝ)^2048 ≤ (10000000008994871/10000000000000000 : ℝ)^8417 := by
      have hnat : (25000000092419223619 : ℕ)^2048*10000000000000000^8417 ≤ 10000000008994871^8417*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000092419223619 25000000000000000000 10000000008994871 10000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000008994871/10000000000000000 : ℝ)) (X := (25000000092419223619/25000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100496288471757387567/100000000000000000000 : ℝ) ≤ (5006026469412663/5000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (100496288471757387567/100000000000000000000 : ℝ)^2048 ≤ (5006026469412663/5000000000000000 : ℝ)^8417 := by
      have hnat : (100496288471757387567 : ℕ)^2048*5000000000000000^8417 ≤ 5006026469412663^8417*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100496288471757387567 100000000000000000000 5006026469412663 5000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006026469412663/5000000000000000 : ℝ)) (X := (100496288471757387567/100000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50496288286918940329/50000000000000000000 : ℝ) ≤ (10024105868655781/10000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (50496288286918940329/50000000000000000000 : ℝ)^2048 ≤ (10024105868655781/10000000000000000 : ℝ)^8417 := by
      have hnat : (50496288286918940329 : ℕ)^2048*10000000000000000^8417 ≤ 10024105868655781^8417*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50496288286918940329 50000000000000000000 10024105868655781 10000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10024105868655781/10000000000000000 : ℝ)) (X := (50496288286918940329/50000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(92419223619/50000000000000000000 : ℝ) ≤ ((1069927683383468467/1070000000000000000 : ℝ)+2*(2410585966091/535000000000000 : ℝ)*(3/400 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (1069927683383468467/1070000000000000000 : ℝ)+2*(2410585966091/535000000000000 : ℝ)*(3/400 : ℝ)=(10000000008994871/10000000000000000 : ℝ) by norm_num, show 1+2*(92419223619/50000000000000000000 : ℝ)=(25000000092419223619/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(496288286918940329/100000000000000000000 : ℝ)+(92419223619/50000000000000000000 : ℝ) ≤ ((1069927683383468467/1070000000000000000 : ℝ)+(2410585966091/535000000000000 : ℝ)*((11/40 : ℝ)+(3/400 : ℝ)))^(8417/2048 : ℝ) := by
    rw [show (1069927683383468467/1070000000000000000 : ℝ)+(2410585966091/535000000000000 : ℝ)*((11/40 : ℝ)+(3/400 : ℝ))=(5006026469412663/5000000000000000 : ℝ) by norm_num, show 1+(496288286918940329/100000000000000000000 : ℝ)+(92419223619/50000000000000000000 : ℝ)=(100496288471757387567/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(496288286918940329/100000000000000000000 : ℝ) ≤ ((1069927683383468467/1070000000000000000 : ℝ)+2*(2410585966091/535000000000000 : ℝ)*(11/40 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (1069927683383468467/1070000000000000000 : ℝ)+2*(2410585966091/535000000000000 : ℝ)*(11/40 : ℝ)=(10024105868655781/10000000000000000 : ℝ) by norm_num, show 1+2*(496288286918940329/100000000000000000000 : ℝ)=(50496288286918940329/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1069927683383468467/1070000000000000000 : ℝ)*(X 1 0+X 2 0)+(2410585966091/535000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (3/400 : ℝ)) (hi := (11/40 : ℝ)) (c := (1069927683383468467/1070000000000000000 : ℝ)) (alpha := (2410585966091/535000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1069927683383468467/1070000000000000000 : ℝ)*(X 0 1+X 2 1)+(2410585966091/535000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (3/400 : ℝ)) (hi := (11/40 : ℝ)) (c := (1069927683383468467/1070000000000000000 : ℝ)) (alpha := (2410585966091/535000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1069927683383468467/1070000000000000000 : ℝ)*(X 0 2+X 1 2)+(2410585966091/535000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (3/400 : ℝ)) (hi := (11/40 : ℝ)) (c := (1069927683383468467/1070000000000000000 : ℝ)) (alpha := (2410585966091/535000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-516115959/2500000000 : ℝ)*X 0 0+(5679896821/10000000000 : ℝ)*X 0 1+(1003834087/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2707291503/5000000000 : ℝ)*X 1 0+(-120977897/500000000 : ℝ)*X 1 1+(5019170459/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2707291523/5000000000 : ℝ)*X 2 0+(5019170449/10000000000 : ℝ)*X 2 1+(-24195579/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((8620657/20000000 : ℝ)*X 0 0+(369236577/1000000000 : ℝ)*X 0 1+(628537277/1250000000 : ℝ)*X 0 2+(8620657/20000000 : ℝ)*X 1 0+(369236577/1000000000 : ℝ)*X 1 1+(628537277/1250000000 : ℝ)*X 1 2+(8620657/20000000 : ℝ)*X 2 0+(369236577/1000000000 : ℝ)*X 2 1+(628537277/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-258144527/1250000000 : ℝ)*X 0 0+(1005580913/2000000000 : ℝ)*X 0 1+(88609351/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5244497973/10000000000 : ℝ)*X 1 0+(-1767736327/10000000000 : ℝ)*X 1 1+(708873891/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((524449803/1000000000 : ℝ)*X 2 0+(1417747913/2500000000 : ℝ)*X 2 1+(-1767735483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4311736101/10000000000 : ℝ)*X 0 0+(626328919/1250000000 : ℝ)*X 0 1+(115949129/312500000 : ℝ)*X 0 2+(4311736101/10000000000 : ℝ)*X 1 0+(626328919/1250000000 : ℝ)*X 1 1+(115949129/312500000 : ℝ)*X 1 2+(4311736101/10000000000 : ℝ)*X 2 0+(626328919/1250000000 : ℝ)*X 2 1+(115949129/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14676444168695857155830949/1671875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (102556753/100000000000000 : ℝ)*(base1) + (19114853/1000000000000 : ℝ)*(base19) + (1538133/80000000000 : ℝ)*(base23) + (52222663/25000000000000 : ℝ)*(upper3) + (56641577/25000000000000 : ℝ)*(upper5) + (35344662893467/3125000000000 : ℝ)*(major0) + (35344662893467/3125000000000 : ℝ)*(major1) + (35344662893467/3125000000000 : ℝ)*(major2) + (302699194482217/20000000000000 : ℝ)*(sp0) + (94594039123983/6250000000000 : ℝ)*(sp1) + (756752307401389/50000000000000 : ℝ)*(sp2) + (37427306489813/5000000000000 : ℝ)*(sp3) + (1333451837/12500000000000 : ℝ)*(sp4) + (1340686343/25000000000000 : ℝ)*(sp7) + (149710319019677/20000000000000 : ℝ)*(f.failure) + (378376634367257/25000000000000 : ℝ)*(f.sum) + (41332702121/26123046875000000000000000 : ℝ)*base65 + (27072346208455339/3343750000000000000000000000000 : ℝ)*base67 + (36504758918392839/3343750000000000000000000000000 : ℝ)*base69 + (33941947599174089/3343750000000000000000000000000 : ℝ)*base71 + (2157422008619/1671875000000000000000000000 : ℝ)*base73 + (28699803639299089/3343750000000000000000000000000 : ℝ)*base75 + (24809579788549089/3343750000000000000000000000000 : ℝ)*base77 + (33008976059111589/3343750000000000000000000000000 : ℝ)*base79 + (8613376095119/1671875000000000000000000000 : ℝ)*base81 + (5517129/500000000000000000000 : ℝ)*base90 + (5517129/500000000000000000000 : ℝ)*base92 + (5517129/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (199527152216138259198983571/53500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (271033987/100000000000000 : ℝ)*(base19) + (42040861/100000000000000 : ℝ)*(base23) + (375147027/100000000000000 : ℝ)*(lower2) + (249195249/100000000000000 : ℝ)*(lower3) + (123094041/50000000000000 : ℝ)*(lower4) + (174554381/100000000000000 : ℝ)*(lower5) + (1162043026271829/100000000000000 : ℝ)*(major0) + (1162043026271829/100000000000000 : ℝ)*(major1) + (1162043026271829/100000000000000 : ℝ)*(major2) + (11877796289/100000000000000 : ℝ)*(sp0) + (777498256806649/50000000000000 : ℝ)*(sp4) + (1555008120375601/100000000000000 : ℝ)*(sp5) + (1555008349368727/100000000000000 : ℝ)*(sp6) + (769077536818077/100000000000000 : ℝ)*(sp7) + (769077536818077/100000000000000 : ℝ)*(f.failure) + (388752097852397/25000000000000 : ℝ)*(f.sum) + (155014084983311/26750000000000000000000000000 : ℝ)*base66 + (1055502247591794143/107000000000000000000000000000000 : ℝ)*base67 + (1428964871891794143/107000000000000000000000000000000 : ℝ)*base69 + (1158082954242794143/107000000000000000000000000000000 : ℝ)*base71 + (8306441115689/26750000000000000000000000000 : ℝ)*base73 + (127797167795205857/107000000000000000000000000000000 : ℝ)*base76 + (24475806716205857/107000000000000000000000000000000 : ℝ)*base78 + (814616960536794143/107000000000000000000000000000000 : ℝ)*base79 + (137387893674189/26750000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (19393929/2500000000000000000000 : ℝ)*base90 + (19393929/2500000000000000000000 : ℝ)*base92 + (19393929/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1225_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11/40 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3/400 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6101/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20071/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1225_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1225_s2_0 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2113364919/10000000000 : ℝ)*x 0 + (2747857219/5000000000 : ℝ)*x 1 + (5172181741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113364919/10000000000 : ℝ)^4209 ≤ (12821800795787/100000000000000 : ℝ)^3185 := by
    have hnat : (2113364919 : ℕ)^4209*100000000000000^3185 ≤ 12821800795787^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113364919 10000000000 12821800795787 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2747857219/5000000000 : ℝ)^4209 ≤ (1133391881179/2500000000000 : ℝ)^3185 := by
    have hnat : (2747857219 : ℕ)^4209*2500000000000^3185 ≤ 1133391881179^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747857219 5000000000 1133391881179 2500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5172181741/10000000000 : ℝ)^4209 ≤ (41842523943201/100000000000000 : ℝ)^3185 := by
    have hnat : (5172181741 : ℕ)^4209*100000000000000^3185 ≤ 41842523943201^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172181741 10000000000 41842523943201 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2113364919/10000000000 : ℝ), (2747857219/5000000000 : ℝ), (5172181741/10000000000 : ℝ)] ![(12821800795787/100000000000000 : ℝ), (1133391881179/2500000000000 : ℝ), (41842523943201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2113364919/10000000000 : ℝ)|^4209 ≤ (12821800795787/100000000000000 : ℝ)^3185
        have hw : |(-2113364919/10000000000 : ℝ)|=(2113364919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2747857219/5000000000 : ℝ)|^4209 ≤ (1133391881179/2500000000000 : ℝ)^3185
        have hw : |(2747857219/5000000000 : ℝ)|=(2747857219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5172181741/10000000000 : ℝ)|^4209 ≤ (41842523943201/100000000000000 : ℝ)^3185
        have hw : |(5172181741/10000000000 : ℝ)|=(5172181741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s2_1 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370379343/10000000000 : ℝ)*x 0 + (-71282897/312500000 : ℝ)*x 1 + (1293045419/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370379343/10000000000 : ℝ)^4209 ≤ (43974372624211/100000000000000 : ℝ)^3185 := by
    have hnat : (5370379343 : ℕ)^4209*100000000000000^3185 ≤ 43974372624211^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370379343 10000000000 43974372624211 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71282897/312500000 : ℝ)^4209 ≤ (14183104108787/100000000000000 : ℝ)^3185 := by
    have hnat : (71282897 : ℕ)^4209*100000000000000^3185 ≤ 14183104108787^3185*312500000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71282897 312500000 14183104108787 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293045419/2500000000 : ℝ)^4209 ≤ (41842523248293/100000000000000 : ℝ)^3185 := by
    have hnat : (1293045419 : ℕ)^4209*100000000000000^3185 ≤ 41842523248293^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293045419 2500000000 41842523248293 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370379343/10000000000 : ℝ), (-71282897/312500000 : ℝ), (1293045419/2500000000 : ℝ)] ![(43974372624211/100000000000000 : ℝ), (14183104108787/100000000000000 : ℝ), (41842523248293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370379343/10000000000 : ℝ)|^4209 ≤ (43974372624211/100000000000000 : ℝ)^3185
        have hw : |(5370379343/10000000000 : ℝ)|=(5370379343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-71282897/312500000 : ℝ)|^4209 ≤ (14183104108787/100000000000000 : ℝ)^3185
        have hw : |(-71282897/312500000 : ℝ)|=(71282897/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293045419/2500000000 : ℝ)|^4209 ≤ (41842523248293/100000000000000 : ℝ)^3185
        have hw : |(1293045419/2500000000 : ℝ)|=(1293045419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s2_2 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107407583/200000000 : ℝ)*x 0 + (5172181847/10000000000 : ℝ)*x 1 + (-35641449/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107407583/200000000 : ℝ)^4209 ≤ (43974370535773/100000000000000 : ℝ)^3185 := by
    have hnat : (107407583 : ℕ)^4209*100000000000000^3185 ≤ 43974370535773^3185*200000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107407583 200000000 43974370535773 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5172181847/10000000000 : ℝ)^4209 ≤ (20921262538217/50000000000000 : ℝ)^3185 := by
    have hnat : (5172181847 : ℕ)^4209*50000000000000^3185 ≤ 20921262538217^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172181847 10000000000 20921262538217 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35641449/156250000 : ℝ)^4209 ≤ (7091552185863/50000000000000 : ℝ)^3185 := by
    have hnat : (35641449 : ℕ)^4209*50000000000000^3185 ≤ 7091552185863^3185*156250000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35641449 156250000 7091552185863 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107407583/200000000 : ℝ), (5172181847/10000000000 : ℝ), (-35641449/156250000 : ℝ)] ![(43974370535773/100000000000000 : ℝ), (20921262538217/50000000000000 : ℝ), (7091552185863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107407583/200000000 : ℝ)|^4209 ≤ (43974370535773/100000000000000 : ℝ)^3185
        have hw : |(107407583/200000000 : ℝ)|=(107407583/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5172181847/10000000000 : ℝ)|^4209 ≤ (20921262538217/50000000000000 : ℝ)^3185
        have hw : |(5172181847/10000000000 : ℝ)|=(5172181847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35641449/156250000 : ℝ)|^4209 ≤ (7091552185863/50000000000000 : ℝ)^3185
        have hw : |(-35641449/156250000 : ℝ)|=(35641449/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s2_3 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4344068003/10000000000 : ℝ)*x 0 + (805792531/2000000000 : ℝ)*x 1 + (4683118153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4344068003/10000000000 : ℝ)^4209 ≤ (4153247687523/12500000000000 : ℝ)^3185 := by
    have hnat : (4344068003 : ℕ)^4209*12500000000000^3185 ≤ 4153247687523^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4344068003 10000000000 4153247687523 12500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (805792531/2000000000 : ℝ)^4209 ≤ (30078770501209/100000000000000 : ℝ)^3185 := by
    have hnat : (805792531 : ℕ)^4209*100000000000000^3185 ≤ 30078770501209^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805792531 2000000000 30078770501209 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4683118153/10000000000 : ℝ)^4209 ≤ (7339049596889/20000000000000 : ℝ)^3185 := by
    have hnat : (4683118153 : ℕ)^4209*20000000000000^3185 ≤ 7339049596889^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4683118153 10000000000 7339049596889 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4344068003/10000000000 : ℝ), (805792531/2000000000 : ℝ), (4683118153/10000000000 : ℝ)] ![(4153247687523/12500000000000 : ℝ), (30078770501209/100000000000000 : ℝ), (7339049596889/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4344068003/10000000000 : ℝ)|^4209 ≤ (4153247687523/12500000000000 : ℝ)^3185
        have hw : |(4344068003/10000000000 : ℝ)|=(4344068003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(805792531/2000000000 : ℝ)|^4209 ≤ (30078770501209/100000000000000 : ℝ)^3185
        have hw : |(805792531/2000000000 : ℝ)|=(805792531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4683118153/10000000000 : ℝ)|^4209 ≤ (7339049596889/20000000000000 : ℝ)^3185
        have hw : |(4683118153/10000000000 : ℝ)|=(4683118153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s2_4 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-422689391/2000000000 : ℝ)*x 0 + (1293571567/2500000000 : ℝ)*x 1 + (1098717993/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422689391/2000000000 : ℝ)^4209 ≤ (3205614632793/25000000000000 : ℝ)^3185 := by
    have hnat : (422689391 : ℕ)^4209*25000000000000^3185 ≤ 3205614632793^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422689391 2000000000 3205614632793 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293571567/2500000000 : ℝ)^4209 ≤ (523312808339/1250000000000 : ℝ)^3185 := by
    have hnat : (1293571567 : ℕ)^4209*1250000000000^3185 ≤ 523312808339^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293571567 2500000000 523312808339 1250000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098717993/2000000000 : ℝ)^4209 ≤ (45312516788867/100000000000000 : ℝ)^3185 := by
    have hnat : (1098717993 : ℕ)^4209*100000000000000^3185 ≤ 45312516788867^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098717993 2000000000 45312516788867 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-422689391/2000000000 : ℝ), (1293571567/2500000000 : ℝ), (1098717993/2000000000 : ℝ)] ![(3205614632793/25000000000000 : ℝ), (523312808339/1250000000000 : ℝ), (45312516788867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-422689391/2000000000 : ℝ)|^4209 ≤ (3205614632793/25000000000000 : ℝ)^3185
        have hw : |(-422689391/2000000000 : ℝ)|=(422689391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1293571567/2500000000 : ℝ)|^4209 ≤ (523312808339/1250000000000 : ℝ)^3185
        have hw : |(1293571567/2500000000 : ℝ)|=(1293571567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1098717993/2000000000 : ℝ)|^4209 ≤ (45312516788867/100000000000000 : ℝ)^3185
        have hw : |(1098717993/2000000000 : ℝ)|=(1098717993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s2_5 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643922823/5000000000 : ℝ)*x 0 + (-489911061/2500000000 : ℝ)*x 1 + (5493590003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643922823/5000000000 : ℝ)^4209 ≤ (21541748109321/50000000000000 : ℝ)^3185 := by
    have hnat : (2643922823 : ℕ)^4209*50000000000000^3185 ≤ 21541748109321^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643922823 5000000000 21541748109321 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (489911061/2500000000 : ℝ)^4209 ≤ (2320797313121/20000000000000 : ℝ)^3185 := by
    have hnat : (489911061 : ℕ)^4209*20000000000000^3185 ≤ 2320797313121^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489911061 2500000000 2320797313121 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5493590003/10000000000 : ℝ)^4209 ≤ (45312517203071/100000000000000 : ℝ)^3185 := by
    have hnat : (5493590003 : ℕ)^4209*100000000000000^3185 ≤ 45312517203071^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493590003 10000000000 45312517203071 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643922823/5000000000 : ℝ), (-489911061/2500000000 : ℝ), (5493590003/10000000000 : ℝ)] ![(21541748109321/50000000000000 : ℝ), (2320797313121/20000000000000 : ℝ), (45312517203071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643922823/5000000000 : ℝ)|^4209 ≤ (21541748109321/50000000000000 : ℝ)^3185
        have hw : |(2643922823/5000000000 : ℝ)|=(2643922823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-489911061/2500000000 : ℝ)|^4209 ≤ (2320797313121/20000000000000 : ℝ)^3185
        have hw : |(-489911061/2500000000 : ℝ)|=(489911061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5493590003/10000000000 : ℝ)|^4209 ≤ (45312517203071/100000000000000 : ℝ)^3185
        have hw : |(5493590003/10000000000 : ℝ)|=(5493590003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s2_6 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287845827/10000000000 : ℝ)*x 0 + (686698757/1250000000 : ℝ)*x 1 + (-979821961/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287845827/10000000000 : ℝ)^4209 ≤ (17233399267/40000000000 : ℝ)^3185 := by
    have hnat : (5287845827 : ℕ)^4209*40000000000^3185 ≤ 17233399267^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287845827 10000000000 17233399267 40000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (686698757/1250000000 : ℝ)^4209 ≤ (22656258890389/50000000000000 : ℝ)^3185 := by
    have hnat : (686698757 : ℕ)^4209*50000000000000^3185 ≤ 22656258890389^3185*1250000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686698757 1250000000 22656258890389 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (979821961/5000000000 : ℝ)^4209 ≤ (11603984045867/100000000000000 : ℝ)^3185 := by
    have hnat : (979821961 : ℕ)^4209*100000000000000^3185 ≤ 11603984045867^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979821961 5000000000 11603984045867 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287845827/10000000000 : ℝ), (686698757/1250000000 : ℝ), (-979821961/5000000000 : ℝ)] ![(17233399267/40000000000 : ℝ), (22656258890389/50000000000000 : ℝ), (11603984045867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287845827/10000000000 : ℝ)|^4209 ≤ (17233399267/40000000000 : ℝ)^3185
        have hw : |(5287845827/10000000000 : ℝ)|=(5287845827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(686698757/1250000000 : ℝ)|^4209 ≤ (22656258890389/50000000000000 : ℝ)^3185
        have hw : |(686698757/1250000000 : ℝ)|=(686698757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-979821961/5000000000 : ℝ)|^4209 ≤ (11603984045867/100000000000000 : ℝ)^3185
        have hw : |(-979821961/5000000000 : ℝ)|=(979821961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s2_7 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4344233337/10000000000 : ℝ)*x 0 + (4678863117/10000000000 : ℝ)*x 1 + (2016628901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4344233337/10000000000 : ℝ)^4209 ≤ (33227652650529/100000000000000 : ℝ)^3185 := by
    have hnat : (4344233337 : ℕ)^4209*100000000000000^3185 ≤ 33227652650529^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4344233337 10000000000 33227652650529 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4678863117/10000000000 : ℝ)^4209 ≤ (36651194122189/100000000000000 : ℝ)^3185 := by
    have hnat : (4678863117 : ℕ)^4209*100000000000000^3185 ≤ 36651194122189^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4678863117 10000000000 36651194122189 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2016628901/5000000000 : ℝ)^4209 ≤ (30121153215041/100000000000000 : ℝ)^3185 := by
    have hnat : (2016628901 : ℕ)^4209*100000000000000^3185 ≤ 30121153215041^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016628901 5000000000 30121153215041 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4344233337/10000000000 : ℝ), (4678863117/10000000000 : ℝ), (2016628901/5000000000 : ℝ)] ![(33227652650529/100000000000000 : ℝ), (36651194122189/100000000000000 : ℝ), (30121153215041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4344233337/10000000000 : ℝ)|^4209 ≤ (33227652650529/100000000000000 : ℝ)^3185
        have hw : |(4344233337/10000000000 : ℝ)|=(4344233337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4678863117/10000000000 : ℝ)|^4209 ≤ (36651194122189/100000000000000 : ℝ)^3185
        have hw : |(4678863117/10000000000 : ℝ)|=(4678863117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2016628901/5000000000 : ℝ)|^4209 ≤ (30121153215041/100000000000000 : ℝ)^3185
        have hw : |(2016628901/5000000000 : ℝ)|=(2016628901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1225_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (943/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4067/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6101/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6101/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6101/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6101/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6101/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6101/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6101/100000 : ℝ) ^ (8417/2048 : ℝ) ≤ (509488370721839/50000000000000000000 : ℝ) := by
    have hpowers : (6101/100000 : ℝ)^8417 ≤ (509488370721839/50000000000000000000 : ℝ)^2048 := by
      have hnat : (6101 : ℕ)^8417*50000000000000000000^2048 ≤ 509488370721839^2048*100000^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6101 100000 509488370721839 50000000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6101/100000 : ℝ)) (X := (509488370721839/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20071/100000 : ℝ) ^ (8417/2048 : ℝ) ≤ (136036041778786289/100000000000000000000 : ℝ) := by
    have hpowers : (20071/100000 : ℝ)^8417 ≤ (136036041778786289/100000000000000000000 : ℝ)^2048 := by
      have hnat : (20071 : ℕ)^8417*100000000000000000000^2048 ≤ 136036041778786289^2048*100000^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20071 100000 136036041778786289 100000000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20071/100000 : ℝ)) (X := (136036041778786289/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000509488370721839/25000000000000000000 : ℝ) ≤ (2000009917302013/2000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (25000509488370721839/25000000000000000000 : ℝ)^2048 ≤ (2000009917302013/2000000000000000 : ℝ)^8417 := by
      have hnat : (25000509488370721839 : ℕ)^2048*2000000000000000^8417 ≤ 2000009917302013^8417*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000509488370721839 25000000000000000000 2000009917302013 2000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000009917302013/2000000000000000 : ℝ)) (X := (25000509488370721839/25000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100137055018520229967/100000000000000000000 : ℝ) ≤ (5001666527548161/5000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (100137055018520229967/100000000000000000000 : ℝ)^2048 ≤ (5001666527548161/5000000000000000 : ℝ)^8417 := by
      have hnat : (100137055018520229967 : ℕ)^2048*5000000000000000^8417 ≤ 5001666527548161^8417*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100137055018520229967 100000000000000000000 5001666527548161 5000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001666527548161/5000000000000000 : ℝ)) (X := (100137055018520229967/100000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50136036041778786289/50000000000000000000 : ℝ) ≤ (10006616523682579/10000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (50136036041778786289/50000000000000000000 : ℝ)^2048 ≤ (10006616523682579/10000000000000000 : ℝ)^8417 := by
      have hnat : (50136036041778786289 : ℕ)^2048*10000000000000000^8417 ≤ 10006616523682579^8417*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50136036041778786289 50000000000000000000 10006616523682579 10000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006616523682579/10000000000000000 : ℝ)) (X := (50136036041778786289/50000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(509488370721839/50000000000000000000 : ℝ) ≤ ((17457578479982012517/17462500000000000000 : ℝ)+2*(3283468586257/1397000000000000 : ℝ)*(6101/100000 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (17457578479982012517/17462500000000000000 : ℝ)+2*(3283468586257/1397000000000000 : ℝ)*(6101/100000 : ℝ)=(2000009917302013/2000000000000000 : ℝ) by norm_num, show 1+2*(509488370721839/50000000000000000000 : ℝ)=(25000509488370721839/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(136036041778786289/100000000000000000000 : ℝ)+(509488370721839/50000000000000000000 : ℝ) ≤ ((17457578479982012517/17462500000000000000 : ℝ)+(3283468586257/1397000000000000 : ℝ)*((20071/100000 : ℝ)+(6101/100000 : ℝ)))^(8417/2048 : ℝ) := by
    rw [show (17457578479982012517/17462500000000000000 : ℝ)+(3283468586257/1397000000000000 : ℝ)*((20071/100000 : ℝ)+(6101/100000 : ℝ))=(5001666527548161/5000000000000000 : ℝ) by norm_num, show 1+(136036041778786289/100000000000000000000 : ℝ)+(509488370721839/50000000000000000000 : ℝ)=(100137055018520229967/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(136036041778786289/100000000000000000000 : ℝ) ≤ ((17457578479982012517/17462500000000000000 : ℝ)+2*(3283468586257/1397000000000000 : ℝ)*(20071/100000 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (17457578479982012517/17462500000000000000 : ℝ)+2*(3283468586257/1397000000000000 : ℝ)*(20071/100000 : ℝ)=(10006616523682579/10000000000000000 : ℝ) by norm_num, show 1+2*(136036041778786289/100000000000000000000 : ℝ)=(50136036041778786289/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17457578479982012517/17462500000000000000 : ℝ)*(X 1 0+X 2 0)+(3283468586257/1397000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (6101/100000 : ℝ)) (hi := (20071/100000 : ℝ)) (c := (17457578479982012517/17462500000000000000 : ℝ)) (alpha := (3283468586257/1397000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17457578479982012517/17462500000000000000 : ℝ)*(X 0 1+X 2 1)+(3283468586257/1397000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (6101/100000 : ℝ)) (hi := (20071/100000 : ℝ)) (c := (17457578479982012517/17462500000000000000 : ℝ)) (alpha := (3283468586257/1397000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17457578479982012517/17462500000000000000 : ℝ)*(X 0 2+X 1 2)+(3283468586257/1397000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (6101/100000 : ℝ)) (hi := (20071/100000 : ℝ)) (c := (17457578479982012517/17462500000000000000 : ℝ)) (alpha := (3283468586257/1397000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2113364919/10000000000 : ℝ)*X 0 0+(2747857219/5000000000 : ℝ)*X 0 1+(5172181741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5370379343/10000000000 : ℝ)*X 1 0+(-71282897/312500000 : ℝ)*X 1 1+(1293045419/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((107407583/200000000 : ℝ)*X 2 0+(5172181847/10000000000 : ℝ)*X 2 1+(-35641449/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4344068003/10000000000 : ℝ)*X 0 0+(805792531/2000000000 : ℝ)*X 0 1+(4683118153/10000000000 : ℝ)*X 0 2+(4344068003/10000000000 : ℝ)*X 1 0+(805792531/2000000000 : ℝ)*X 1 1+(4683118153/10000000000 : ℝ)*X 1 2+(4344068003/10000000000 : ℝ)*X 2 0+(805792531/2000000000 : ℝ)*X 2 1+(4683118153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-422689391/2000000000 : ℝ)*X 0 0+(1293571567/2500000000 : ℝ)*X 0 1+(1098717993/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643922823/5000000000 : ℝ)*X 1 0+(-489911061/2500000000 : ℝ)*X 1 1+(5493590003/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287845827/10000000000 : ℝ)*X 2 0+(686698757/1250000000 : ℝ)*X 2 1+(-979821961/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4344233337/10000000000 : ℝ)*X 0 0+(4678863117/10000000000 : ℝ)*X 0 1+(2016628901/5000000000 : ℝ)*X 0 2+(4344233337/10000000000 : ℝ)*X 1 0+(4678863117/10000000000 : ℝ)*X 1 1+(2016628901/5000000000 : ℝ)*X 1 2+(4344233337/10000000000 : ℝ)*X 2 0+(4678863117/10000000000 : ℝ)*X 2 1+(2016628901/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1925297154892649854475906943/873125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (207258611/50000000000000 : ℝ)*(base19) + (33196807/12500000000000 : ℝ)*(base23) + (10166923/50000000000000 : ℝ)*(lower2) + (11897999/12500000000000 : ℝ)*(upper3) + (1801847/10000000000000 : ℝ)*(upper5) + (2309788733395207/100000000000000 : ℝ)*(major0) + (2309788733395207/100000000000000 : ℝ)*(major1) + (2309788733395207/100000000000000 : ℝ)*(major2) + (1545441053271103/50000000000000 : ℝ)*(sp0) + (154544216593269/5000000000000 : ℝ)*(sp1) + (1545442240404073/50000000000000 : ℝ)*(sp2) + (764345156805051/50000000000000 : ℝ)*(sp3) + (527968079/20000000000000 : ℝ)*(sp4) + (2333295547/100000000000000 : ℝ)*(sp7) + (1528692646905649/100000000000000 : ℝ)*(f.failure) + (1545442373191301/50000000000000 : ℝ)*(f.sum) + (193498302166099/69850000000000000000000000000 : ℝ)*base65 + (13036985426673043519/1746250000000000000000000000000000 : ℝ)*base67 + (9603614806763043519/1746250000000000000000000000000000 : ℝ)*base69 + (472205545746956481/1746250000000000000000000000000000 : ℝ)*base72 + (201908578633549/69850000000000000000000000000 : ℝ)*base73 + (3243632503734293519/1746250000000000000000000000000000 : ℝ)*base75 + (18702124888853043519/1746250000000000000000000000000000 : ℝ)*base77 + (6695918229424456481/1746250000000000000000000000000000 : ℝ)*base80 + (30776338933201/69850000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1408973/2500000000000000000000 : ℝ)*base90 + (1408973/2500000000000000000000 : ℝ)*base92 + (1408973/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2311281761616826083863586111/436562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (713898843/50000000000000 : ℝ)*(base19) + (1699846151/100000000000000 : ℝ)*(base23) + (5104541/12500000000000 : ℝ)*(upper2) + (99916233/50000000000000 : ℝ)*(upper3) + (26275471/25000000000000 : ℝ)*(upper5) + (2340374094123189/100000000000000 : ℝ)*(major0) + (2340374094123189/100000000000000 : ℝ)*(major1) + (2340374094123189/100000000000000 : ℝ)*(major2) + (14171773503/100000000000000 : ℝ)*(sp1) + (9892840639/50000000000000 : ℝ)*(sp2) + (1565906493560967/50000000000000 : ℝ)*(sp4) + (391474673443843/12500000000000 : ℝ)*(sp5) + (1565895750797253/50000000000000 : ℝ)*(sp6) + (154893502464861/10000000000000 : ℝ)*(sp7) + (154893502464861/10000000000000 : ℝ)*(f.failure) + (1565906493560967/50000000000000 : ℝ)*(f.sum) + (346565793503573/69850000000000000000000000000 : ℝ)*base65 + (23201034674215119213/1746250000000000000000000000000000 : ℝ)*base67 + (117737955354880787/1746250000000000000000000000000000 : ℝ)*base70 + (16201364356368869213/1746250000000000000000000000000000 : ℝ)*base71 + (183368454531873/69850000000000000000000000000 : ℝ)*base73 + (31875743198207619213/1746250000000000000000000000000000 : ℝ)*base75 + (5960706481902619213/1746250000000000000000000000000000 : ℝ)*base77 + (7541729031052619213/1746250000000000000000000000000000 : ℝ)*base79 + (82794157274427/69850000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (2880297/250000000000000000000 : ℝ)*base90 + (2880297/250000000000000000000 : ℝ)*base92 + (2880297/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1225_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6101/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (943/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4067/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1225_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1225_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (943/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4067/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1225_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1225_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1225_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (943/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4067/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1225_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
