-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1350_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:07:22.17099+00:00
-- url     : https://prove2.me/submissions/68096918-a5cd-4011-b339-695f4bd25540

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
theorem support_rectangle_w1350_s0_0 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-72177053/400000000 : ℝ)*x 0 + (5993468731/10000000000 : ℝ)*x 1 + (75200221/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (72177053/400000000 : ℝ)^2155 ≤ (211653659839/2000000000000 : ℝ)^1643 := by
    have hnat : (72177053 : ℕ)^2155*2000000000000^1643 ≤ 211653659839^1643*400000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72177053 400000000 211653659839 2000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5993468731/10000000000 : ℝ)^2155 ≤ (3193575788201/6250000000000 : ℝ)^1643 := by
    have hnat : (5993468731 : ℕ)^2155*6250000000000^1643 ≤ 3193575788201^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5993468731 10000000000 3193575788201 6250000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75200221/156250000 : ℝ)^2155 ≤ (9580026096007/25000000000000 : ℝ)^1643 := by
    have hnat : (75200221 : ℕ)^2155*25000000000000^1643 ≤ 9580026096007^1643*156250000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75200221 156250000 9580026096007 25000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-72177053/400000000 : ℝ), (5993468731/10000000000 : ℝ), (75200221/156250000 : ℝ)] ![(211653659839/2000000000000 : ℝ), (3193575788201/6250000000000 : ℝ), (9580026096007/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-72177053/400000000 : ℝ)|^2155 ≤ (211653659839/2000000000000 : ℝ)^1643
        have hw : |(-72177053/400000000 : ℝ)|=(72177053/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5993468731/10000000000 : ℝ)|^2155 ≤ (3193575788201/6250000000000 : ℝ)^1643
        have hw : |(5993468731/10000000000 : ℝ)|=(5993468731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(75200221/156250000 : ℝ)|^2155 ≤ (9580026096007/25000000000000 : ℝ)^1643
        have hw : |(75200221/156250000 : ℝ)|=(75200221/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s0_1 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2750458441/5000000000 : ℝ)*x 0 + (-2475115757/10000000000 : ℝ)*x 1 + (1203203647/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2750458441/5000000000 : ℝ)^2155 ≤ (45661286744081/100000000000000 : ℝ)^1643 := by
    have hnat : (2750458441 : ℕ)^2155*100000000000000^1643 ≤ 45661286744081^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750458441 5000000000 45661286744081 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2475115757/10000000000 : ℝ)^2155 ≤ (16018604220243/100000000000000 : ℝ)^1643 := by
    have hnat : (2475115757 : ℕ)^2155*100000000000000^1643 ≤ 16018604220243^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2475115757 10000000000 16018604220243 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1203203647/2500000000 : ℝ)^2155 ≤ (2395006813803/6250000000000 : ℝ)^1643 := by
    have hnat : (1203203647 : ℕ)^2155*6250000000000^1643 ≤ 2395006813803^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203203647 2500000000 2395006813803 6250000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2750458441/5000000000 : ℝ), (-2475115757/10000000000 : ℝ), (1203203647/2500000000 : ℝ)] ![(45661286744081/100000000000000 : ℝ), (16018604220243/100000000000000 : ℝ), (2395006813803/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2750458441/5000000000 : ℝ)|^2155 ≤ (45661286744081/100000000000000 : ℝ)^1643
        have hw : |(2750458441/5000000000 : ℝ)|=(2750458441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2475115757/10000000000 : ℝ)|^2155 ≤ (16018604220243/100000000000000 : ℝ)^1643
        have hw : |(-2475115757/10000000000 : ℝ)|=(2475115757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1203203647/2500000000 : ℝ)|^2155 ≤ (2395006813803/6250000000000 : ℝ)^1643
        have hw : |(1203203647/2500000000 : ℝ)|=(1203203647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s0_2 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (220036667/400000000 : ℝ)*x 0 + (4812814249/10000000000 : ℝ)*x 1 + (-61877911/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220036667/400000000 : ℝ)^2155 ≤ (45661284490397/100000000000000 : ℝ)^1643 := by
    have hnat : (220036667 : ℕ)^2155*100000000000000^1643 ≤ 45661284490397^1643*400000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220036667 400000000 45661284490397 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4812814249/10000000000 : ℝ)^2155 ≤ (38320105480573/100000000000000 : ℝ)^1643 := by
    have hnat : (4812814249 : ℕ)^2155*100000000000000^1643 ≤ 38320105480573^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4812814249 10000000000 38320105480573 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (61877911/250000000 : ℝ)^2155 ≤ (8009305008997/50000000000000 : ℝ)^1643 := by
    have hnat : (61877911 : ℕ)^2155*50000000000000^1643 ≤ 8009305008997^1643*250000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61877911 250000000 8009305008997 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(220036667/400000000 : ℝ), (4812814249/10000000000 : ℝ), (-61877911/250000000 : ℝ)] ![(45661284490397/100000000000000 : ℝ), (38320105480573/100000000000000 : ℝ), (8009305008997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(220036667/400000000 : ℝ)|^2155 ≤ (45661284490397/100000000000000 : ℝ)^1643
        have hw : |(220036667/400000000 : ℝ)|=(220036667/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4812814249/10000000000 : ℝ)|^2155 ≤ (38320105480573/100000000000000 : ℝ)^1643
        have hw : |(4812814249/10000000000 : ℝ)|=(4812814249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-61877911/250000000 : ℝ)|^2155 ≤ (8009305008997/50000000000000 : ℝ)^1643
        have hw : |(-61877911/250000000 : ℝ)|=(61877911/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s0_3 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4177551563/10000000000 : ℝ)*x 0 + (1553089069/5000000000 : ℝ)*x 1 + (5586589341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4177551563/10000000000 : ℝ)^2155 ≤ (3978336964947/12500000000000 : ℝ)^1643 := by
    have hnat : (4177551563 : ℕ)^2155*12500000000000^1643 ≤ 3978336964947^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4177551563 10000000000 3978336964947 12500000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1553089069/5000000000 : ℝ)^2155 ≤ (21577014782827/100000000000000 : ℝ)^1643 := by
    have hnat : (1553089069 : ℕ)^2155*100000000000000^1643 ≤ 21577014782827^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1553089069 5000000000 21577014782827 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5586589341/10000000000 : ℝ)^2155 ≤ (4659628947909/10000000000000 : ℝ)^1643 := by
    have hnat : (5586589341 : ℕ)^2155*10000000000000^1643 ≤ 4659628947909^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5586589341 10000000000 4659628947909 10000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4177551563/10000000000 : ℝ), (1553089069/5000000000 : ℝ), (5586589341/10000000000 : ℝ)] ![(3978336964947/12500000000000 : ℝ), (21577014782827/100000000000000 : ℝ), (4659628947909/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4177551563/10000000000 : ℝ)|^2155 ≤ (3978336964947/12500000000000 : ℝ)^1643
        have hw : |(4177551563/10000000000 : ℝ)|=(4177551563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1553089069/5000000000 : ℝ)|^2155 ≤ (21577014782827/100000000000000 : ℝ)^1643
        have hw : |(1553089069/5000000000 : ℝ)|=(1553089069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5586589341/10000000000 : ℝ)|^2155 ≤ (4659628947909/10000000000000 : ℝ)^1643
        have hw : |(5586589341/10000000000 : ℝ)|=(5586589341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s0_4 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1808841143/10000000000 : ℝ)*x 0 + (2421593407/5000000000 : ℝ)*x 1 + (119240227/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1808841143/10000000000 : ℝ)^2155 ≤ (2654164206979/25000000000000 : ℝ)^1643 := by
    have hnat : (1808841143 : ℕ)^2155*25000000000000^1643 ≤ 2654164206979^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1808841143 10000000000 2654164206979 25000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2421593407/5000000000 : ℝ)^2155 ≤ (38637606402933/100000000000000 : ℝ)^1643 := by
    have hnat : (2421593407 : ℕ)^2155*100000000000000^1643 ≤ 38637606402933^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2421593407 5000000000 38637606402933 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119240227/200000000 : ℝ)^2155 ≤ (50745736753661/100000000000000 : ℝ)^1643 := by
    have hnat : (119240227 : ℕ)^2155*100000000000000^1643 ≤ 50745736753661^1643*200000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119240227 200000000 50745736753661 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1808841143/10000000000 : ℝ), (2421593407/5000000000 : ℝ), (119240227/200000000 : ℝ)] ![(2654164206979/25000000000000 : ℝ), (38637606402933/100000000000000 : ℝ), (50745736753661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1808841143/10000000000 : ℝ)|^2155 ≤ (2654164206979/25000000000000 : ℝ)^1643
        have hw : |(-1808841143/10000000000 : ℝ)|=(1808841143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2421593407/5000000000 : ℝ)|^2155 ≤ (38637606402933/100000000000000 : ℝ)^1643
        have hw : |(2421593407/5000000000 : ℝ)|=(2421593407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119240227/200000000 : ℝ)|^2155 ≤ (50745736753661/100000000000000 : ℝ)^1643
        have hw : |(119240227/200000000 : ℝ)|=(119240227/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s0_5 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5179099747/10000000000 : ℝ)*x 0 + (-132592017/1000000000 : ℝ)*x 1 + (1490502751/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5179099747/10000000000 : ℝ)^2155 ≤ (10547480980153/25000000000000 : ℝ)^1643 := by
    have hnat : (5179099747 : ℕ)^2155*25000000000000^1643 ≤ 10547480980153^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179099747 10000000000 10547480980153 25000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132592017/1000000000 : ℝ)^2155 ≤ (7064343169183/100000000000000 : ℝ)^1643 := by
    have hnat : (132592017 : ℕ)^2155*100000000000000^1643 ≤ 7064343169183^1643*1000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132592017 1000000000 7064343169183 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1490502751/2500000000 : ℝ)^2155 ≤ (50745732890947/100000000000000 : ℝ)^1643 := by
    have hnat : (1490502751 : ℕ)^2155*100000000000000^1643 ≤ 50745732890947^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1490502751 2500000000 50745732890947 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5179099747/10000000000 : ℝ), (-132592017/1000000000 : ℝ), (1490502751/2500000000 : ℝ)] ![(10547480980153/25000000000000 : ℝ), (7064343169183/100000000000000 : ℝ), (50745732890947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5179099747/10000000000 : ℝ)|^2155 ≤ (10547480980153/25000000000000 : ℝ)^1643
        have hw : |(5179099747/10000000000 : ℝ)|=(5179099747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-132592017/1000000000 : ℝ)|^2155 ≤ (7064343169183/100000000000000 : ℝ)^1643
        have hw : |(-132592017/1000000000 : ℝ)|=(132592017/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1490502751/2500000000 : ℝ)|^2155 ≤ (50745732890947/100000000000000 : ℝ)^1643
        have hw : |(1490502751/2500000000 : ℝ)|=(1490502751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s0_6 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1294774923/2500000000 : ℝ)*x 0 + (1192402279/2000000000 : ℝ)*x 1 + (-132591963/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1294774923/2500000000 : ℝ)^2155 ≤ (42189923332951/100000000000000 : ℝ)^1643 := by
    have hnat : (1294774923 : ℕ)^2155*100000000000000^1643 ≤ 42189923332951^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294774923 2500000000 42189923332951 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1192402279/2000000000 : ℝ)^2155 ≤ (25372868628019/50000000000000 : ℝ)^1643 := by
    have hnat : (1192402279 : ℕ)^2155*50000000000000^1643 ≤ 25372868628019^1643*2000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192402279 2000000000 25372868628019 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132591963/1000000000 : ℝ)^2155 ≤ (3532169697783/50000000000000 : ℝ)^1643 := by
    have hnat : (132591963 : ℕ)^2155*50000000000000^1643 ≤ 3532169697783^1643*1000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132591963 1000000000 3532169697783 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1294774923/2500000000 : ℝ), (1192402279/2000000000 : ℝ), (-132591963/1000000000 : ℝ)] ![(42189923332951/100000000000000 : ℝ), (25372868628019/50000000000000 : ℝ), (3532169697783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1294774923/2500000000 : ℝ)|^2155 ≤ (42189923332951/100000000000000 : ℝ)^1643
        have hw : |(1294774923/2500000000 : ℝ)|=(1294774923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1192402279/2000000000 : ℝ)|^2155 ≤ (25372868628019/50000000000000 : ℝ)^1643
        have hw : |(1192402279/2000000000 : ℝ)|=(1192402279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-132591963/1000000000 : ℝ)|^2155 ≤ (3532169697783/50000000000000 : ℝ)^1643
        have hw : |(-132591963/1000000000 : ℝ)|=(132591963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s0_7 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4186823973/10000000000 : ℝ)*x 0 + (110455623/200000000 : ℝ)*x 1 + (396533229/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4186823973/10000000000 : ℝ)^2155 ≤ (31919383432083/100000000000000 : ℝ)^1643 := by
    have hnat : (4186823973 : ℕ)^2155*100000000000000^1643 ≤ 31919383432083^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186823973 10000000000 31919383432083 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110455623/200000000 : ℝ)^2155 ≤ (9179895658471/20000000000000 : ℝ)^1643 := by
    have hnat : (110455623 : ℕ)^2155*20000000000000^1643 ≤ 9179895658471^1643*200000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110455623 200000000 9179895658471 20000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (396533229/1250000000 : ℝ)^2155 ≤ (11090569131003/50000000000000 : ℝ)^1643 := by
    have hnat : (396533229 : ℕ)^2155*50000000000000^1643 ≤ 11090569131003^1643*1250000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396533229 1250000000 11090569131003 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4186823973/10000000000 : ℝ), (110455623/200000000 : ℝ), (396533229/1250000000 : ℝ)] ![(31919383432083/100000000000000 : ℝ), (9179895658471/20000000000000 : ℝ), (11090569131003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4186823973/10000000000 : ℝ)|^2155 ≤ (31919383432083/100000000000000 : ℝ)^1643
        have hw : |(4186823973/10000000000 : ℝ)|=(4186823973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110455623/200000000 : ℝ)|^2155 ≤ (9179895658471/20000000000000 : ℝ)^1643
        have hw : |(110455623/200000000 : ℝ)|=(110455623/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(396533229/1250000000 : ℝ)|^2155 ≤ (11090569131003/50000000000000 : ℝ)^1643
        have hw : |(396533229/1250000000 : ℝ)|=(396533229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1350_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (737/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13407/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4309/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4309 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4309*1^1024 ≤ 0^1024*1^4309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4309 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4309/1024 : ℝ) ≤ (1057877399445414523/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4309 ≤ (1057877399445414523/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4309*50000000000000000000^1024 ≤ 1057877399445414523^1024*5^4309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1057877399445414523 50000000000000000000 4309 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1057877399445414523/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4309 := by
      have hnat : (1 : ℕ)^1024*1^4309 ≤ 1^4309*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (51057877399445414523/50000000000000000000 : ℝ) ≤ (10049878725460957/10000000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (51057877399445414523/50000000000000000000 : ℝ)^1024 ≤ (10049878725460957/10000000000000000 : ℝ)^4309 := by
      have hnat : (51057877399445414523 : ℕ)^1024*10000000000000000^4309 ≤ 10049878725460957^4309*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51057877399445414523 50000000000000000000 10049878725460957 10000000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10049878725460957/10000000000000000 : ℝ)) (X := (51057877399445414523/50000000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (26057877399445414523/25000000000000000000 : ℝ) ≤ (5049878725460957/5000000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (26057877399445414523/25000000000000000000 : ℝ)^1024 ≤ (5049878725460957/5000000000000000 : ℝ)^4309 := by
      have hnat : (26057877399445414523 : ℕ)^1024*5000000000000000^4309 ≤ 5049878725460957^4309*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26057877399445414523 25000000000000000000 5049878725460957 5000000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5049878725460957/5000000000000000 : ℝ)) (X := (26057877399445414523/25000000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(49878725460957/4000000000000000 : ℝ)*(0 : ℝ))^(4309/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(49878725460957/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1057877399445414523/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(49878725460957/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4309/1024 : ℝ) := by
    rw [show (1 : ℝ)+(49878725460957/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10049878725460957/10000000000000000 : ℝ) by norm_num, show 1+(1057877399445414523/50000000000000000000 : ℝ)+(0 : ℝ)=(51057877399445414523/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1057877399445414523/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(49878725460957/4000000000000000 : ℝ)*(2/5 : ℝ))^(4309/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(49878725460957/4000000000000000 : ℝ)*(2/5 : ℝ)=(5049878725460957/5000000000000000 : ℝ) by norm_num, show 1+2*(1057877399445414523/50000000000000000000 : ℝ)=(26057877399445414523/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(49878725460957/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49878725460957/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(49878725460957/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49878725460957/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(49878725460957/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49878725460957/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-72177053/400000000 : ℝ)*X 0 0+(5993468731/10000000000 : ℝ)*X 0 1+(75200221/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2750458441/5000000000 : ℝ)*X 1 0+(-2475115757/10000000000 : ℝ)*X 1 1+(1203203647/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((220036667/400000000 : ℝ)*X 2 0+(4812814249/10000000000 : ℝ)*X 2 1+(-61877911/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4177551563/10000000000 : ℝ)*X 0 0+(1553089069/5000000000 : ℝ)*X 0 1+(5586589341/10000000000 : ℝ)*X 0 2+(4177551563/10000000000 : ℝ)*X 1 0+(1553089069/5000000000 : ℝ)*X 1 1+(5586589341/10000000000 : ℝ)*X 1 2+(4177551563/10000000000 : ℝ)*X 2 0+(1553089069/5000000000 : ℝ)*X 2 1+(5586589341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1808841143/10000000000 : ℝ)*X 0 0+(2421593407/5000000000 : ℝ)*X 0 1+(119240227/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5179099747/10000000000 : ℝ)*X 1 0+(-132592017/1000000000 : ℝ)*X 1 1+(1490502751/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1294774923/2500000000 : ℝ)*X 2 0+(1192402279/2000000000 : ℝ)*X 2 1+(-132591963/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4186823973/10000000000 : ℝ)*X 0 0+(110455623/200000000 : ℝ)*X 0 1+(396533229/1250000000 : ℝ)*X 0 2+(4186823973/10000000000 : ℝ)*X 1 0+(110455623/200000000 : ℝ)*X 1 1+(396533229/1250000000 : ℝ)*X 1 2+(4186823973/10000000000 : ℝ)*X 2 0+(110455623/200000000 : ℝ)*X 2 1+(396533229/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (688506926107989549/125000000000000000000000 : ℝ) := by norm_num
    linear_combination (31489221/25000000000000 : ℝ)*(base1) + (1293752269/100000000000000 : ℝ)*(base19) + (1261879781/100000000000000 : ℝ)*(base23) + (112676831/50000000000000 : ℝ)*(upper3) + (20189729/50000000000000 : ℝ)*(upper5) + (625079498942431/100000000000000 : ℝ)*(major0) + (625079498942431/100000000000000 : ℝ)*(major1) + (625079498942431/100000000000000 : ℝ)*(major2) + (169398488571431/20000000000000 : ℝ)*(sp0) + (423497350795071/50000000000000 : ℝ)*(sp1) + (84699473346263/10000000000000 : ℝ)*(sp2) + (80632105857187/20000000000000 : ℝ)*(sp3) + (3678442139/100000000000000 : ℝ)*(sp4) + (2163697781/100000000000000 : ℝ)*(sp7) + (2015814094703/500000000000 : ℝ)*(f.failure) + (846995995342411/100000000000000 : ℝ)*(f.sum) + (519953532033533/200000000000000000000000000000 : ℝ)*base66 + (2993117428766467/400000000000000000000000000000 : ℝ)*base67 + (1019428242366467/400000000000000000000000000000 : ℝ)*base69 + (1612104543633533/400000000000000000000000000000 : ℝ)*base72 + (910984543966467/200000000000000000000000000000 : ℝ)*base73 + (290342831966467/400000000000000000000000000000 : ℝ)*base75 + (605615746033533/400000000000000000000000000000 : ℝ)*base78 + (467461661166467/400000000000000000000000000000 : ℝ)*base79 + (45545604233533/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (55261/10000000000000000000 : ℝ)*base89 + (55261/10000000000000000000 : ℝ)*base91 + (55261/10000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (863713343787851090139243/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1792780421/100000000000000 : ℝ)*(base19) + (1877075719/100000000000000 : ℝ)*(base23) + (3579237/5000000000000 : ℝ)*(base39) + (57177537/25000000000000 : ℝ)*(upper3) + (229772487/100000000000000 : ℝ)*(upper5) + (659616806660467/100000000000000 : ℝ)*(major0) + (659616806660467/100000000000000 : ℝ)*(major1) + (41226045942233/6250000000000 : ℝ)*(major2) + (2020052069/50000000000000 : ℝ)*(sp1) + (553143967/12500000000000 : ℝ)*(sp2) + (111724326874573/12500000000000 : ℝ)*(sp4) + (35751551284481/4000000000000 : ℝ)*(sp5) + (893788384353869/100000000000000 : ℝ)*(sp6) + (212719319417579/50000000000000 : ℝ)*(sp7) + (212719319417579/50000000000000 : ℝ)*(f.failure) + (223448671645331/25000000000000 : ℝ)*(f.sum) + (136450915487723/80000000000000000000000000000 : ℝ)*base65 + (30935558003019/25000000000000000000000000000 : ℝ)*base68 + (177032421486919/400000000000000000000000000000 : ℝ)*base69 + (131724134228019/25000000000000000000000000000 : ℝ)*base72 + (523495894527723/80000000000000000000000000000 : ℝ)*base73 + (258208483886919/400000000000000000000000000000 : ℝ)*base75 + (2547447188913081/400000000000000000000000000000 : ℝ)*base78 + (2316945723713081/400000000000000000000000000000 : ℝ)*base80 + (793805734686919/200000000000000000000000000000 : ℝ)*base81 + (1266673/1000000000000000000000 : ℝ)*base89 + (1266673/1000000000000000000000 : ℝ)*base91 + (8733327/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1350_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (737/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13407/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1350_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1350_s1_0 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-397617009/2000000000 : ℝ)*x 0 + (2819285567/5000000000 : ℝ)*x 1 + (5050086699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (397617009/2000000000 : ℝ)^2155 ≤ (2403475473191/20000000000000 : ℝ)^1643 := by
    have hnat : (397617009 : ℕ)^2155*20000000000000^1643 ≤ 2403475473191^1643*2000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397617009 2000000000 2403475473191 20000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2819285567/5000000000 : ℝ)^2155 ≤ (4716578904593/10000000000000 : ℝ)^1643 := by
    have hnat : (2819285567 : ℕ)^2155*10000000000000^1643 ≤ 4716578904593^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2819285567 5000000000 4716578904593 10000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5050086699/10000000000 : ℝ)^2155 ≤ (40816833575557/100000000000000 : ℝ)^1643 := by
    have hnat : (5050086699 : ℕ)^2155*100000000000000^1643 ≤ 40816833575557^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5050086699 10000000000 40816833575557 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-397617009/2000000000 : ℝ), (2819285567/5000000000 : ℝ), (5050086699/10000000000 : ℝ)] ![(2403475473191/20000000000000 : ℝ), (4716578904593/10000000000000 : ℝ), (40816833575557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-397617009/2000000000 : ℝ)|^2155 ≤ (2403475473191/20000000000000 : ℝ)^1643
        have hw : |(-397617009/2000000000 : ℝ)|=(397617009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2819285567/5000000000 : ℝ)|^2155 ≤ (4716578904593/10000000000000 : ℝ)^1643
        have hw : |(2819285567/5000000000 : ℝ)|=(2819285567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5050086699/10000000000 : ℝ)|^2155 ≤ (40816833575557/100000000000000 : ℝ)^1643
        have hw : |(5050086699/10000000000 : ℝ)|=(5050086699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s1_1 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (540488641/1000000000 : ℝ)*x 0 + (-460380113/2000000000 : ℝ)*x 1 + (5050087111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540488641/1000000000 : ℝ)^2155 ≤ (44618623302173/100000000000000 : ℝ)^1643 := by
    have hnat : (540488641 : ℕ)^2155*100000000000000^1643 ≤ 44618623302173^1643*1000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540488641 1000000000 44618623302173 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (460380113/2000000000 : ℝ)^2155 ≤ (14564538741713/100000000000000 : ℝ)^1643 := by
    have hnat : (460380113 : ℕ)^2155*100000000000000^1643 ≤ 14564538741713^1643*2000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460380113 2000000000 14564538741713 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5050087111/10000000000 : ℝ)^2155 ≤ (40816837943203/100000000000000 : ℝ)^1643 := by
    have hnat : (5050087111 : ℕ)^2155*100000000000000^1643 ≤ 40816837943203^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5050087111 10000000000 40816837943203 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540488641/1000000000 : ℝ), (-460380113/2000000000 : ℝ), (5050087111/10000000000 : ℝ)] ![(44618623302173/100000000000000 : ℝ), (14564538741713/100000000000000 : ℝ), (40816837943203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540488641/1000000000 : ℝ)|^2155 ≤ (44618623302173/100000000000000 : ℝ)^1643
        have hw : |(540488641/1000000000 : ℝ)|=(540488641/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-460380113/2000000000 : ℝ)|^2155 ≤ (14564538741713/100000000000000 : ℝ)^1643
        have hw : |(-460380113/2000000000 : ℝ)|=(460380113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5050087111/10000000000 : ℝ)|^2155 ≤ (40816837943203/100000000000000 : ℝ)^1643
        have hw : |(5050087111/10000000000 : ℝ)|=(5050087111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s1_2 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (675610797/1250000000 : ℝ)*x 0 + (5050086741/10000000000 : ℝ)*x 1 + (-1150950541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675610797/1250000000 : ℝ)^2155 ≤ (11154655733507/25000000000000 : ℝ)^1643 := by
    have hnat : (675610797 : ℕ)^2155*25000000000000^1643 ≤ 11154655733507^1643*1250000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675610797 1250000000 11154655733507 25000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5050086741/10000000000 : ℝ)^2155 ≤ (40816834020803/100000000000000 : ℝ)^1643 := by
    have hnat : (5050086741 : ℕ)^2155*100000000000000^1643 ≤ 40816834020803^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5050086741 10000000000 40816834020803 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1150950541/5000000000 : ℝ)^2155 ≤ (7282271516119/50000000000000 : ℝ)^1643 := by
    have hnat : (1150950541 : ℕ)^2155*50000000000000^1643 ≤ 7282271516119^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1150950541 5000000000 7282271516119 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675610797/1250000000 : ℝ), (5050086741/10000000000 : ℝ), (-1150950541/5000000000 : ℝ)] ![(11154655733507/25000000000000 : ℝ), (40816834020803/100000000000000 : ℝ), (7282271516119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675610797/1250000000 : ℝ)|^2155 ≤ (11154655733507/25000000000000 : ℝ)^1643
        have hw : |(675610797/1250000000 : ℝ)|=(675610797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5050086741/10000000000 : ℝ)|^2155 ≤ (40816834020803/100000000000000 : ℝ)^1643
        have hw : |(5050086741/10000000000 : ℝ)|=(5050086741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1150950541/5000000000 : ℝ)|^2155 ≤ (7282271516119/50000000000000 : ℝ)^1643
        have hw : |(-1150950541/5000000000 : ℝ)|=(1150950541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s1_3 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4290879081/10000000000 : ℝ)*x 0 + (92845891/250000000 : ℝ)*x 1 + (990033537/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4290879081/10000000000 : ℝ)^2155 ≤ (32963891910667/100000000000000 : ℝ)^1643 := by
    have hnat : (4290879081 : ℕ)^2155*100000000000000^1643 ≤ 32963891910667^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4290879081 10000000000 32963891910667 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (92845891/250000000 : ℝ)^2155 ≤ (27275243688573/100000000000000 : ℝ)^1643 := by
    have hnat : (92845891 : ℕ)^2155*100000000000000^1643 ≤ 27275243688573^1643*250000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92845891 250000000 27275243688573 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (990033537/2000000000 : ℝ)^2155 ≤ (39760864382849/100000000000000 : ℝ)^1643 := by
    have hnat : (990033537 : ℕ)^2155*100000000000000^1643 ≤ 39760864382849^1643*2000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990033537 2000000000 39760864382849 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4290879081/10000000000 : ℝ), (92845891/250000000 : ℝ), (990033537/2000000000 : ℝ)] ![(32963891910667/100000000000000 : ℝ), (27275243688573/100000000000000 : ℝ), (39760864382849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4290879081/10000000000 : ℝ)|^2155 ≤ (32963891910667/100000000000000 : ℝ)^1643
        have hw : |(4290879081/10000000000 : ℝ)|=(4290879081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(92845891/250000000 : ℝ)|^2155 ≤ (27275243688573/100000000000000 : ℝ)^1643
        have hw : |(92845891/250000000 : ℝ)|=(92845891/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(990033537/2000000000 : ℝ)|^2155 ≤ (39760864382849/100000000000000 : ℝ)^1643
        have hw : |(990033537/2000000000 : ℝ)|=(990033537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s1_4 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-124287951/625000000 : ℝ)*x 0 + (2528712919/5000000000 : ℝ)*x 1 + (1126219861/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (124287951/625000000 : ℝ)^2155 ≤ (3005379376357/25000000000000 : ℝ)^1643 := by
    have hnat : (124287951 : ℕ)^2155*25000000000000^1643 ≤ 3005379376357^1643*625000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124287951 625000000 3005379376357 25000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2528712919/5000000000 : ℝ)^2155 ≤ (40894654000419/100000000000000 : ℝ)^1643 := by
    have hnat : (2528712919 : ℕ)^2155*100000000000000^1643 ≤ 40894654000419^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2528712919 5000000000 40894654000419 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126219861/2000000000 : ℝ)^2155 ≤ (47083828476003/100000000000000 : ℝ)^1643 := by
    have hnat : (1126219861 : ℕ)^2155*100000000000000^1643 ≤ 47083828476003^1643*2000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126219861 2000000000 47083828476003 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-124287951/625000000 : ℝ), (2528712919/5000000000 : ℝ), (1126219861/2000000000 : ℝ)] ![(3005379376357/25000000000000 : ℝ), (40894654000419/100000000000000 : ℝ), (47083828476003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-124287951/625000000 : ℝ)|^2155 ≤ (3005379376357/25000000000000 : ℝ)^1643
        have hw : |(-124287951/625000000 : ℝ)|=(124287951/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2528712919/5000000000 : ℝ)|^2155 ≤ (40894654000419/100000000000000 : ℝ)^1643
        have hw : |(2528712919/5000000000 : ℝ)|=(2528712919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126219861/2000000000 : ℝ)|^2155 ≤ (47083828476003/100000000000000 : ℝ)^1643
        have hw : |(1126219861/2000000000 : ℝ)|=(1126219861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s1_5 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5252081131/10000000000 : ℝ)*x 0 + (-172088813/1000000000 : ℝ)*x 1 + (2815549677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252081131/10000000000 : ℝ)^2155 ≤ (42971418052927/100000000000000 : ℝ)^1643 := by
    have hnat : (5252081131 : ℕ)^2155*100000000000000^1643 ≤ 42971418052927^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252081131 10000000000 42971418052927 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172088813/1000000000 : ℝ)^2155 ≤ (9944752909909/100000000000000 : ℝ)^1643 := by
    have hnat : (172088813 : ℕ)^2155*100000000000000^1643 ≤ 9944752909909^1643*1000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172088813 1000000000 9944752909909 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2815549677/5000000000 : ℝ)^2155 ≤ (23541914506693/50000000000000 : ℝ)^1643 := by
    have hnat : (2815549677 : ℕ)^2155*50000000000000^1643 ≤ 23541914506693^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2815549677 5000000000 23541914506693 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252081131/10000000000 : ℝ), (-172088813/1000000000 : ℝ), (2815549677/5000000000 : ℝ)] ![(42971418052927/100000000000000 : ℝ), (9944752909909/100000000000000 : ℝ), (23541914506693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252081131/10000000000 : ℝ)|^2155 ≤ (42971418052927/100000000000000 : ℝ)^1643
        have hw : |(5252081131/10000000000 : ℝ)|=(5252081131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-172088813/1000000000 : ℝ)|^2155 ≤ (9944752909909/100000000000000 : ℝ)^1643
        have hw : |(-172088813/1000000000 : ℝ)|=(172088813/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2815549677/5000000000 : ℝ)|^2155 ≤ (23541914506693/50000000000000 : ℝ)^1643
        have hw : |(2815549677/5000000000 : ℝ)|=(2815549677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s1_6 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5252081029/10000000000 : ℝ)*x 0 + (2815549713/5000000000 : ℝ)*x 1 + (-1720888171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252081029/10000000000 : ℝ)^2155 ≤ (537142711979/1250000000000 : ℝ)^1643 := by
    have hnat : (5252081029 : ℕ)^2155*1250000000000^1643 ≤ 537142711979^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252081029 10000000000 537142711979 1250000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2815549713/5000000000 : ℝ)^2155 ≤ (47083829803011/100000000000000 : ℝ)^1643 := by
    have hnat : (2815549713 : ℕ)^2155*100000000000000^1643 ≤ 47083829803011^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2815549713 5000000000 47083829803011 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1720888171/10000000000 : ℝ)^2155 ≤ (2486188305169/25000000000000 : ℝ)^1643 := by
    have hnat : (1720888171 : ℕ)^2155*25000000000000^1643 ≤ 2486188305169^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1720888171 10000000000 2486188305169 25000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252081029/10000000000 : ℝ), (2815549713/5000000000 : ℝ), (-1720888171/10000000000 : ℝ)] ![(537142711979/1250000000000 : ℝ), (47083829803011/100000000000000 : ℝ), (2486188305169/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252081029/10000000000 : ℝ)|^2155 ≤ (537142711979/1250000000000 : ℝ)^1643
        have hw : |(5252081029/10000000000 : ℝ)|=(5252081029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2815549713/5000000000 : ℝ)|^2155 ≤ (47083829803011/100000000000000 : ℝ)^1643
        have hw : |(2815549713/5000000000 : ℝ)|=(2815549713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1720888171/10000000000 : ℝ)|^2155 ≤ (2486188305169/25000000000000 : ℝ)^1643
        have hw : |(-1720888171/10000000000 : ℝ)|=(1720888171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s1_7 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2145988241/5000000000 : ℝ)*x 0 + (4934749839/10000000000 : ℝ)*x 1 + (3729531337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2145988241/5000000000 : ℝ)^2155 ≤ (32974950114043/100000000000000 : ℝ)^1643 := by
    have hnat : (2145988241 : ℕ)^2155*100000000000000^1643 ≤ 32974950114043^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145988241 5000000000 32974950114043 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4934749839/10000000000 : ℝ)^2155 ≤ (39598512115657/100000000000000 : ℝ)^1643 := by
    have hnat : (4934749839 : ℕ)^2155*100000000000000^1643 ≤ 39598512115657^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4934749839 10000000000 39598512115657 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3729531337/10000000000 : ℝ)^2155 ≤ (3428317219217/12500000000000 : ℝ)^1643 := by
    have hnat : (3729531337 : ℕ)^2155*12500000000000^1643 ≤ 3428317219217^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3729531337 10000000000 3428317219217 12500000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2145988241/5000000000 : ℝ), (4934749839/10000000000 : ℝ), (3729531337/10000000000 : ℝ)] ![(32974950114043/100000000000000 : ℝ), (39598512115657/100000000000000 : ℝ), (3428317219217/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2145988241/5000000000 : ℝ)|^2155 ≤ (32974950114043/100000000000000 : ℝ)^1643
        have hw : |(2145988241/5000000000 : ℝ)|=(2145988241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4934749839/10000000000 : ℝ)|^2155 ≤ (39598512115657/100000000000000 : ℝ)^1643
        have hw : |(4934749839/10000000000 : ℝ)|=(4934749839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3729531337/10000000000 : ℝ)|^2155 ≤ (3428317219217/12500000000000 : ℝ)^1643
        have hw : |(3729531337/10000000000 : ℝ)|=(3729531337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1350_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13407/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (737/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1741/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9701/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13407/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (737/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13407/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (737/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13407/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (737/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13407/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (737/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13407/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (737/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13407/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (737/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (737/50000 : ℝ) ^ (4309/1024 : ℝ) ≤ (245433089933/12500000000000000000 : ℝ) := by
    have hpowers : (737/50000 : ℝ)^4309 ≤ (245433089933/12500000000000000000 : ℝ)^1024 := by
      have hnat : (737 : ℕ)^4309*12500000000000000000^1024 ≤ 245433089933^1024*50000^4309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        737 50000 245433089933 12500000000000000000 4309 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (737/50000 : ℝ)) (X := (245433089933/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13407/50000 : ℝ) ^ (4309/1024 : ℝ) ≤ (78626901912390667/20000000000000000000 : ℝ) := by
    have hpowers : (13407/50000 : ℝ)^4309 ≤ (78626901912390667/20000000000000000000 : ℝ)^1024 := by
      have hnat : (13407 : ℕ)^4309*20000000000000000000^1024 ≤ 78626901912390667^1024*50000^4309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13407 50000 78626901912390667 20000000000000000000 4309 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13407/50000 : ℝ)) (X := (78626901912390667/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250000245433089933/6250000000000000000 : ℝ) ≤ (1250000011665049/1250000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (6250000245433089933/6250000000000000000 : ℝ)^1024 ≤ (1250000011665049/1250000000000000 : ℝ)^4309 := by
      have hnat : (6250000245433089933 : ℕ)^1024*1250000000000000^4309 ≤ 1250000011665049^4309*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250000245433089933 6250000000000000000 1250000011665049 1250000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000011665049/1250000000000000 : ℝ)) (X := (6250000245433089933/6250000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100393136473026672799/100000000000000000000 : ℝ) ≤ (10009328611339219/10000000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (100393136473026672799/100000000000000000000 : ℝ)^1024 ≤ (10009328611339219/10000000000000000 : ℝ)^4309 := by
      have hnat : (100393136473026672799 : ℕ)^1024*10000000000000000^4309 ≤ 10009328611339219^4309*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100393136473026672799 100000000000000000000 10009328611339219 10000000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009328611339219/10000000000000000 : ℝ)) (X := (100393136473026672799/100000000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10078626901912390667/10000000000000000000 : ℝ) ≤ (5009328564679023/5000000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (10078626901912390667/10000000000000000000 : ℝ)^1024 ≤ (5009328564679023/5000000000000000 : ℝ)^4309 := by
      have hnat : (10078626901912390667 : ℕ)^1024*5000000000000000^4309 ≤ 5009328564679023^4309*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10078626901912390667 10000000000000000000 5009328564679023 5000000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5009328564679023/5000000000000000 : ℝ)) (X := (10078626901912390667/10000000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(245433089933/12500000000000000000 : ℝ) ≤ ((9049017924772115403/9050000000000000000 : ℝ)+2*(1332645431261/362000000000000 : ℝ)*(737/50000 : ℝ))^(4309/1024 : ℝ) := by
    rw [show (9049017924772115403/9050000000000000000 : ℝ)+2*(1332645431261/362000000000000 : ℝ)*(737/50000 : ℝ)=(1250000011665049/1250000000000000 : ℝ) by norm_num, show 1+2*(245433089933/12500000000000000000 : ℝ)=(6250000245433089933/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(78626901912390667/20000000000000000000 : ℝ)+(245433089933/12500000000000000000 : ℝ) ≤ ((9049017924772115403/9050000000000000000 : ℝ)+(1332645431261/362000000000000 : ℝ)*((13407/50000 : ℝ)+(737/50000 : ℝ)))^(4309/1024 : ℝ) := by
    rw [show (9049017924772115403/9050000000000000000 : ℝ)+(1332645431261/362000000000000 : ℝ)*((13407/50000 : ℝ)+(737/50000 : ℝ))=(10009328611339219/10000000000000000 : ℝ) by norm_num, show 1+(78626901912390667/20000000000000000000 : ℝ)+(245433089933/12500000000000000000 : ℝ)=(100393136473026672799/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(78626901912390667/20000000000000000000 : ℝ) ≤ ((9049017924772115403/9050000000000000000 : ℝ)+2*(1332645431261/362000000000000 : ℝ)*(13407/50000 : ℝ))^(4309/1024 : ℝ) := by
    rw [show (9049017924772115403/9050000000000000000 : ℝ)+2*(1332645431261/362000000000000 : ℝ)*(13407/50000 : ℝ)=(5009328564679023/5000000000000000 : ℝ) by norm_num, show 1+2*(78626901912390667/20000000000000000000 : ℝ)=(10078626901912390667/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9049017924772115403/9050000000000000000 : ℝ)*(X 1 0+X 2 0)+(1332645431261/362000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (737/50000 : ℝ)) (hi := (13407/50000 : ℝ)) (c := (9049017924772115403/9050000000000000000 : ℝ)) (alpha := (1332645431261/362000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9049017924772115403/9050000000000000000 : ℝ)*(X 0 1+X 2 1)+(1332645431261/362000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (737/50000 : ℝ)) (hi := (13407/50000 : ℝ)) (c := (9049017924772115403/9050000000000000000 : ℝ)) (alpha := (1332645431261/362000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9049017924772115403/9050000000000000000 : ℝ)*(X 0 2+X 1 2)+(1332645431261/362000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (737/50000 : ℝ)) (hi := (13407/50000 : ℝ)) (c := (9049017924772115403/9050000000000000000 : ℝ)) (alpha := (1332645431261/362000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-397617009/2000000000 : ℝ)*X 0 0+(2819285567/5000000000 : ℝ)*X 0 1+(5050086699/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((540488641/1000000000 : ℝ)*X 1 0+(-460380113/2000000000 : ℝ)*X 1 1+(5050087111/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((675610797/1250000000 : ℝ)*X 2 0+(5050086741/10000000000 : ℝ)*X 2 1+(-1150950541/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4290879081/10000000000 : ℝ)*X 0 0+(92845891/250000000 : ℝ)*X 0 1+(990033537/2000000000 : ℝ)*X 0 2+(4290879081/10000000000 : ℝ)*X 1 0+(92845891/250000000 : ℝ)*X 1 1+(990033537/2000000000 : ℝ)*X 1 2+(4290879081/10000000000 : ℝ)*X 2 0+(92845891/250000000 : ℝ)*X 2 1+(990033537/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-124287951/625000000 : ℝ)*X 0 0+(2528712919/5000000000 : ℝ)*X 0 1+(1126219861/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5252081131/10000000000 : ℝ)*X 1 0+(-172088813/1000000000 : ℝ)*X 1 1+(2815549677/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5252081029/10000000000 : ℝ)*X 2 0+(2815549713/5000000000 : ℝ)*X 2 1+(-1720888171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2145988241/5000000000 : ℝ)*X 0 0+(4934749839/10000000000 : ℝ)*X 0 1+(3729531337/10000000000 : ℝ)*X 0 2+(2145988241/5000000000 : ℝ)*X 1 0+(4934749839/10000000000 : ℝ)*X 1 1+(3729531337/10000000000 : ℝ)*X 1 2+(2145988241/5000000000 : ℝ)*X 2 0+(4934749839/10000000000 : ℝ)*X 2 1+(3729531337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (881971421165993416451961963/226250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5725619/12500000000000 : ℝ)*(base16) + (400629811/100000000000000 : ℝ)*(base19) + (17686471/4000000000000 : ℝ)*(base23) + (433509/12500000000000 : ℝ)*(upper2) + (43140367/50000000000000 : ℝ)*(upper3) + (1254066390439007/100000000000000 : ℝ)*(major0) + (1254066390439007/100000000000000 : ℝ)*(major1) + (1254066390439007/100000000000000 : ℝ)*(major2) + (212410511749563/12500000000000 : ℝ)*(sp0) + (849643191274857/50000000000000 : ℝ)*(sp1) + (849643193411351/50000000000000 : ℝ)*(sp2) + (40442241095927/5000000000000 : ℝ)*(sp3) + (2734987973/100000000000000 : ℝ)*(sp4) + (1000034449/100000000000000 : ℝ)*(sp7) + (202211455488247/25000000000000 : ℝ)*(f.failure) + (1699286828984477/100000000000000 : ℝ)*(f.sum) + (18305285413173/18100000000000000000000000000 : ℝ)*base66 + (8095219927822600179/905000000000000000000000000000000 : ℝ)*base68 + (643789444212399821/905000000000000000000000000000000 : ℝ)*base69 + (2646708765507600179/905000000000000000000000000000000 : ℝ)*base72 + (76670302710273/18100000000000000000000000000 : ℝ)*base74 + (9710837915452600179/905000000000000000000000000000000 : ℝ)*base76 + (492194462367600179/905000000000000000000000000000000 : ℝ)*base78 + (10871065133982600179/905000000000000000000000000000000 : ℝ)*base80 + (44044683450927/18100000000000000000000000000 : ℝ)*base81 + (2773611/500000000000000000000 : ℝ)*base90 + (2773611/500000000000000000000 : ℝ)*base92 + (2773611/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1713462441247368523657304667/226250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82733541/100000000000000 : ℝ)*(base1) + (1547609251/100000000000000 : ℝ)*(base19) + (755561551/50000000000000 : ℝ)*(base23) + (87654641/50000000000000 : ℝ)*(upper3) + (166699687/100000000000000 : ℝ)*(upper5) + (643219262259479/50000000000000 : ℝ)*(major0) + (643219262259479/50000000000000 : ℝ)*(major1) + (643219262259479/50000000000000 : ℝ)*(major2) + (3982525273/50000000000000 : ℝ)*(sp1) + (3937279963/50000000000000 : ℝ)*(sp2) + (1743151727860751/100000000000000 : ℝ)*(sp4) + (435785533116853/25000000000000 : ℝ)*(sp5) + (871571129722091/50000000000000 : ℝ)*(sp6) + (829725068733337/100000000000000 : ℝ)*(sp7) + (414862575733439/50000000000000 : ℝ)*(f.failure) + (174315164512721/10000000000000 : ℝ)*(f.sum) + (13476249150119/9050000000000000000000000000 : ℝ)*base65 + (1003830836491630037/452500000000000000000000000000000 : ℝ)*base67 + (2770484710784130037/452500000000000000000000000000000 : ℝ)*base69 + (2136847312779130037/452500000000000000000000000000000 : ℝ)*base71 + (539242701369/9050000000000000000000000000 : ℝ)*base73 + (5999304615236630037/452500000000000000000000000000000 : ℝ)*base75 + (3347959661324130037/452500000000000000000000000000000 : ℝ)*base77 + (4049926733591630037/452500000000000000000000000000000 : ℝ)*base79 + (2483492012269/9050000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1271507/1000000000000000000000 : ℝ)*base90 + (1271507/1000000000000000000000 : ℝ)*base92 + (1271507/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1350_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13407/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (737/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1741/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9701/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1350_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1350_s2_0 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-253443623/1250000000 : ℝ)*x 0 + (342348887/625000000 : ℝ)*x 1 + (1037157077/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (253443623/1250000000 : ℝ)^2155 ≤ (12331225822047/100000000000000 : ℝ)^1643 := by
    have hnat : (253443623 : ℕ)^2155*100000000000000^1643 ≤ 12331225822047^1643*1250000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253443623 1250000000 12331225822047 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342348887/625000000 : ℝ)^2155 ≤ (22703700771323/50000000000000 : ℝ)^1643 := by
    have hnat : (342348887 : ℕ)^2155*50000000000000^1643 ≤ 22703700771323^1643*625000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342348887 625000000 22703700771323 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037157077/2000000000 : ℝ)^2155 ≤ (5282671578031/12500000000000 : ℝ)^1643 := by
    have hnat : (1037157077 : ℕ)^2155*12500000000000^1643 ≤ 5282671578031^1643*2000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037157077 2000000000 5282671578031 12500000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-253443623/1250000000 : ℝ), (342348887/625000000 : ℝ), (1037157077/2000000000 : ℝ)] ![(12331225822047/100000000000000 : ℝ), (22703700771323/50000000000000 : ℝ), (5282671578031/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-253443623/1250000000 : ℝ)|^2155 ≤ (12331225822047/100000000000000 : ℝ)^1643
        have hw : |(-253443623/1250000000 : ℝ)|=(253443623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(342348887/625000000 : ℝ)|^2155 ≤ (22703700771323/50000000000000 : ℝ)^1643
        have hw : |(342348887/625000000 : ℝ)|=(342348887/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1037157077/2000000000 : ℝ)|^2155 ≤ (5282671578031/12500000000000 : ℝ)^1643
        have hw : |(1037157077/2000000000 : ℝ)|=(1037157077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s2_1 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5365393793/10000000000 : ℝ)*x 0 + (-2178256849/10000000000 : ℝ)*x 1 + (5185785773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5365393793/10000000000 : ℝ)^2155 ≤ (44191493708609/100000000000000 : ℝ)^1643 := by
    have hnat : (5365393793 : ℕ)^2155*100000000000000^1643 ≤ 44191493708609^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5365393793 10000000000 44191493708609 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2178256849/10000000000 : ℝ)^2155 ≤ (1354712950521/10000000000000 : ℝ)^1643 := by
    have hnat : (2178256849 : ℕ)^2155*10000000000000^1643 ≤ 1354712950521^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178256849 10000000000 1354712950521 10000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5185785773/10000000000 : ℝ)^2155 ≤ (10565344192899/25000000000000 : ℝ)^1643 := by
    have hnat : (5185785773 : ℕ)^2155*25000000000000^1643 ≤ 10565344192899^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185785773 10000000000 10565344192899 25000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5365393793/10000000000 : ℝ), (-2178256849/10000000000 : ℝ), (5185785773/10000000000 : ℝ)] ![(44191493708609/100000000000000 : ℝ), (1354712950521/10000000000000 : ℝ), (10565344192899/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5365393793/10000000000 : ℝ)|^2155 ≤ (44191493708609/100000000000000 : ℝ)^1643
        have hw : |(5365393793/10000000000 : ℝ)|=(5365393793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2178256849/10000000000 : ℝ)|^2155 ≤ (1354712950521/10000000000000 : ℝ)^1643
        have hw : |(-2178256849/10000000000 : ℝ)|=(2178256849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5185785773/10000000000 : ℝ)|^2155 ≤ (10565344192899/25000000000000 : ℝ)^1643
        have hw : |(5185785773/10000000000 : ℝ)|=(5185785773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s2_2 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1341348467/2500000000 : ℝ)*x 0 + (5185785687/10000000000 : ℝ)*x 1 + (-2178256863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341348467/2500000000 : ℝ)^2155 ≤ (22095747259419/50000000000000 : ℝ)^1643 := by
    have hnat : (1341348467 : ℕ)^2155*50000000000000^1643 ≤ 22095747259419^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341348467 2500000000 22095747259419 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185785687/10000000000 : ℝ)^2155 ≤ (21130687926169/50000000000000 : ℝ)^1643 := by
    have hnat : (5185785687 : ℕ)^2155*50000000000000^1643 ≤ 21130687926169^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185785687 10000000000 21130687926169 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2178256863/10000000000 : ℝ)^2155 ≤ (13547129619413/100000000000000 : ℝ)^1643 := by
    have hnat : (2178256863 : ℕ)^2155*100000000000000^1643 ≤ 13547129619413^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178256863 10000000000 13547129619413 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341348467/2500000000 : ℝ), (5185785687/10000000000 : ℝ), (-2178256863/10000000000 : ℝ)] ![(22095747259419/50000000000000 : ℝ), (21130687926169/50000000000000 : ℝ), (13547129619413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341348467/2500000000 : ℝ)|^2155 ≤ (22095747259419/50000000000000 : ℝ)^1643
        have hw : |(1341348467/2500000000 : ℝ)|=(1341348467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185785687/10000000000 : ℝ)|^2155 ≤ (21130687926169/50000000000000 : ℝ)^1643
        have hw : |(5185785687/10000000000 : ℝ)|=(5185785687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2178256863/10000000000 : ℝ)|^2155 ≤ (13547129619413/100000000000000 : ℝ)^1643
        have hw : |(-2178256863/10000000000 : ℝ)|=(2178256863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s2_3 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4318501381/10000000000 : ℝ)*x 0 + (402209179/1000000000 : ℝ)*x 1 + (4635120707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318501381/10000000000 : ℝ)^2155 ≤ (6648500357359/20000000000000 : ℝ)^1643 := by
    have hnat : (4318501381 : ℕ)^2155*20000000000000^1643 ≤ 6648500357359^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318501381 10000000000 6648500357359 20000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402209179/1000000000 : ℝ)^2155 ≤ (3785291312691/12500000000000 : ℝ)^1643 := by
    have hnat : (402209179 : ℕ)^2155*12500000000000^1643 ≤ 3785291312691^1643*1000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402209179 1000000000 3785291312691 12500000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4635120707/10000000000 : ℝ)^2155 ≤ (36475167696773/100000000000000 : ℝ)^1643 := by
    have hnat : (4635120707 : ℕ)^2155*100000000000000^1643 ≤ 36475167696773^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4635120707 10000000000 36475167696773 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318501381/10000000000 : ℝ), (402209179/1000000000 : ℝ), (4635120707/10000000000 : ℝ)] ![(6648500357359/20000000000000 : ℝ), (3785291312691/12500000000000 : ℝ), (36475167696773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318501381/10000000000 : ℝ)|^2155 ≤ (6648500357359/20000000000000 : ℝ)^1643
        have hw : |(4318501381/10000000000 : ℝ)|=(4318501381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(402209179/1000000000 : ℝ)|^2155 ≤ (3785291312691/12500000000000 : ℝ)^1643
        have hw : |(402209179/1000000000 : ℝ)|=(402209179/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4635120707/10000000000 : ℝ)|^2155 ≤ (36475167696773/100000000000000 : ℝ)^1643
        have hw : |(4635120707/10000000000 : ℝ)|=(4635120707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s2_4 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-40552253/200000000 : ℝ)*x 0 + (2593799917/5000000000 : ℝ)*x 1 + (5475751531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40552253/200000000 : ℝ)^2155 ≤ (6165866847039/50000000000000 : ℝ)^1643 := by
    have hnat : (40552253 : ℕ)^2155*50000000000000^1643 ≤ 6165866847039^1643*200000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40552253 200000000 6165866847039 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593799917/5000000000 : ℝ)^2155 ≤ (528509605031/1250000000000 : ℝ)^1643 := by
    have hnat : (2593799917 : ℕ)^2155*1250000000000^1643 ≤ 528509605031^1643*5000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593799917 5000000000 528509605031 1250000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5475751531/10000000000 : ℝ)^2155 ≤ (22693748945323/50000000000000 : ℝ)^1643 := by
    have hnat : (5475751531 : ℕ)^2155*50000000000000^1643 ≤ 22693748945323^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475751531 10000000000 22693748945323 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-40552253/200000000 : ℝ), (2593799917/5000000000 : ℝ), (5475751531/10000000000 : ℝ)] ![(6165866847039/50000000000000 : ℝ), (528509605031/1250000000000 : ℝ), (22693748945323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-40552253/200000000 : ℝ)|^2155 ≤ (6165866847039/50000000000000 : ℝ)^1643
        have hw : |(-40552253/200000000 : ℝ)|=(40552253/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593799917/5000000000 : ℝ)|^2155 ≤ (528509605031/1250000000000 : ℝ)^1643
        have hw : |(2593799917/5000000000 : ℝ)|=(2593799917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5475751531/10000000000 : ℝ)|^2155 ≤ (22693748945323/50000000000000 : ℝ)^1643
        have hw : |(5475751531/10000000000 : ℝ)|=(5475751531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s2_5 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5290118227/10000000000 : ℝ)*x 0 + (-1888290793/10000000000 : ℝ)*x 1 + (5475751509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290118227/10000000000 : ℝ)^2155 ≤ (43380070694807/100000000000000 : ℝ)^1643 := by
    have hnat : (5290118227 : ℕ)^2155*100000000000000^1643 ≤ 43380070694807^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290118227 10000000000 43380070694807 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1888290793/10000000000 : ℝ)^2155 ≤ (11232431632061/100000000000000 : ℝ)^1643 := by
    have hnat : (1888290793 : ℕ)^2155*100000000000000^1643 ≤ 11232431632061^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888290793 10000000000 11232431632061 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5475751509/10000000000 : ℝ)^2155 ≤ (22693748825733/50000000000000 : ℝ)^1643 := by
    have hnat : (5475751509 : ℕ)^2155*50000000000000^1643 ≤ 22693748825733^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475751509 10000000000 22693748825733 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290118227/10000000000 : ℝ), (-1888290793/10000000000 : ℝ), (5475751509/10000000000 : ℝ)] ![(43380070694807/100000000000000 : ℝ), (11232431632061/100000000000000 : ℝ), (22693748825733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290118227/10000000000 : ℝ)|^2155 ≤ (43380070694807/100000000000000 : ℝ)^1643
        have hw : |(5290118227/10000000000 : ℝ)|=(5290118227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1888290793/10000000000 : ℝ)|^2155 ≤ (11232431632061/100000000000000 : ℝ)^1643
        have hw : |(-1888290793/10000000000 : ℝ)|=(1888290793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5475751509/10000000000 : ℝ)|^2155 ≤ (22693748825733/50000000000000 : ℝ)^1643
        have hw : |(5475751509/10000000000 : ℝ)|=(5475751509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s2_6 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (264505911/500000000 : ℝ)*x 0 + (5475751537/10000000000 : ℝ)*x 1 + (-472072691/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264505911/500000000 : ℝ)^2155 ≤ (21690035309759/50000000000000 : ℝ)^1643 := by
    have hnat : (264505911 : ℕ)^2155*50000000000000^1643 ≤ 21690035309759^1643*500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264505911 500000000 21690035309759 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5475751537/10000000000 : ℝ)^2155 ≤ (45387497955877/100000000000000 : ℝ)^1643 := by
    have hnat : (5475751537 : ℕ)^2155*100000000000000^1643 ≤ 45387497955877^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475751537 10000000000 45387497955877 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (472072691/2500000000 : ℝ)^2155 ≤ (5616215702899/50000000000000 : ℝ)^1643 := by
    have hnat : (472072691 : ℕ)^2155*50000000000000^1643 ≤ 5616215702899^1643*2500000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472072691 2500000000 5616215702899 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264505911/500000000 : ℝ), (5475751537/10000000000 : ℝ), (-472072691/2500000000 : ℝ)] ![(21690035309759/50000000000000 : ℝ), (45387497955877/100000000000000 : ℝ), (5616215702899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264505911/500000000 : ℝ)|^2155 ≤ (21690035309759/50000000000000 : ℝ)^1643
        have hw : |(264505911/500000000 : ℝ)|=(264505911/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5475751537/10000000000 : ℝ)|^2155 ≤ (45387497955877/100000000000000 : ℝ)^1643
        have hw : |(5475751537/10000000000 : ℝ)|=(5475751537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-472072691/2500000000 : ℝ)|^2155 ≤ (5616215702899/50000000000000 : ℝ)^1643
        have hw : |(-472072691/2500000000 : ℝ)|=(472072691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1350_s2_7 (p : ℝ) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4318635473/10000000000 : ℝ)*x 0 + (926261879/2000000000 : ℝ)*x 1 + (4025937189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318635473/10000000000 : ℝ)^2155 ≤ (16621927825831/50000000000000 : ℝ)^1643 := by
    have hnat : (4318635473 : ℕ)^2155*50000000000000^1643 ≤ 16621927825831^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318635473 10000000000 16621927825831 50000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (926261879/2000000000 : ℝ)^2155 ≤ (36435833996291/100000000000000 : ℝ)^1643 := by
    have hnat : (926261879 : ℕ)^2155*100000000000000^1643 ≤ 36435833996291^1643*2000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926261879 2000000000 36435833996291 100000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4025937189/10000000000 : ℝ)^2155 ≤ (6064062068017/20000000000000 : ℝ)^1643 := by
    have hnat : (4025937189 : ℕ)^2155*20000000000000^1643 ≤ 6064062068017^1643*10000000000^2155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025937189 10000000000 6064062068017 20000000000000 2155 1643 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2155/512 : ℝ)) 2155 1643 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318635473/10000000000 : ℝ), (926261879/2000000000 : ℝ), (4025937189/10000000000 : ℝ)] ![(16621927825831/50000000000000 : ℝ), (36435833996291/100000000000000 : ℝ), (6064062068017/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318635473/10000000000 : ℝ)|^2155 ≤ (16621927825831/50000000000000 : ℝ)^1643
        have hw : |(4318635473/10000000000 : ℝ)|=(4318635473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(926261879/2000000000 : ℝ)|^2155 ≤ (36435833996291/100000000000000 : ℝ)^1643
        have hw : |(926261879/2000000000 : ℝ)|=(926261879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4025937189/10000000000 : ℝ)|^2155 ≤ (6064062068017/20000000000000 : ℝ)^1643
        have hw : |(4025937189/10000000000 : ℝ)|=(4025937189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1350_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9701/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1741/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (619/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16073/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9701/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1741/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9701/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1741/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9701/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1741/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9701/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1741/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9701/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1741/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9701/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1741/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1741/25000 : ℝ) ^ (4309/1024 : ℝ) ≤ (1351265324329361/100000000000000000000 : ℝ) := by
    have hpowers : (1741/25000 : ℝ)^4309 ≤ (1351265324329361/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1741 : ℕ)^4309*100000000000000000000^1024 ≤ 1351265324329361^1024*25000^4309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1741 25000 1351265324329361 100000000000000000000 4309 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1741/25000 : ℝ)) (X := (1351265324329361/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9701/50000 : ℝ) ^ (4309/1024 : ℝ) ≤ (1259396616988613/1250000000000000000 : ℝ) := by
    have hpowers : (9701/50000 : ℝ)^4309 ≤ (1259396616988613/1250000000000000000 : ℝ)^1024 := by
      have hnat : (9701 : ℕ)^4309*1250000000000000000^1024 ≤ 1259396616988613^1024*50000^4309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9701 50000 1259396616988613 1250000000000000000 4309 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9701/50000 : ℝ)) (X := (1259396616988613/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001351265324329361/50000000000000000000 : ℝ) ≤ (5000032111428133/5000000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (50001351265324329361/50000000000000000000 : ℝ)^1024 ≤ (5000032111428133/5000000000000000 : ℝ)^4309 := by
      have hnat : (50001351265324329361 : ℕ)^1024*5000000000000000^4309 ≤ 5000032111428133^4309*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001351265324329361 50000000000000000000 5000032111428133 5000000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000032111428133/5000000000000000 : ℝ)) (X := (50001351265324329361/50000000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100102102994683418401/100000000000000000000 : ℝ) ≤ (2500606363421031/2500000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (100102102994683418401/100000000000000000000 : ℝ)^1024 ≤ (2500606363421031/2500000000000000 : ℝ)^4309 := by
      have hnat : (100102102994683418401 : ℕ)^1024*2500000000000000^4309 ≤ 2500606363421031^4309*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100102102994683418401 100000000000000000000 2500606363421031 2500000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500606363421031/2500000000000000 : ℝ)) (X := (100102102994683418401/100000000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (626259396616988613/625000000000000000 : ℝ) ≤ (5002393342255991/5000000000000000 : ℝ) ^ (4309/1024 : ℝ) := by
    have hpowers : (626259396616988613/625000000000000000 : ℝ)^1024 ≤ (5002393342255991/5000000000000000 : ℝ)^4309 := by
      have hnat : (626259396616988613 : ℕ)^1024*5000000000000000^4309 ≤ 5002393342255991^4309*625000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        626259396616988613 625000000000000000 5002393342255991 5000000000000000 1024 4309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002393342255991/5000000000000000 : ℝ)) (X := (626259396616988613/625000000000000000 : ℝ)) (by norm_num) 4309 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1351265324329361/100000000000000000000 : ℝ) ≤ ((31086977895228957571/31095000000000000000 : ℝ)+2*(1180615413929/621900000000000 : ℝ)*(1741/25000 : ℝ))^(4309/1024 : ℝ) := by
    rw [show (31086977895228957571/31095000000000000000 : ℝ)+2*(1180615413929/621900000000000 : ℝ)*(1741/25000 : ℝ)=(5000032111428133/5000000000000000 : ℝ) by norm_num, show 1+2*(1351265324329361/100000000000000000000 : ℝ)=(50001351265324329361/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1259396616988613/1250000000000000000 : ℝ)+(1351265324329361/100000000000000000000 : ℝ) ≤ ((31086977895228957571/31095000000000000000 : ℝ)+(1180615413929/621900000000000 : ℝ)*((9701/50000 : ℝ)+(1741/25000 : ℝ)))^(4309/1024 : ℝ) := by
    rw [show (31086977895228957571/31095000000000000000 : ℝ)+(1180615413929/621900000000000 : ℝ)*((9701/50000 : ℝ)+(1741/25000 : ℝ))=(2500606363421031/2500000000000000 : ℝ) by norm_num, show 1+(1259396616988613/1250000000000000000 : ℝ)+(1351265324329361/100000000000000000000 : ℝ)=(100102102994683418401/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1259396616988613/1250000000000000000 : ℝ) ≤ ((31086977895228957571/31095000000000000000 : ℝ)+2*(1180615413929/621900000000000 : ℝ)*(9701/50000 : ℝ))^(4309/1024 : ℝ) := by
    rw [show (31086977895228957571/31095000000000000000 : ℝ)+2*(1180615413929/621900000000000 : ℝ)*(9701/50000 : ℝ)=(5002393342255991/5000000000000000 : ℝ) by norm_num, show 1+2*(1259396616988613/1250000000000000000 : ℝ)=(626259396616988613/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (31086977895228957571/31095000000000000000 : ℝ)*(X 1 0+X 2 0)+(1180615413929/621900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (1741/25000 : ℝ)) (hi := (9701/50000 : ℝ)) (c := (31086977895228957571/31095000000000000000 : ℝ)) (alpha := (1180615413929/621900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (31086977895228957571/31095000000000000000 : ℝ)*(X 0 1+X 2 1)+(1180615413929/621900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (1741/25000 : ℝ)) (hi := (9701/50000 : ℝ)) (c := (31086977895228957571/31095000000000000000 : ℝ)) (alpha := (1180615413929/621900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (31086977895228957571/31095000000000000000 : ℝ)*(X 0 2+X 1 2)+(1180615413929/621900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4309/1024 : ℝ)) (lo := (1741/25000 : ℝ)) (hi := (9701/50000 : ℝ)) (c := (31086977895228957571/31095000000000000000 : ℝ)) (alpha := (1180615413929/621900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-253443623/1250000000 : ℝ)*X 0 0+(342348887/625000000 : ℝ)*X 0 1+(1037157077/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5365393793/10000000000 : ℝ)*X 1 0+(-2178256849/10000000000 : ℝ)*X 1 1+(5185785773/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1341348467/2500000000 : ℝ)*X 2 0+(5185785687/10000000000 : ℝ)*X 2 1+(-2178256863/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4318501381/10000000000 : ℝ)*X 0 0+(402209179/1000000000 : ℝ)*X 0 1+(4635120707/10000000000 : ℝ)*X 0 2+(4318501381/10000000000 : ℝ)*X 1 0+(402209179/1000000000 : ℝ)*X 1 1+(4635120707/10000000000 : ℝ)*X 1 2+(4318501381/10000000000 : ℝ)*X 2 0+(402209179/1000000000 : ℝ)*X 2 1+(4635120707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-40552253/200000000 : ℝ)*X 0 0+(2593799917/5000000000 : ℝ)*X 0 1+(5475751531/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5290118227/10000000000 : ℝ)*X 1 0+(-1888290793/10000000000 : ℝ)*X 1 1+(5475751509/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((264505911/500000000 : ℝ)*X 2 0+(5475751537/10000000000 : ℝ)*X 2 1+(-472072691/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4318635473/10000000000 : ℝ)*X 0 0+(926261879/2000000000 : ℝ)*X 0 1+(4025937189/10000000000 : ℝ)*X 0 2+(4318635473/10000000000 : ℝ)*X 1 0+(926261879/2000000000 : ℝ)*X 1 1+(4025937189/10000000000 : ℝ)*X 1 2+(4318635473/10000000000 : ℝ)*X 2 0+(926261879/2000000000 : ℝ)*X 2 1+(4025937189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1350_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (783762062118874075469239469/259125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85412521/20000000000000 : ℝ)*(base19) + (226641753/50000000000000 : ℝ)*(base23) + (34807411/50000000000000 : ℝ)*(upper3) + (11634407/100000000000000 : ℝ)*(upper4) + (52643673/100000000000000 : ℝ)*(upper5) + (1264578001955239/50000000000000 : ℝ)*(major0) + (1264578001955239/50000000000000 : ℝ)*(major1) + (1264578001955239/50000000000000 : ℝ)*(major2) + (3427051461567239/100000000000000 : ℝ)*(sp0) + (3427060309801967/100000000000000 : ℝ)*(sp1) + (1713530141790533/50000000000000 : ℝ)*(sp2) + (1631247626941047/100000000000000 : ℝ)*(sp3) + (9275297333/100000000000000 : ℝ)*(sp4) + (1771596857/50000000000000 : ℝ)*(sp7) + (1631251170134761/100000000000000 : ℝ)*(f.failure) + (856765184216143/25000000000000 : ℝ)*(f.sum) + (208601205820223/31095000000000000000000000000 : ℝ)*base66 + (6865518191933785531/1554750000000000000000000000000000 : ℝ)*base68 + (765721490511964469/1554750000000000000000000000000000 : ℝ)*base69 + (13204538190961285531/1554750000000000000000000000000000 : ℝ)*base72 + (133118720630753/31095000000000000000000000000 : ℝ)*base74 + (10000863956760214469/1554750000000000000000000000000000 : ℝ)*base75 + (449854983482035531/1554750000000000000000000000000000 : ℝ)*base78 + (2883106497260785531/1554750000000000000000000000000000 : ℝ)*base80 + (81992602729553/31095000000000000000000000000 : ℝ)*base82 + (5144907/2000000000000000000000 : ℝ)*base89 + (5144907/2000000000000000000000 : ℝ)*base91 + (5144907/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (801056928196751586707024013/86375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93209901/5000000000000 : ℝ)*(base19) + (1035278291/50000000000000 : ℝ)*(base23) + (27850251/12500000000000 : ℝ)*(upper3) + (21488691/25000000000000 : ℝ)*(lower4) + (31802349/20000000000000 : ℝ)*(upper5) + (1280567188669697/50000000000000 : ℝ)*(major0) + (1280567188669697/50000000000000 : ℝ)*(major1) + (1280567188669697/50000000000000 : ℝ)*(major2) + (21139485187/100000000000000 : ℝ)*(sp1) + (24545693703/100000000000000 : ℝ)*(sp2) + (3470391913033241/100000000000000 : ℝ)*(sp4) + (1735184454675017/50000000000000 : ℝ)*(sp5) + (867591324195739/25000000000000 : ℝ)*(sp6) + (825938266253173/50000000000000 : ℝ)*(sp7) + (825938266253173/50000000000000 : ℝ)*(f.failure) + (3470391913033241/100000000000000 : ℝ)*(f.sum) + (42744984517633/15547500000000000000000000000 : ℝ)*base65 + (11900615836168075987/1554750000000000000000000000000000 : ℝ)*base67 + (6697270731288325987/1554750000000000000000000000000000 : ℝ)*base69 + (15147675447253825987/1554750000000000000000000000000000 : ℝ)*base71 + (232178301369251/31095000000000000000000000000 : ℝ)*base73 + (13050128664529825987/1554750000000000000000000000000000 : ℝ)*base75 + (3220010450807575987/1554750000000000000000000000000000 : ℝ)*base77 + (9525345996607825987/1554750000000000000000000000000000 : ℝ)*base79 + (46753798382531/31095000000000000000000000000 : ℝ)*base81 + (10368849/1000000000000000000000 : ℝ)*base90 + (10368849/1000000000000000000000 : ℝ)*base92 + (10368849/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1350_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9701/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1741/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (619/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16073/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1350_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1350_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (619/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16073/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1350_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1350_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1350_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4309/1024 : ℝ) ≤ p) (hpb : p ≤ (2155/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31008787/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (619/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16073/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1350_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
