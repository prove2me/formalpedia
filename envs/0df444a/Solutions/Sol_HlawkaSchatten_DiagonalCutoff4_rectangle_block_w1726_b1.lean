-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1726_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:01:25.734985+00:00
-- url     : https://prove2.me/submissions/f4baee7e-73b6-4fa2-a3eb-4aaaed478807

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
theorem support_rectangle_w1726_s3_0 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-42384499/312500000 : ℝ)*x 0 + (5460006801/10000000000 : ℝ)*x 1 + (160625387/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42384499/312500000 : ℝ)^5431 ≤ (426308103323/5000000000000 : ℝ)^4407 := by
    have hnat : (42384499 : ℕ)^5431*5000000000000^4407 ≤ 426308103323^4407*312500000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42384499 312500000 426308103323 5000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5460006801/10000000000 : ℝ)^5431 ≤ (47438180056147/100000000000000 : ℝ)^4407 := by
    have hnat : (5460006801 : ℕ)^5431*100000000000000^4407 ≤ 47438180056147^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460006801 10000000000 47438180056147 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160625387/312500000 : ℝ)^5431 ≤ (22017828930757/50000000000000 : ℝ)^4407 := by
    have hnat : (160625387 : ℕ)^5431*50000000000000^4407 ≤ 22017828930757^4407*312500000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160625387 312500000 22017828930757 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42384499/312500000 : ℝ), (5460006801/10000000000 : ℝ), (160625387/312500000 : ℝ)] ![(426308103323/5000000000000 : ℝ), (47438180056147/100000000000000 : ℝ), (22017828930757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42384499/312500000 : ℝ)|^5431 ≤ (426308103323/5000000000000 : ℝ)^4407
        have hw : |(-42384499/312500000 : ℝ)|=(42384499/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5460006801/10000000000 : ℝ)|^5431 ≤ (47438180056147/100000000000000 : ℝ)^4407
        have hw : |(5460006801/10000000000 : ℝ)|=(5460006801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(160625387/312500000 : ℝ)|^5431 ≤ (22017828930757/50000000000000 : ℝ)^4407
        have hw : |(160625387/312500000 : ℝ)|=(160625387/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s3_1 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5338137323/10000000000 : ℝ)*x 0 + (-152201757/1000000000 : ℝ)*x 1 + (1028002477/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5338137323/10000000000 : ℝ)^5431 ≤ (46136715427521/100000000000000 : ℝ)^4407 := by
    have hnat : (5338137323 : ℕ)^5431*100000000000000^4407 ≤ 46136715427521^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5338137323 10000000000 46136715427521 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (152201757/1000000000 : ℝ)^5431 ≤ (9827626690609/100000000000000 : ℝ)^4407 := by
    have hnat : (152201757 : ℕ)^5431*100000000000000^4407 ≤ 9827626690609^4407*1000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152201757 1000000000 9827626690609 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028002477/2000000000 : ℝ)^5431 ≤ (44035657872071/100000000000000 : ℝ)^4407 := by
    have hnat : (1028002477 : ℕ)^5431*100000000000000^4407 ≤ 44035657872071^4407*2000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028002477 2000000000 44035657872071 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5338137323/10000000000 : ℝ), (-152201757/1000000000 : ℝ), (1028002477/2000000000 : ℝ)] ![(46136715427521/100000000000000 : ℝ), (9827626690609/100000000000000 : ℝ), (44035657872071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5338137323/10000000000 : ℝ)|^5431 ≤ (46136715427521/100000000000000 : ℝ)^4407
        have hw : |(5338137323/10000000000 : ℝ)|=(5338137323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-152201757/1000000000 : ℝ)|^5431 ≤ (9827626690609/100000000000000 : ℝ)^4407
        have hw : |(-152201757/1000000000 : ℝ)|=(152201757/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1028002477/2000000000 : ℝ)|^5431 ≤ (44035657872071/100000000000000 : ℝ)^4407
        have hw : |(1028002477/2000000000 : ℝ)|=(1028002477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s3_2 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5338137323/10000000000 : ℝ)*x 0 + (160625387/312500000 : ℝ)*x 1 + (-152201757/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5338137323/10000000000 : ℝ)^5431 ≤ (46136715427521/100000000000000 : ℝ)^4407 := by
    have hnat : (5338137323 : ℕ)^5431*100000000000000^4407 ≤ 46136715427521^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5338137323 10000000000 46136715427521 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160625387/312500000 : ℝ)^5431 ≤ (22017828930757/50000000000000 : ℝ)^4407 := by
    have hnat : (160625387 : ℕ)^5431*50000000000000^4407 ≤ 22017828930757^4407*312500000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160625387 312500000 22017828930757 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (152201757/1000000000 : ℝ)^5431 ≤ (9827626690609/100000000000000 : ℝ)^4407 := by
    have hnat : (152201757 : ℕ)^5431*100000000000000^4407 ≤ 9827626690609^4407*1000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152201757 1000000000 9827626690609 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5338137323/10000000000 : ℝ), (160625387/312500000 : ℝ), (-152201757/1000000000 : ℝ)] ![(46136715427521/100000000000000 : ℝ), (22017828930757/50000000000000 : ℝ), (9827626690609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5338137323/10000000000 : ℝ)|^5431 ≤ (46136715427521/100000000000000 : ℝ)^4407
        have hw : |(5338137323/10000000000 : ℝ)|=(5338137323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160625387/312500000 : ℝ)|^5431 ≤ (22017828930757/50000000000000 : ℝ)^4407
        have hw : |(160625387/312500000 : ℝ)|=(160625387/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-152201757/1000000000 : ℝ)|^5431 ≤ (9827626690609/100000000000000 : ℝ)^4407
        have hw : |(-152201757/1000000000 : ℝ)|=(152201757/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s3_3 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2042344553/5000000000 : ℝ)*x 0 + (905258229/2500000000 : ℝ)*x 1 + (4582703959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2042344553/5000000000 : ℝ)^5431 ≤ (6634968079671/20000000000000 : ℝ)^4407 := by
    have hnat : (2042344553 : ℕ)^5431*20000000000000^4407 ≤ 6634968079671^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042344553 5000000000 6634968079671 20000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (905258229/2500000000 : ℝ)^5431 ≤ (3574652686807/12500000000000 : ℝ)^4407 := by
    have hnat : (905258229 : ℕ)^5431*12500000000000^4407 ≤ 3574652686807^4407*2500000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905258229 2500000000 3574652686807 12500000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4582703959/10000000000 : ℝ)^5431 ≤ (2389246130327/6250000000000 : ℝ)^4407 := by
    have hnat : (4582703959 : ℕ)^5431*6250000000000^4407 ≤ 2389246130327^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4582703959 10000000000 2389246130327 6250000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2042344553/5000000000 : ℝ), (905258229/2500000000 : ℝ), (4582703959/10000000000 : ℝ)] ![(6634968079671/20000000000000 : ℝ), (3574652686807/12500000000000 : ℝ), (2389246130327/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2042344553/5000000000 : ℝ)|^5431 ≤ (6634968079671/20000000000000 : ℝ)^4407
        have hw : |(2042344553/5000000000 : ℝ)|=(2042344553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(905258229/2500000000 : ℝ)|^5431 ≤ (3574652686807/12500000000000 : ℝ)^4407
        have hw : |(905258229/2500000000 : ℝ)|=(905258229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4582703959/10000000000 : ℝ)|^5431 ≤ (2389246130327/6250000000000 : ℝ)^4407
        have hw : |(4582703959/10000000000 : ℝ)|=(4582703959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s3_4 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-678223133/5000000000 : ℝ)*x 0 + (1285901419/2500000000 : ℝ)*x 1 + (1364090013/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (678223133/5000000000 : ℝ)^5431 ≤ (4263632230931/50000000000000 : ℝ)^4407 := by
    have hnat : (678223133 : ℕ)^5431*50000000000000^4407 ≤ 4263632230931^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678223133 5000000000 4263632230931 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1285901419/2500000000 : ℝ)^5431 ≤ (44073598518877/100000000000000 : ℝ)^4407 := by
    have hnat : (1285901419 : ℕ)^5431*100000000000000^4407 ≤ 44073598518877^4407*2500000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285901419 2500000000 44073598518877 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364090013/2500000000 : ℝ)^5431 ≤ (47399137004637/100000000000000 : ℝ)^4407 := by
    have hnat : (1364090013 : ℕ)^5431*100000000000000^4407 ≤ 47399137004637^4407*2500000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364090013 2500000000 47399137004637 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-678223133/5000000000 : ℝ), (1285901419/2500000000 : ℝ), (1364090013/2500000000 : ℝ)] ![(4263632230931/50000000000000 : ℝ), (44073598518877/100000000000000 : ℝ), (47399137004637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-678223133/5000000000 : ℝ)|^5431 ≤ (4263632230931/50000000000000 : ℝ)^4407
        have hw : |(-678223133/5000000000 : ℝ)|=(678223133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1285901419/2500000000 : ℝ)|^5431 ≤ (44073598518877/100000000000000 : ℝ)^4407
        have hw : |(1285901419/2500000000 : ℝ)|=(1285901419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1364090013/2500000000 : ℝ)|^5431 ≤ (47399137004637/100000000000000 : ℝ)^4407
        have hw : |(1364090013/2500000000 : ℝ)|=(1364090013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s3_5 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210099483/400000000 : ℝ)*x 0 + (-602834989/5000000000 : ℝ)*x 1 + (272817997/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210099483/400000000 : ℝ)^5431 ≤ (22613077641717/50000000000000 : ℝ)^4407 := by
    have hnat : (210099483 : ℕ)^5431*50000000000000^4407 ≤ 22613077641717^4407*400000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210099483 400000000 22613077641717 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (602834989/5000000000 : ℝ)^5431 ≤ (1474941779113/20000000000000 : ℝ)^4407 := by
    have hnat : (602834989 : ℕ)^5431*20000000000000^4407 ≤ 1474941779113^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602834989 5000000000 1474941779113 20000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272817997/500000000 : ℝ)^5431 ≤ (47399135805629/100000000000000 : ℝ)^4407 := by
    have hnat : (272817997 : ℕ)^5431*100000000000000^4407 ≤ 47399135805629^4407*500000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272817997 500000000 47399135805629 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210099483/400000000 : ℝ), (-602834989/5000000000 : ℝ), (272817997/500000000 : ℝ)] ![(22613077641717/50000000000000 : ℝ), (1474941779113/20000000000000 : ℝ), (47399135805629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210099483/400000000 : ℝ)|^5431 ≤ (22613077641717/50000000000000 : ℝ)^4407
        have hw : |(210099483/400000000 : ℝ)|=(210099483/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-602834989/5000000000 : ℝ)|^5431 ≤ (1474941779113/20000000000000 : ℝ)^4407
        have hw : |(-602834989/5000000000 : ℝ)|=(602834989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(272817997/500000000 : ℝ)|^5431 ≤ (47399135805629/100000000000000 : ℝ)^4407
        have hw : |(272817997/500000000 : ℝ)|=(272817997/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s3_6 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626243513/5000000000 : ℝ)*x 0 + (545635999/1000000000 : ℝ)*x 1 + (-150708747/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626243513/5000000000 : ℝ)^5431 ≤ (45226154763489/100000000000000 : ℝ)^4407 := by
    have hnat : (2626243513 : ℕ)^5431*100000000000000^4407 ≤ 45226154763489^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626243513 5000000000 45226154763489 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545635999/1000000000 : ℝ)^5431 ≤ (473991363409/1000000000000 : ℝ)^4407 := by
    have hnat : (545635999 : ℕ)^5431*1000000000000^4407 ≤ 473991363409^4407*1000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545635999 1000000000 473991363409 1000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150708747/1250000000 : ℝ)^5431 ≤ (7374708880489/100000000000000 : ℝ)^4407 := by
    have hnat : (150708747 : ℕ)^5431*100000000000000^4407 ≤ 7374708880489^4407*1250000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150708747 1250000000 7374708880489 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626243513/5000000000 : ℝ), (545635999/1000000000 : ℝ), (-150708747/1250000000 : ℝ)] ![(45226154763489/100000000000000 : ℝ), (473991363409/1000000000000 : ℝ), (7374708880489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626243513/5000000000 : ℝ)|^5431 ≤ (45226154763489/100000000000000 : ℝ)^4407
        have hw : |(2626243513/5000000000 : ℝ)|=(2626243513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545635999/1000000000 : ℝ)|^5431 ≤ (473991363409/1000000000000 : ℝ)^4407
        have hw : |(545635999/1000000000 : ℝ)|=(545635999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-150708747/1250000000 : ℝ)|^5431 ≤ (7374708880489/100000000000000 : ℝ)^4407
        have hw : |(-150708747/1250000000 : ℝ)|=(150708747/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_s3_7 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (817023373/2000000000 : ℝ)*x 0 + (914380973/2000000000 : ℝ)*x 1 + (1815996301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (817023373/2000000000 : ℝ)^5431 ≤ (8294780462459/25000000000000 : ℝ)^4407 := by
    have hnat : (817023373 : ℕ)^5431*25000000000000^4407 ≤ 8294780462459^4407*2000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      817023373 2000000000 8294780462459 25000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (914380973/2000000000 : ℝ)^5431 ≤ (19058476559/50000000000 : ℝ)^4407 := by
    have hnat : (914380973 : ℕ)^5431*50000000000^4407 ≤ 19058476559^4407*2000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914380973 2000000000 19058476559 50000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1815996301/5000000000 : ℝ)^5431 ≤ (3587990628413/12500000000000 : ℝ)^4407 := by
    have hnat : (1815996301 : ℕ)^5431*12500000000000^4407 ≤ 3587990628413^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1815996301 5000000000 3587990628413 12500000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(817023373/2000000000 : ℝ), (914380973/2000000000 : ℝ), (1815996301/5000000000 : ℝ)] ![(8294780462459/25000000000000 : ℝ), (19058476559/50000000000 : ℝ), (3587990628413/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(817023373/2000000000 : ℝ)|^5431 ≤ (8294780462459/25000000000000 : ℝ)^4407
        have hw : |(817023373/2000000000 : ℝ)|=(817023373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(914380973/2000000000 : ℝ)|^5431 ≤ (19058476559/50000000000 : ℝ)^4407
        have hw : |(914380973/2000000000 : ℝ)|=(914380973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1815996301/5000000000 : ℝ)|^5431 ≤ (3587990628413/12500000000000 : ℝ)^4407
        have hw : |(1815996301/5000000000 : ℝ)|=(1815996301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1726_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100131861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2123/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10123/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (633/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8489/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2123/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10123/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2123/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10123/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2123/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10123/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2123/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10123/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2123/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10123/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2123/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10123/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10123/100000 : ℝ) ^ (5423/1024 : ℝ) ≤ (539782426931413/100000000000000000000 : ℝ) := by
    have hpowers : (10123/100000 : ℝ)^5423 ≤ (539782426931413/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10123 : ℕ)^5423*100000000000000000000^1024 ≤ 539782426931413^1024*100000^5423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10123 100000 539782426931413 100000000000000000000 5423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10123/100000 : ℝ)) (X := (539782426931413/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2123/12500 : ℝ) ^ (5423/1024 : ℝ) ≤ (1045393877557809/12500000000000000000 : ℝ) := by
    have hpowers : (2123/12500 : ℝ)^5423 ≤ (1045393877557809/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2123 : ℕ)^5423*12500000000000000000^1024 ≤ 1045393877557809^1024*12500^5423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2123 12500 1045393877557809 12500000000000000000 5423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2123/12500 : ℝ)) (X := (1045393877557809/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000539782426931413/50000000000000000000 : ℝ) ≤ (10000020384834409/10000000000000000 : ℝ) ^ (5423/1024 : ℝ) := by
    have hpowers : (50000539782426931413/50000000000000000000 : ℝ)^1024 ≤ (10000020384834409/10000000000000000 : ℝ)^5423 := by
      have hnat : (50000539782426931413 : ℕ)^1024*10000000000000000^5423 ≤ 10000020384834409^5423*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000539782426931413 50000000000000000000 10000020384834409 10000000000000000 1024 5423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000020384834409/10000000000000000 : ℝ)) (X := (50000539782426931413/50000000000000000000 : ℝ)) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20001780586689478777/20000000000000000000 : ℝ) ≤ (125002101298791/125000000000000 : ℝ) ^ (5423/1024 : ℝ) := by
    have hpowers : (20001780586689478777/20000000000000000000 : ℝ)^1024 ≤ (125002101298791/125000000000000 : ℝ)^5423 := by
      have hnat : (20001780586689478777 : ℕ)^1024*125000000000000^5423 ≤ 125002101298791^5423*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20001780586689478777 20000000000000000000 125002101298791 125000000000000 1024 5423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125002101298791/125000000000000 : ℝ)) (X := (20001780586689478777/20000000000000000000 : ℝ)) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6251045393877557809/6250000000000000000 : ℝ) ≤ (10000315822972151/10000000000000000 : ℝ) ^ (5423/1024 : ℝ) := by
    have hpowers : (6251045393877557809/6250000000000000000 : ℝ)^1024 ≤ (10000315822972151/10000000000000000 : ℝ)^5423 := by
      have hnat : (6251045393877557809 : ℕ)^1024*10000000000000000^5423 ≤ 10000315822972151^5423*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251045393877557809 6250000000000000000 10000315822972151 10000000000000000 1024 5423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000315822972151/10000000000000000 : ℝ)) (X := (6251045393877557809/6250000000000000000 : ℝ)) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(539782426931413/100000000000000000000 : ℝ) ≤ ((68607149140080517883/68610000000000000000 : ℝ)+2*(147719068871/686100000000000 : ℝ)*(10123/100000 : ℝ))^(5423/1024 : ℝ) := by
    rw [show (68607149140080517883/68610000000000000000 : ℝ)+2*(147719068871/686100000000000 : ℝ)*(10123/100000 : ℝ)=(10000020384834409/10000000000000000 : ℝ) by norm_num, show 1+2*(539782426931413/100000000000000000000 : ℝ)=(50000539782426931413/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1045393877557809/12500000000000000000 : ℝ)+(539782426931413/100000000000000000000 : ℝ) ≤ ((68607149140080517883/68610000000000000000 : ℝ)+(147719068871/686100000000000 : ℝ)*((2123/12500 : ℝ)+(10123/100000 : ℝ)))^(5423/1024 : ℝ) := by
    rw [show (68607149140080517883/68610000000000000000 : ℝ)+(147719068871/686100000000000 : ℝ)*((2123/12500 : ℝ)+(10123/100000 : ℝ))=(125002101298791/125000000000000 : ℝ) by norm_num, show 1+(1045393877557809/12500000000000000000 : ℝ)+(539782426931413/100000000000000000000 : ℝ)=(20001780586689478777/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1045393877557809/12500000000000000000 : ℝ) ≤ ((68607149140080517883/68610000000000000000 : ℝ)+2*(147719068871/686100000000000 : ℝ)*(2123/12500 : ℝ))^(5423/1024 : ℝ) := by
    rw [show (68607149140080517883/68610000000000000000 : ℝ)+2*(147719068871/686100000000000 : ℝ)*(2123/12500 : ℝ)=(10000315822972151/10000000000000000 : ℝ) by norm_num, show 1+2*(1045393877557809/12500000000000000000 : ℝ)=(6251045393877557809/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (68607149140080517883/68610000000000000000 : ℝ)*(X 1 0+X 2 0)+(147719068871/686100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5423/1024 : ℝ)) (lo := (10123/100000 : ℝ)) (hi := (2123/12500 : ℝ)) (c := (68607149140080517883/68610000000000000000 : ℝ)) (alpha := (147719068871/686100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (68607149140080517883/68610000000000000000 : ℝ)*(X 0 1+X 2 1)+(147719068871/686100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5423/1024 : ℝ)) (lo := (10123/100000 : ℝ)) (hi := (2123/12500 : ℝ)) (c := (68607149140080517883/68610000000000000000 : ℝ)) (alpha := (147719068871/686100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (68607149140080517883/68610000000000000000 : ℝ)*(X 0 2+X 1 2)+(147719068871/686100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5423/1024 : ℝ)) (lo := (10123/100000 : ℝ)) (hi := (2123/12500 : ℝ)) (c := (68607149140080517883/68610000000000000000 : ℝ)) (alpha := (147719068871/686100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-42384499/312500000 : ℝ)*X 0 0+(5460006801/10000000000 : ℝ)*X 0 1+(160625387/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5338137323/10000000000 : ℝ)*X 1 0+(-152201757/1000000000 : ℝ)*X 1 1+(1028002477/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5338137323/10000000000 : ℝ)*X 2 0+(160625387/312500000 : ℝ)*X 2 1+(-152201757/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2042344553/5000000000 : ℝ)*X 0 0+(905258229/2500000000 : ℝ)*X 0 1+(4582703959/10000000000 : ℝ)*X 0 2+(2042344553/5000000000 : ℝ)*X 1 0+(905258229/2500000000 : ℝ)*X 1 1+(4582703959/10000000000 : ℝ)*X 1 2+(2042344553/5000000000 : ℝ)*X 2 0+(905258229/2500000000 : ℝ)*X 2 1+(4582703959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-678223133/5000000000 : ℝ)*X 0 0+(1285901419/2500000000 : ℝ)*X 0 1+(1364090013/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((210099483/400000000 : ℝ)*X 1 0+(-602834989/5000000000 : ℝ)*X 1 1+(272817997/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2626243513/5000000000 : ℝ)*X 2 0+(545635999/1000000000 : ℝ)*X 2 1+(-150708747/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((817023373/2000000000 : ℝ)*X 0 0+(914380973/2000000000 : ℝ)*X 0 1+(1815996301/5000000000 : ℝ)*X 0 2+(817023373/2000000000 : ℝ)*X 1 0+(914380973/2000000000 : ℝ)*X 1 1+(1815996301/5000000000 : ℝ)*X 1 2+(817023373/2000000000 : ℝ)*X 2 0+(914380973/2000000000 : ℝ)*X 2 1+(1815996301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4840421759577167722693317021/571750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1217821179/100000000000000 : ℝ)*(base19) + (17905517/1562500000000 : ℝ)*(base23) + (19182087/50000000000000 : ℝ)*(lower2) + (101769451/50000000000000 : ℝ)*(upper3) + (9536919/6250000000000 : ℝ)*(upper5) + (1041236137076487/50000000000000 : ℝ)*(major0) + (1041236137076487/50000000000000 : ℝ)*(major1) + (1041236137076487/50000000000000 : ℝ)*(major2) + (3125067020363583/100000000000000 : ℝ)*(sp0) + (4882934511789/156250000000 : ℝ)*(sp1) + (781269539853263/25000000000000 : ℝ)*(sp2) + (207972106415477/20000000000000 : ℝ)*(sp3) + (12285002557/100000000000000 : ℝ)*(sp4) + (221433161/5000000000000 : ℝ)*(sp7) + (207972992148121/20000000000000 : ℝ)*(f.failure) + (156253965268307/5000000000000 : ℝ)*(f.sum) + (20708869331189/5717500000000000000000000000 : ℝ)*base65 + (420658928390839007/1143500000000000000000000000000000 : ℝ)*base67 + (8453380216405160993/1143500000000000000000000000000000 : ℝ)*base70 + (1040280919711660993/1143500000000000000000000000000000 : ℝ)*base72 + (10378209281759/5717500000000000000000000000 : ℝ)*base73 + (1713404225960839007/1143500000000000000000000000000000 : ℝ)*base75 + (5886431307957660993/1143500000000000000000000000000000 : ℝ)*base78 + (2916982528614660993/1143500000000000000000000000000000 : ℝ)*base80 + (46346668617407/11435000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3383181/1000000000000000000000 : ℝ)*base89 + (3383181/1000000000000000000000 : ℝ)*base91 + (3383181/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1546058155012802616626038509/142937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1483313111/100000000000000 : ℝ)*(base19) + (1578522271/100000000000000 : ℝ)*(base23) + (213354483/50000000000000 : ℝ)*(lower1) + (105722209/50000000000000 : ℝ)*(upper3) + (61159793/100000000000000 : ℝ)*(lower4) + (249768791/100000000000000 : ℝ)*(upper5) + (266331749059077/12500000000000 : ℝ)*(major0) + (266331749059077/12500000000000 : ℝ)*(major1) + (266331749059077/12500000000000 : ℝ)*(major2) + (527244797/100000000000000 : ℝ)*(sp2) + (799345882279023/25000000000000 : ℝ)*(sp4) + (159869102290149/5000000000000 : ℝ)*(sp5) + (1598690711674511/50000000000000 : ℝ)*(sp6) + (33247627977657/3125000000000 : ℝ)*(sp7) + (33247627977657/3125000000000 : ℝ)*(f.failure) + (799345882279023/25000000000000 : ℝ)*(f.sum) + (2441102509827/714687500000000000000000000 : ℝ)*base65 + (4683846397331557997/285875000000000000000000000000000 : ℝ)*base67 + (1033044483088442003/285875000000000000000000000000000 : ℝ)*base70 + (2419020775407057997/285875000000000000000000000000000 : ℝ)*base71 + (2061063051291/357343750000000000000000000 : ℝ)*base73 + (21600454123012442003/285875000000000000000000000000000 : ℝ)*base76 + (2332811308986932997/285875000000000000000000000000000 : ℝ)*base77 + (4869134095640057997/285875000000000000000000000000000 : ℝ)*base79 + (13356616463051/5717500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/50000000000000 : ℝ)*base88 + (670323/156250000000000000000 : ℝ)*base90 + (670323/156250000000000000000 : ℝ)*base92 + (670323/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1726_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100131861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2123/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10123/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (633/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8489/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1726_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1726_box_0 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-524795109/5000000000 : ℝ)*x 0 + (5408916679/10000000000 : ℝ)*x 1 + (270445817/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524795109/5000000000 : ℝ)^5431 ≤ (3108252349313/50000000000000 : ℝ)^4407 := by
    have hnat : (524795109 : ℕ)^5431*50000000000000^4407 ≤ 3108252349313^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524795109 5000000000 3108252349313 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408916679/10000000000 : ℝ)^5431 ≤ (2930734341023/6250000000000 : ℝ)^4407 := by
    have hnat : (5408916679 : ℕ)^5431*6250000000000^4407 ≤ 2930734341023^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408916679 10000000000 2930734341023 6250000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270445817/500000000 : ℝ)^5431 ≤ (5861468229323/12500000000000 : ℝ)^4407 := by
    have hnat : (270445817 : ℕ)^5431*12500000000000^4407 ≤ 5861468229323^4407*500000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270445817 500000000 5861468229323 12500000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-524795109/5000000000 : ℝ), (5408916679/10000000000 : ℝ), (270445817/500000000 : ℝ)] ![(3108252349313/50000000000000 : ℝ), (2930734341023/6250000000000 : ℝ), (5861468229323/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-524795109/5000000000 : ℝ)|^5431 ≤ (3108252349313/50000000000000 : ℝ)^4407
        have hw : |(-524795109/5000000000 : ℝ)|=(524795109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408916679/10000000000 : ℝ)|^5431 ≤ (2930734341023/6250000000000 : ℝ)^4407
        have hw : |(5408916679/10000000000 : ℝ)|=(5408916679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270445817/500000000 : ℝ)|^5431 ≤ (5861468229323/12500000000000 : ℝ)^4407
        have hw : |(270445817/500000000 : ℝ)|=(270445817/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_box_1 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612229181/5000000000 : ℝ)*x 0 + (-163919837/1250000000 : ℝ)*x 1 + (2704458503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612229181/5000000000 : ℝ)^5431 ≤ (4492892374609/10000000000000 : ℝ)^4407 := by
    have hnat : (2612229181 : ℕ)^5431*10000000000000^4407 ≤ 4492892374609^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612229181 5000000000 4492892374609 10000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163919837/1250000000 : ℝ)^5431 ≤ (8179323296569/100000000000000 : ℝ)^4407 := by
    have hnat : (163919837 : ℕ)^5431*100000000000000^4407 ≤ 8179323296569^4407*1250000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163919837 1250000000 8179323296569 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704458503/5000000000 : ℝ)^5431 ≤ (11722938237487/25000000000000 : ℝ)^4407 := by
    have hnat : (2704458503 : ℕ)^5431*25000000000000^4407 ≤ 11722938237487^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704458503 5000000000 11722938237487 25000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612229181/5000000000 : ℝ), (-163919837/1250000000 : ℝ), (2704458503/5000000000 : ℝ)] ![(4492892374609/10000000000000 : ℝ), (8179323296569/100000000000000 : ℝ), (11722938237487/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612229181/5000000000 : ℝ)|^5431 ≤ (4492892374609/10000000000000 : ℝ)^4407
        have hw : |(2612229181/5000000000 : ℝ)|=(2612229181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-163919837/1250000000 : ℝ)|^5431 ≤ (8179323296569/100000000000000 : ℝ)^4407
        have hw : |(-163919837/1250000000 : ℝ)|=(163919837/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704458503/5000000000 : ℝ)|^5431 ≤ (11722938237487/25000000000000 : ℝ)^4407
        have hw : |(2704458503/5000000000 : ℝ)|=(2704458503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_box_2 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224458963/10000000000 : ℝ)*x 0 + (5408916317/10000000000 : ℝ)*x 1 + (-163919853/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224458963/10000000000 : ℝ)^5431 ≤ (44928930115453/100000000000000 : ℝ)^4407 := by
    have hnat : (5224458963 : ℕ)^5431*100000000000000^4407 ≤ 44928930115453^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224458963 10000000000 44928930115453 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408916317/10000000000 : ℝ)^5431 ≤ (23445872794429/50000000000000 : ℝ)^4407 := by
    have hnat : (5408916317 : ℕ)^5431*50000000000000^4407 ≤ 23445872794429^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408916317 10000000000 23445872794429 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163919853/1250000000 : ℝ)^5431 ≤ (163586485609/2000000000000 : ℝ)^4407 := by
    have hnat : (163919853 : ℕ)^5431*2000000000000^4407 ≤ 163586485609^4407*1250000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163919853 1250000000 163586485609 2000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224458963/10000000000 : ℝ), (5408916317/10000000000 : ℝ), (-163919853/1250000000 : ℝ)] ![(44928930115453/100000000000000 : ℝ), (23445872794429/50000000000000 : ℝ), (163586485609/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224458963/10000000000 : ℝ)|^5431 ≤ (44928930115453/100000000000000 : ℝ)^4407
        have hw : |(5224458963/10000000000 : ℝ)|=(5224458963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408916317/10000000000 : ℝ)|^5431 ≤ (23445872794429/50000000000000 : ℝ)^4407
        have hw : |(5408916317/10000000000 : ℝ)|=(5408916317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-163919853/1250000000 : ℝ)|^5431 ≤ (163586485609/2000000000000 : ℝ)^4407
        have hw : |(-163919853/1250000000 : ℝ)|=(163919853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_box_3 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2232498567/5000000000 : ℝ)*x 0 + (1957727371/5000000000 : ℝ)*x 1 + (3915454627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2232498567/5000000000 : ℝ)^5431 ≤ (18510769594213/50000000000000 : ℝ)^4407 := by
    have hnat : (2232498567 : ℕ)^5431*50000000000000^4407 ≤ 18510769594213^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2232498567 5000000000 18510769594213 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1957727371/5000000000 : ℝ)^5431 ≤ (393615387123/1250000000000 : ℝ)^4407 := by
    have hnat : (1957727371 : ℕ)^5431*1250000000000^4407 ≤ 393615387123^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1957727371 5000000000 393615387123 1250000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3915454627/10000000000 : ℝ)^5431 ≤ (31489229830077/100000000000000 : ℝ)^4407 := by
    have hnat : (3915454627 : ℕ)^5431*100000000000000^4407 ≤ 31489229830077^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3915454627 10000000000 31489229830077 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2232498567/5000000000 : ℝ), (1957727371/5000000000 : ℝ), (3915454627/10000000000 : ℝ)] ![(18510769594213/50000000000000 : ℝ), (393615387123/1250000000000 : ℝ), (31489229830077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2232498567/5000000000 : ℝ)|^5431 ≤ (18510769594213/50000000000000 : ℝ)^4407
        have hw : |(2232498567/5000000000 : ℝ)|=(2232498567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1957727371/5000000000 : ℝ)|^5431 ≤ (393615387123/1250000000000 : ℝ)^4407
        have hw : |(1957727371/5000000000 : ℝ)|=(1957727371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3915454627/10000000000 : ℝ)|^5431 ≤ (31489229830077/100000000000000 : ℝ)^4407
        have hw : |(3915454627/10000000000 : ℝ)|=(3915454627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_box_4 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-336679099/2000000000 : ℝ)*x 0 + (1294484549/2500000000 : ℝ)*x 1 + (323621129/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336679099/2000000000 : ℝ)^5431 ≤ (5563583729869/50000000000000 : ℝ)^4407 := by
    have hnat : (336679099 : ℕ)^5431*50000000000000^4407 ≤ 5563583729869^4407*2000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336679099 2000000000 5563583729869 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294484549/2500000000 : ℝ)^5431 ≤ (44436416963343/100000000000000 : ℝ)^4407 := by
    have hnat : (1294484549 : ℕ)^5431*100000000000000^4407 ≤ 44436416963343^4407*2500000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294484549 2500000000 44436416963343 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323621129/625000000 : ℝ)^5431 ≤ (44436415567319/100000000000000 : ℝ)^4407 := by
    have hnat : (323621129 : ℕ)^5431*100000000000000^4407 ≤ 44436415567319^4407*625000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323621129 625000000 44436415567319 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-336679099/2000000000 : ℝ), (1294484549/2500000000 : ℝ), (323621129/625000000 : ℝ)] ![(5563583729869/50000000000000 : ℝ), (44436416963343/100000000000000 : ℝ), (44436415567319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-336679099/2000000000 : ℝ)|^5431 ≤ (5563583729869/50000000000000 : ℝ)^4407
        have hw : |(-336679099/2000000000 : ℝ)|=(336679099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294484549/2500000000 : ℝ)|^5431 ≤ (44436416963343/100000000000000 : ℝ)^4407
        have hw : |(1294484549/2500000000 : ℝ)|=(1294484549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323621129/625000000 : ℝ)|^5431 ≤ (44436415567319/100000000000000 : ℝ)^4407
        have hw : |(323621129/625000000 : ℝ)|=(323621129/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_box_5 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380514093/10000000000 : ℝ)*x 0 + (-282794049/2000000000 : ℝ)*x 1 + (5177938967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380514093/10000000000 : ℝ)^5431 ≤ (23294244635731/50000000000000 : ℝ)^4407 := by
    have hnat : (5380514093 : ℕ)^5431*50000000000000^4407 ≤ 23294244635731^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380514093 10000000000 23294244635731 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282794049/2000000000 : ℝ)^5431 ≤ (8975085606611/100000000000000 : ℝ)^4407 := by
    have hnat : (282794049 : ℕ)^5431*100000000000000^4407 ≤ 8975085606611^4407*2000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282794049 2000000000 8975085606611 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177938967/10000000000 : ℝ)^5431 ≤ (2777276569837/6250000000000 : ℝ)^4407 := by
    have hnat : (5177938967 : ℕ)^5431*6250000000000^4407 ≤ 2777276569837^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177938967 10000000000 2777276569837 6250000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380514093/10000000000 : ℝ), (-282794049/2000000000 : ℝ), (5177938967/10000000000 : ℝ)] ![(23294244635731/50000000000000 : ℝ), (8975085606611/100000000000000 : ℝ), (2777276569837/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380514093/10000000000 : ℝ)|^5431 ≤ (23294244635731/50000000000000 : ℝ)^4407
        have hw : |(5380514093/10000000000 : ℝ)|=(5380514093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-282794049/2000000000 : ℝ)|^5431 ≤ (8975085606611/100000000000000 : ℝ)^4407
        have hw : |(-282794049/2000000000 : ℝ)|=(282794049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177938967/10000000000 : ℝ)|^5431 ≤ (2777276569837/6250000000000 : ℝ)^4407
        have hw : |(5177938967/10000000000 : ℝ)|=(5177938967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_box_6 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380514003/10000000000 : ℝ)*x 0 + (2588969447/5000000000 : ℝ)*x 1 + (-706985233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380514003/10000000000 : ℝ)^5431 ≤ (23294244155551/50000000000000 : ℝ)^4407 := by
    have hnat : (5380514003 : ℕ)^5431*50000000000000^4407 ≤ 23294244155551^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380514003 10000000000 23294244155551 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588969447/5000000000 : ℝ)^5431 ≤ (11109106086337/25000000000000 : ℝ)^4407 := by
    have hnat : (2588969447 : ℕ)^5431*25000000000000^4407 ≤ 11109106086337^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588969447 5000000000 11109106086337 25000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (706985233/5000000000 : ℝ)^5431 ≤ (4487543667671/50000000000000 : ℝ)^4407 := by
    have hnat : (706985233 : ℕ)^5431*50000000000000^4407 ≤ 4487543667671^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706985233 5000000000 4487543667671 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380514003/10000000000 : ℝ), (2588969447/5000000000 : ℝ), (-706985233/5000000000 : ℝ)] ![(23294244155551/50000000000000 : ℝ), (11109106086337/25000000000000 : ℝ), (4487543667671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380514003/10000000000 : ℝ)|^5431 ≤ (23294244155551/50000000000000 : ℝ)^4407
        have hw : |(5380514003/10000000000 : ℝ)|=(5380514003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588969447/5000000000 : ℝ)|^5431 ≤ (11109106086337/25000000000000 : ℝ)^4407
        have hw : |(2588969447/5000000000 : ℝ)|=(2588969447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-706985233/5000000000 : ℝ)|^5431 ≤ (4487543667671/50000000000000 : ℝ)^4407
        have hw : |(-706985233/5000000000 : ℝ)|=(706985233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_box_7 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3687917283/10000000000 : ℝ)*x 0 + (16809341/39062500 : ℝ)*x 1 + (2151595389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3687917283/10000000000 : ℝ)^5431 ≤ (3656196190433/12500000000000 : ℝ)^4407 := by
    have hnat : (3687917283 : ℕ)^5431*12500000000000^4407 ≤ 3656196190433^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3687917283 10000000000 3656196190433 12500000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16809341/39062500 : ℝ)^5431 ≤ (35375217855479/100000000000000 : ℝ)^4407 := by
    have hnat : (16809341 : ℕ)^5431*100000000000000^4407 ≤ 35375217855479^4407*39062500^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16809341 39062500 35375217855479 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2151595389/5000000000 : ℝ)^5431 ≤ (35375212607707/100000000000000 : ℝ)^4407 := by
    have hnat : (2151595389 : ℕ)^5431*100000000000000^4407 ≤ 35375212607707^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151595389 5000000000 35375212607707 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3687917283/10000000000 : ℝ), (16809341/39062500 : ℝ), (2151595389/5000000000 : ℝ)] ![(3656196190433/12500000000000 : ℝ), (35375217855479/100000000000000 : ℝ), (35375212607707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3687917283/10000000000 : ℝ)|^5431 ≤ (3656196190433/12500000000000 : ℝ)^4407
        have hw : |(3687917283/10000000000 : ℝ)|=(3687917283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16809341/39062500 : ℝ)|^5431 ≤ (35375217855479/100000000000000 : ℝ)^4407
        have hw : |(16809341/39062500 : ℝ)|=(16809341/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2151595389/5000000000 : ℝ)|^5431 ≤ (35375212607707/100000000000000 : ℝ)^4407
        have hw : |(2151595389/5000000000 : ℝ)|=(2151595389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_box_8 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-96679873/625000000 : ℝ)*x 0 + (5006694927/10000000000 : ℝ)*x 1 + (5451003643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (96679873/625000000 : ℝ)^5431 ≤ (2506455544007/25000000000000 : ℝ)^4407 := by
    have hnat : (96679873 : ℕ)^5431*25000000000000^4407 ≤ 2506455544007^4407*625000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96679873 625000000 2506455544007 25000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5006694927/10000000000 : ℝ)^5431 ≤ (10658094230767/25000000000000 : ℝ)^4407 := by
    have hnat : (5006694927 : ℕ)^5431*25000000000000^4407 ≤ 10658094230767^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5006694927 10000000000 10658094230767 25000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451003643/10000000000 : ℝ)^5431 ≤ (47341800878029/100000000000000 : ℝ)^4407 := by
    have hnat : (5451003643 : ℕ)^5431*100000000000000^4407 ≤ 47341800878029^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451003643 10000000000 47341800878029 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-96679873/625000000 : ℝ), (5006694927/10000000000 : ℝ), (5451003643/10000000000 : ℝ)] ![(2506455544007/25000000000000 : ℝ), (10658094230767/25000000000000 : ℝ), (47341800878029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-96679873/625000000 : ℝ)|^5431 ≤ (2506455544007/25000000000000 : ℝ)^4407
        have hw : |(-96679873/625000000 : ℝ)|=(96679873/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5006694927/10000000000 : ℝ)|^5431 ≤ (10658094230767/25000000000000 : ℝ)^4407
        have hw : |(5006694927/10000000000 : ℝ)|=(5006694927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451003643/10000000000 : ℝ)|^5431 ≤ (47341800878029/100000000000000 : ℝ)^4407
        have hw : |(5451003643/10000000000 : ℝ)|=(5451003643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_box_9 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039209559/2000000000 : ℝ)*x 0 + (-322980353/2500000000 : ℝ)*x 1 + (681375489/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039209559/2000000000 : ℝ)^5431 ≤ (8925604144941/20000000000000 : ℝ)^4407 := by
    have hnat : (1039209559 : ℕ)^5431*20000000000000^4407 ≤ 8925604144941^4407*2000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039209559 2000000000 8925604144941 20000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (322980353/2500000000 : ℝ)^5431 ≤ (4015087751483/50000000000000 : ℝ)^4407 := by
    have hnat : (322980353 : ℕ)^5431*50000000000000^4407 ≤ 4015087751483^4407*2500000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322980353 2500000000 4015087751483 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681375489/1250000000 : ℝ)^5431 ≤ (47341803757133/100000000000000 : ℝ)^4407 := by
    have hnat : (681375489 : ℕ)^5431*100000000000000^4407 ≤ 47341803757133^4407*1250000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681375489 1250000000 47341803757133 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039209559/2000000000 : ℝ), (-322980353/2500000000 : ℝ), (681375489/1250000000 : ℝ)] ![(8925604144941/20000000000000 : ℝ), (4015087751483/50000000000000 : ℝ), (47341803757133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039209559/2000000000 : ℝ)|^5431 ≤ (8925604144941/20000000000000 : ℝ)^4407
        have hw : |(1039209559/2000000000 : ℝ)|=(1039209559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-322980353/2500000000 : ℝ)|^5431 ≤ (4015087751483/50000000000000 : ℝ)^4407
        have hw : |(-322980353/2500000000 : ℝ)|=(322980353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(681375489/1250000000 : ℝ)|^5431 ≤ (47341803757133/100000000000000 : ℝ)^4407
        have hw : |(681375489/1250000000 : ℝ)|=(681375489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_box_10 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1014853/1953125 : ℝ)*x 0 + (5451003979/10000000000 : ℝ)*x 1 + (-1291921919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1014853/1953125 : ℝ)^5431 ≤ (44628016120439/100000000000000 : ℝ)^4407 := by
    have hnat : (1014853 : ℕ)^5431*100000000000000^4407 ≤ 44628016120439^4407*1953125^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014853 1953125 44628016120439 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5451003979/10000000000 : ℝ)^5431 ≤ (47341804474233/100000000000000 : ℝ)^4407 := by
    have hnat : (5451003979 : ℕ)^5431*100000000000000^4407 ≤ 47341804474233^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451003979 10000000000 47341804474233 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1291921919/10000000000 : ℝ)^5431 ≤ (8030179386559/100000000000000 : ℝ)^4407 := by
    have hnat : (1291921919 : ℕ)^5431*100000000000000^4407 ≤ 8030179386559^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291921919 10000000000 8030179386559 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1014853/1953125 : ℝ), (5451003979/10000000000 : ℝ), (-1291921919/10000000000 : ℝ)] ![(44628016120439/100000000000000 : ℝ), (47341804474233/100000000000000 : ℝ), (8030179386559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1014853/1953125 : ℝ)|^5431 ≤ (44628016120439/100000000000000 : ℝ)^4407
        have hw : |(1014853/1953125 : ℝ)|=(1014853/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5451003979/10000000000 : ℝ)|^5431 ≤ (47341804474233/100000000000000 : ℝ)^4407
        have hw : |(5451003979/10000000000 : ℝ)|=(5451003979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1291921919/10000000000 : ℝ)|^5431 ≤ (8030179386559/100000000000000 : ℝ)^4407
        have hw : |(-1291921919/10000000000 : ℝ)|=(1291921919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_box_11 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4601639529/10000000000 : ℝ)*x 0 + (60072167/156250000 : ℝ)*x 1 + (768923579/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4601639529/10000000000 : ℝ)^5431 ≤ (38422690305641/100000000000000 : ℝ)^4407 := by
    have hnat : (4601639529 : ℕ)^5431*100000000000000^4407 ≤ 38422690305641^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4601639529 10000000000 38422690305641 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (60072167/156250000 : ℝ)^5431 ≤ (3078865874847/10000000000000 : ℝ)^4407 := by
    have hnat : (60072167 : ℕ)^5431*10000000000000^4407 ≤ 3078865874847^4407*156250000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60072167 156250000 3078865874847 10000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (768923579/2000000000 : ℝ)^5431 ≤ (30788650922333/100000000000000 : ℝ)^4407 := by
    have hnat : (768923579 : ℕ)^5431*100000000000000^4407 ≤ 30788650922333^4407*2000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768923579 2000000000 30788650922333 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4601639529/10000000000 : ℝ), (60072167/156250000 : ℝ), (768923579/2000000000 : ℝ)] ![(38422690305641/100000000000000 : ℝ), (3078865874847/10000000000000 : ℝ), (30788650922333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4601639529/10000000000 : ℝ)|^5431 ≤ (38422690305641/100000000000000 : ℝ)^4407
        have hw : |(4601639529/10000000000 : ℝ)|=(4601639529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(60072167/156250000 : ℝ)|^5431 ≤ (3078865874847/10000000000000 : ℝ)^4407
        have hw : |(60072167/156250000 : ℝ)|=(60072167/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(768923579/2000000000 : ℝ)|^5431 ≤ (30788650922333/100000000000000 : ℝ)^4407
        have hw : |(768923579/2000000000 : ℝ)|=(768923579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_box_12 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-590113303/5000000000 : ℝ)*x 0 + (2786168849/5000000000 : ℝ)*x 1 + (5153001139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (590113303/5000000000 : ℝ)^5431 ≤ (287335633651/4000000000000 : ℝ)^4407 := by
    have hnat : (590113303 : ℕ)^5431*4000000000000^4407 ≤ 287335633651^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590113303 5000000000 287335633651 4000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2786168849/5000000000 : ℝ)^5431 ≤ (6080472153681/12500000000000 : ℝ)^4407 := by
    have hnat : (2786168849 : ℕ)^5431*12500000000000^4407 ≤ 6080472153681^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2786168849 5000000000 6080472153681 12500000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5153001139/10000000000 : ℝ)^5431 ≤ (11043207981021/25000000000000 : ℝ)^4407 := by
    have hnat : (5153001139 : ℕ)^5431*25000000000000^4407 ≤ 11043207981021^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5153001139 10000000000 11043207981021 25000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-590113303/5000000000 : ℝ), (2786168849/5000000000 : ℝ), (5153001139/10000000000 : ℝ)] ![(287335633651/4000000000000 : ℝ), (6080472153681/12500000000000 : ℝ), (11043207981021/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-590113303/5000000000 : ℝ)|^5431 ≤ (287335633651/4000000000000 : ℝ)^4407
        have hw : |(-590113303/5000000000 : ℝ)|=(590113303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2786168849/5000000000 : ℝ)|^5431 ≤ (6080472153681/12500000000000 : ℝ)^4407
        have hw : |(2786168849/5000000000 : ℝ)|=(2786168849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5153001139/10000000000 : ℝ)|^5431 ≤ (11043207981021/25000000000000 : ℝ)^4407
        have hw : |(5153001139/10000000000 : ℝ)|=(5153001139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_box_13 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2698697851/5000000000 : ℝ)*x 0 + (-284924247/2000000000 : ℝ)*x 1 + (5153001271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698697851/5000000000 : ℝ)^5431 ≤ (23384346463307/50000000000000 : ℝ)^4407 := by
    have hnat : (2698697851 : ℕ)^5431*50000000000000^4407 ≤ 23384346463307^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698697851 5000000000 23384346463307 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284924247/2000000000 : ℝ)^5431 ≤ (2264618433943/25000000000000 : ℝ)^4407 := by
    have hnat : (284924247 : ℕ)^5431*25000000000000^4407 ≤ 2264618433943^4407*2000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284924247 2000000000 2264618433943 25000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5153001271/10000000000 : ℝ)^5431 ≤ (44172833318543/100000000000000 : ℝ)^4407 := by
    have hnat : (5153001271 : ℕ)^5431*100000000000000^4407 ≤ 44172833318543^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5153001271 10000000000 44172833318543 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698697851/5000000000 : ℝ), (-284924247/2000000000 : ℝ), (5153001271/10000000000 : ℝ)] ![(23384346463307/50000000000000 : ℝ), (2264618433943/25000000000000 : ℝ), (44172833318543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698697851/5000000000 : ℝ)|^5431 ≤ (23384346463307/50000000000000 : ℝ)^4407
        have hw : |(2698697851/5000000000 : ℝ)|=(2698697851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-284924247/2000000000 : ℝ)|^5431 ≤ (2264618433943/25000000000000 : ℝ)^4407
        have hw : |(-284924247/2000000000 : ℝ)|=(284924247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5153001271/10000000000 : ℝ)|^5431 ≤ (44172833318543/100000000000000 : ℝ)^4407
        have hw : |(5153001271/10000000000 : ℝ)|=(5153001271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_box_14 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2698697927/5000000000 : ℝ)*x 0 + (128825029/250000000 : ℝ)*x 1 + (-712310589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698697927/5000000000 : ℝ)^5431 ≤ (46768694549737/100000000000000 : ℝ)^4407 := by
    have hnat : (2698697927 : ℕ)^5431*100000000000000^4407 ≤ 46768694549737^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698697927 5000000000 46768694549737 100000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128825029/250000000 : ℝ)^5431 ≤ (4417283214593/10000000000000 : ℝ)^4407 := by
    have hnat : (128825029 : ℕ)^5431*10000000000000^4407 ≤ 4417283214593^4407*250000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128825029 250000000 4417283214593 10000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (712310589/5000000000 : ℝ)^5431 ≤ (4529236644561/50000000000000 : ℝ)^4407 := by
    have hnat : (712310589 : ℕ)^5431*50000000000000^4407 ≤ 4529236644561^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712310589 5000000000 4529236644561 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698697927/5000000000 : ℝ), (128825029/250000000 : ℝ), (-712310589/5000000000 : ℝ)] ![(46768694549737/100000000000000 : ℝ), (4417283214593/10000000000000 : ℝ), (4529236644561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698697927/5000000000 : ℝ)|^5431 ≤ (46768694549737/100000000000000 : ℝ)^4407
        have hw : |(2698697927/5000000000 : ℝ)|=(2698697927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(128825029/250000000 : ℝ)|^5431 ≤ (4417283214593/10000000000000 : ℝ)^4407
        have hw : |(128825029/250000000 : ℝ)|=(128825029/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-712310589/5000000000 : ℝ)|^5431 ≤ (4529236644561/50000000000000 : ℝ)^4407
        have hw : |(-712310589/5000000000 : ℝ)|=(712310589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1726_box_15 (p : ℝ) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1800519961/5000000000 : ℝ)*x 0 + (4344937773/10000000000 : ℝ)*x 1 + (2172468737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1800519961/5000000000 : ℝ)^5431 ≤ (3550345376851/12500000000000 : ℝ)^4407 := by
    have hnat : (1800519961 : ℕ)^5431*12500000000000^4407 ≤ 3550345376851^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800519961 5000000000 3550345376851 12500000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4344937773/10000000000 : ℝ)^5431 ≤ (1789931000109/5000000000000 : ℝ)^4407 := by
    have hnat : (4344937773 : ℕ)^5431*5000000000000^4407 ≤ 1789931000109^4407*10000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4344937773 10000000000 1789931000109 5000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2172468737/5000000000 : ℝ)^5431 ≤ (17899308483129/50000000000000 : ℝ)^4407 := by
    have hnat : (2172468737 : ℕ)^5431*50000000000000^4407 ≤ 17899308483129^4407*5000000000^5431 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172468737 5000000000 17899308483129 50000000000000 5431 4407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5431/1024 : ℝ)) 5431 4407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1800519961/5000000000 : ℝ), (4344937773/10000000000 : ℝ), (2172468737/5000000000 : ℝ)] ![(3550345376851/12500000000000 : ℝ), (1789931000109/5000000000000 : ℝ), (17899308483129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1800519961/5000000000 : ℝ)|^5431 ≤ (3550345376851/12500000000000 : ℝ)^4407
        have hw : |(1800519961/5000000000 : ℝ)|=(1800519961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4344937773/10000000000 : ℝ)|^5431 ≤ (1789931000109/5000000000000 : ℝ)^4407
        have hw : |(4344937773/10000000000 : ℝ)|=(4344937773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2172468737/5000000000 : ℝ)|^5431 ≤ (17899308483129/50000000000000 : ℝ)^4407
        have hw : |(2172468737/5000000000 : ℝ)|=(2172468737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1726_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100131861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8489/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (633/6250 : ℝ)*pair X i i ≤ pair X i h) :
    -(66903/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(2351/4000 : ℝ) ∧ (16397/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (45323/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8489/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (633/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8489/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (633/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8489/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (633/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8489/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (633/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8489/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (633/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8489/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (633/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (633/6250 : ℝ) ^ (5423/1024 : ℝ) ≤ (33824742199653/6250000000000000000 : ℝ) := by
    have hpowers : (633/6250 : ℝ)^5423 ≤ (33824742199653/6250000000000000000 : ℝ)^1024 := by
      have hnat : (633 : ℕ)^5423*6250000000000000000^1024 ≤ 33824742199653^1024*6250^5423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        633 6250 33824742199653 6250000000000000000 5423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (633/6250 : ℝ)) (X := (33824742199653/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8489/50000 : ℝ) ^ (5423/1024 : ℝ) ≤ (8347516257170049/100000000000000000000 : ℝ) := by
    have hpowers : (8489/50000 : ℝ)^5423 ≤ (8347516257170049/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8489 : ℕ)^5423*100000000000000000000^1024 ≤ 8347516257170049^1024*50000^5423 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8489 50000 8347516257170049 100000000000000000000 5423 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8489/50000 : ℝ)) (X := (8347516257170049/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125033824742199653/3125000000000000000 : ℝ) ≤ (250000510955323/250000000000000 : ℝ) ^ (5423/1024 : ℝ) := by
    have hpowers : (3125033824742199653/3125000000000000000 : ℝ)^1024 ≤ (250000510955323/250000000000000 : ℝ)^5423 := by
      have hnat : (3125033824742199653 : ℕ)^1024*250000000000000^5423 ≤ 250000510955323^5423*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125033824742199653 3125000000000000000 250000510955323 250000000000000 1024 5423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250000510955323/250000000000000 : ℝ)) (X := (3125033824742199653/3125000000000000000 : ℝ)) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100008888712132364497/100000000000000000000 : ℝ) ≤ (625010489711759/625000000000000 : ℝ) ^ (5423/1024 : ℝ) := by
    have hpowers : (100008888712132364497/100000000000000000000 : ℝ)^1024 ≤ (625010489711759/625000000000000 : ℝ)^5423 := by
      have hnat : (100008888712132364497 : ℕ)^1024*625000000000000^5423 ≤ 625010489711759^5423*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100008888712132364497 100000000000000000000 625010489711759 625000000000000 1024 5423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625010489711759/625000000000000 : ℝ)) (X := (100008888712132364497/100000000000000000000 : ℝ)) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50008347516257170049/50000000000000000000 : ℝ) ≤ (1250039404070421/1250000000000000 : ℝ) ^ (5423/1024 : ℝ) := by
    have hpowers : (50008347516257170049/50000000000000000000 : ℝ)^1024 ≤ (1250039404070421/1250000000000000 : ℝ)^5423 := by
      have hnat : (50008347516257170049 : ℕ)^1024*1250000000000000^5423 ≤ 1250039404070421^5423*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008347516257170049 50000000000000000000 1250039404070421 1250000000000000 1024 5423 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250039404070421/1250000000000000 : ℝ)) (X := (50008347516257170049/50000000000000000000 : ℝ)) (by norm_num) 5423 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(33824742199653/6250000000000000000 : ℝ) ≤ ((4281072145286072791/4281250000000000000 : ℝ)+2*(18424646903/85625000000000 : ℝ)*(633/6250 : ℝ))^(5423/1024 : ℝ) := by
    rw [show (4281072145286072791/4281250000000000000 : ℝ)+2*(18424646903/85625000000000 : ℝ)*(633/6250 : ℝ)=(250000510955323/250000000000000 : ℝ) by norm_num, show 1+2*(33824742199653/6250000000000000000 : ℝ)=(3125033824742199653/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8347516257170049/100000000000000000000 : ℝ)+(33824742199653/6250000000000000000 : ℝ) ≤ ((4281072145286072791/4281250000000000000 : ℝ)+(18424646903/85625000000000 : ℝ)*((8489/50000 : ℝ)+(633/6250 : ℝ)))^(5423/1024 : ℝ) := by
    rw [show (4281072145286072791/4281250000000000000 : ℝ)+(18424646903/85625000000000 : ℝ)*((8489/50000 : ℝ)+(633/6250 : ℝ))=(625010489711759/625000000000000 : ℝ) by norm_num, show 1+(8347516257170049/100000000000000000000 : ℝ)+(33824742199653/6250000000000000000 : ℝ)=(100008888712132364497/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8347516257170049/100000000000000000000 : ℝ) ≤ ((4281072145286072791/4281250000000000000 : ℝ)+2*(18424646903/85625000000000 : ℝ)*(8489/50000 : ℝ))^(5423/1024 : ℝ) := by
    rw [show (4281072145286072791/4281250000000000000 : ℝ)+2*(18424646903/85625000000000 : ℝ)*(8489/50000 : ℝ)=(1250039404070421/1250000000000000 : ℝ) by norm_num, show 1+2*(8347516257170049/100000000000000000000 : ℝ)=(50008347516257170049/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4281072145286072791/4281250000000000000 : ℝ)*(X 1 0+X 2 0)+(18424646903/85625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5423/1024 : ℝ)) (lo := (633/6250 : ℝ)) (hi := (8489/50000 : ℝ)) (c := (4281072145286072791/4281250000000000000 : ℝ)) (alpha := (18424646903/85625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4281072145286072791/4281250000000000000 : ℝ)*(X 0 1+X 2 1)+(18424646903/85625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5423/1024 : ℝ)) (lo := (633/6250 : ℝ)) (hi := (8489/50000 : ℝ)) (c := (4281072145286072791/4281250000000000000 : ℝ)) (alpha := (18424646903/85625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4281072145286072791/4281250000000000000 : ℝ)*(X 0 2+X 1 2)+(18424646903/85625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5423/1024 : ℝ)) (lo := (633/6250 : ℝ)) (hi := (8489/50000 : ℝ)) (c := (4281072145286072791/4281250000000000000 : ℝ)) (alpha := (18424646903/85625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-524795109/5000000000 : ℝ)*X 0 0+(5408916679/10000000000 : ℝ)*X 0 1+(270445817/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2612229181/5000000000 : ℝ)*X 1 0+(-163919837/1250000000 : ℝ)*X 1 1+(2704458503/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5224458963/10000000000 : ℝ)*X 2 0+(5408916317/10000000000 : ℝ)*X 2 1+(-163919853/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2232498567/5000000000 : ℝ)*X 0 0+(1957727371/5000000000 : ℝ)*X 0 1+(3915454627/10000000000 : ℝ)*X 0 2+(2232498567/5000000000 : ℝ)*X 1 0+(1957727371/5000000000 : ℝ)*X 1 1+(3915454627/10000000000 : ℝ)*X 1 2+(2232498567/5000000000 : ℝ)*X 2 0+(1957727371/5000000000 : ℝ)*X 2 1+(3915454627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-336679099/2000000000 : ℝ)*X 0 0+(1294484549/2500000000 : ℝ)*X 0 1+(323621129/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5380514093/10000000000 : ℝ)*X 1 0+(-282794049/2000000000 : ℝ)*X 1 1+(5177938967/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5380514003/10000000000 : ℝ)*X 2 0+(2588969447/5000000000 : ℝ)*X 2 1+(-706985233/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3687917283/10000000000 : ℝ)*X 0 0+(16809341/39062500 : ℝ)*X 0 1+(2151595389/5000000000 : ℝ)*X 0 2+(3687917283/10000000000 : ℝ)*X 1 0+(16809341/39062500 : ℝ)*X 1 1+(2151595389/5000000000 : ℝ)*X 1 2+(3687917283/10000000000 : ℝ)*X 2 0+(16809341/39062500 : ℝ)*X 2 1+(2151595389/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-96679873/625000000 : ℝ)*X 0 0+(5006694927/10000000000 : ℝ)*X 0 1+(5451003643/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1039209559/2000000000 : ℝ)*X 1 0+(-322980353/2500000000 : ℝ)*X 1 1+(681375489/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1014853/1953125 : ℝ)*X 2 0+(5451003979/10000000000 : ℝ)*X 2 1+(-1291921919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4601639529/10000000000 : ℝ)*X 0 0+(60072167/156250000 : ℝ)*X 0 1+(768923579/2000000000 : ℝ)*X 0 2+(4601639529/10000000000 : ℝ)*X 1 0+(60072167/156250000 : ℝ)*X 1 1+(768923579/2000000000 : ℝ)*X 1 2+(4601639529/10000000000 : ℝ)*X 2 0+(60072167/156250000 : ℝ)*X 2 1+(768923579/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-590113303/5000000000 : ℝ)*X 0 0+(2786168849/5000000000 : ℝ)*X 0 1+(5153001139/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2698697851/5000000000 : ℝ)*X 1 0+(-284924247/2000000000 : ℝ)*X 1 1+(5153001271/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2698697927/5000000000 : ℝ)*X 2 0+(128825029/250000000 : ℝ)*X 2 1+(-712310589/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1800519961/5000000000 : ℝ)*X 0 0+(4344937773/10000000000 : ℝ)*X 0 1+(2172468737/5000000000 : ℝ)*X 0 2+(1800519961/5000000000 : ℝ)*X 1 0+(4344937773/10000000000 : ℝ)*X 1 1+(2172468737/5000000000 : ℝ)*X 1 2+(1800519961/5000000000 : ℝ)*X 2 0+(4344937773/10000000000 : ℝ)*X 2 1+(2172468737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1726_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66903/100000 : ℝ) ≤ (-2864158741462710992323785559851/4281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4925681/20000000000000 : ℝ)*(upper1) + (4620219/25000000000000 : ℝ)*(upper2) + (25533509/50000000000000 : ℝ)*(upper3) + (6044671/50000000000000 : ℝ)*(lower4) + (27938912756887/2000000000000 : ℝ)*(major0) + (27938912756887/2000000000000 : ℝ)*(major1) + (27938912756887/2000000000000 : ℝ)*(major2) + (106638039/100000000000000 : ℝ)*(sp3) + (423727655310107/20000000000000 : ℝ)*(sp4) + (16551345015723/781250000000 : ℝ)*(sp5) + (2118578976474711/100000000000000 : ℝ)*(sp6) + (697552911898363/100000000000000 : ℝ)*(sp7) + (6611453799/10000000000000 : ℝ)*(sp13) + (3706254739/6250000000000 : ℝ)*(sp14) + (348776509268201/50000000000000 : ℝ)*(f.failure) + (423727655310107/20000000000000 : ℝ)*(f.sum) + (1891011100681/342500000000000000000000000 : ℝ)*base66 + (52069665985236617/8562500000000000000000000000000 : ℝ)*base67 + (6835221012075883/8562500000000000000000000000000 : ℝ)*base70 + (25705083891674117/8562500000000000000000000000000 : ℝ)*base71 + (17125842979/21406250000000000000000000 : ℝ)*base73 + (173215974961299117/8562500000000000000000000000000 : ℝ)*base75 + (19484453933888383/8562500000000000000000000000000 : ℝ)*base78 + (52467560102861617/8562500000000000000000000000000 : ℝ)*base79 + (1265961537577/685000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (35747939/2500000000000000000000 : ℝ)*base90 + (35747939/2500000000000000000000 : ℝ)*base92 + (35747939/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (2351/4000 : ℝ) ≤ (125821387418552078034580016613483/214062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16061509/100000000000000 : ℝ)*(upper0) + (139761/100000000000000 : ℝ)*(lower1) + (53264189/100000000000000 : ℝ)*(upper4) + (1506412609595571/100000000000000 : ℝ)*(major0) + (1506412609595571/100000000000000 : ℝ)*(major1) + (1506412609595571/100000000000000 : ℝ)*(major2) + (280127007370897/12500000000000 : ℝ)*(sp0) + (560253023873899/25000000000000 : ℝ)*(sp1) + (2241017312922961/100000000000000 : ℝ)*(sp2) + (188053268331983/25000000000000 : ℝ)*(sp3) + (1214311789/20000000000000 : ℝ)*(sp5) + (42706579/5000000000000 : ℝ)*(sp6) + (135400383/10000000000000 : ℝ)*(sp7) + (421617473/20000000000000 : ℝ)*(sp8) + (376107213665881/50000000000000 : ℝ)*(f.failure) + (2241018167054541/100000000000000 : ℝ)*(f.sum) + (34026043812399/8562500000000000000000000000 : ℝ)*base66 + (776146480701516339/428125000000000000000000000000000 : ℝ)*base68 + (1409002806239016339/428125000000000000000000000000000 : ℝ)*base70 + (913867157214016339/428125000000000000000000000000000 : ℝ)*base72 + (142755461204923/17125000000000000000000000000 : ℝ)*base74 + (890153347714016339/428125000000000000000000000000000 : ℝ)*base76 + (451689527779733661/428125000000000000000000000000000 : ℝ)*base77 + (1110043276092233661/428125000000000000000000000000000 : ℝ)*base79 + (10402621505887/4281250000000000000000000000 : ℝ)*base82 + (21734541/2500000000000000000000 : ℝ)*base89 + (21734541/2500000000000000000000 : ℝ)*base91 + (21734541/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (16397/20000 : ℝ) ≤ (10969070032037918301675459718863/13378906250000000000000000000000 : ℝ) := by norm_num
    linear_combination (55445717/100000000000000 : ℝ)*(upper1) + (2653603/2500000000000 : ℝ)*(upper2) + (7213723/20000000000000 : ℝ)*(upper3) + (38533071/50000000000000 : ℝ)*(lower5) + (189751264453379/12500000000000 : ℝ)*(major0) + (189751264453379/12500000000000 : ℝ)*(major1) + (189751264453379/12500000000000 : ℝ)*(major2) + (9494703543/50000000000000 : ℝ)*(sp1) + (16088735943/100000000000000 : ℝ)*(sp2) + (1148753903/20000000000000 : ℝ)*(sp3) + (450137084524607/20000000000000 : ℝ)*(sp8) + (2250666433215949/100000000000000 : ℝ)*(sp9) + (562667333471773/25000000000000 : ℝ)*(sp10) + (151599960070693/20000000000000 : ℝ)*(sp11) + (37900277206149/5000000000000 : ℝ)*(f.failure) + (450137084524607/20000000000000 : ℝ)*(f.sum) + (7398838683209/17125000000000000000000000000 : ℝ)*base65 + (135643453402674293/26757812500000000000000000000000 : ℝ)*base68 + (13231522534344959/13378906250000000000000000000000 : ℝ)*base70 + (258921377086207961/53515625000000000000000000000000 : ℝ)*base72 + (34201023500083/8562500000000000000000000000 : ℝ)*base74 + (462929655904176711/53515625000000000000000000000000 : ℝ)*base76 + (111017495818239211/53515625000000000000000000000000 : ℝ)*base78 + (63245840460907459/13378906250000000000000000000000 : ℝ)*base80 + (4544001397521/4281250000000000000000000000 : ℝ)*base81 + (13289/250000000000000000000 : ℝ)*base89 + (13289/250000000000000000000 : ℝ)*base91 + (13289/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-45323/50000 : ℝ) ≤ (-48508561738492527628440249526233/53515625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1002249/50000000000000 : ℝ)*(lower0) + (34422161/100000000000000 : ℝ)*(lower2) + (834531/12500000000000 : ℝ)*(upper3) + (98061347521663/6250000000000 : ℝ)*(major0) + (98061347521663/6250000000000 : ℝ)*(major1) + (98061347521663/6250000000000 : ℝ)*(major2) + (441316547/50000000000000 : ℝ)*(sp0) + (460940293/100000000000000 : ℝ)*(sp5) + (1542321639/100000000000000 : ℝ)*(sp6) + (112871953/100000000000000 : ℝ)*(sp8) + (476943799756073/20000000000000 : ℝ)*(sp12) + (14904497083407/625000000000 : ℝ)*(sp13) + (1192359225981887/50000000000000 : ℝ)*(sp14) + (391728852504451/50000000000000 : ℝ)*(sp15) + (391728852504451/50000000000000 : ℝ)*(f.failure) + (2384719994285413/100000000000000 : ℝ)*(f.sum) + (553430088423/8562500000000000000000000000 : ℝ)*base65 + (241441966556377241/53515625000000000000000000000000 : ℝ)*base67 + (9708823948112721/13378906250000000000000000000000 : ℝ)*base70 + (162691810717060259/53515625000000000000000000000000 : ℝ)*base72 + (63011910699529/17125000000000000000000000000 : ℝ)*base74 + (200132908155341509/53515625000000000000000000000000 : ℝ)*base76 + (99890177157685259/53515625000000000000000000000000 : ℝ)*base78 + (183369463366928567/26757812500000000000000000000000 : ℝ)*base80 + (23060108632077/8562500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (10586689/2500000000000000000000 : ℝ)*base90 + (10586689/2500000000000000000000 : ℝ)*base92 + (10586689/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1726_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100131861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8489/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (633/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66903/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2351/4000 : ℝ) else (16397/20000 : ℝ) ≤ X j i ∧ X j i ≤ (45323/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1726_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1726_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100131861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2123/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10123/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66903/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2351/4000 : ℝ) else (16397/20000 : ℝ) ≤ X j i ∧ X j i ≤ (45323/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1726_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1726_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5423/1024 : ℝ) ≤ p) (hpb : p ≤ (5431/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (100131861/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2123/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10123/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66903/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2351/4000 : ℝ) else (16397/20000 : ℝ) ≤ X j i ∧ X j i ≤ (45323/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1726_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
