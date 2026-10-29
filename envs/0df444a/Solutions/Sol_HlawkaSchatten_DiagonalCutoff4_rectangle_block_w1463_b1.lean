-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1463_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:08:37.948231+00:00
-- url     : https://prove2.me/submissions/e52f2096-899b-4444-a769-409d6c9348a7

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
theorem support_rectangle_w1463_s3_0 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-388601971/2000000000 : ℝ)*x 0 + (1082796623/2000000000 : ℝ)*x 1 + (655083751/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (388601971/2000000000 : ℝ)^4423 ≤ (11860892500891/100000000000000 : ℝ)^3399 := by
    have hnat : (388601971 : ℕ)^4423*100000000000000^3399 ≤ 11860892500891^3399*2000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388601971 2000000000 11860892500891 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082796623/2000000000 : ℝ)^4423 ≤ (11250578462963/25000000000000 : ℝ)^3399 := by
    have hnat : (1082796623 : ℕ)^4423*25000000000000^3399 ≤ 11250578462963^3399*2000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082796623 2000000000 11250578462963 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655083751/1250000000 : ℝ)^4423 ≤ (21568396817897/50000000000000 : ℝ)^3399 := by
    have hnat : (655083751 : ℕ)^4423*50000000000000^3399 ≤ 21568396817897^3399*1250000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655083751 1250000000 21568396817897 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-388601971/2000000000 : ℝ), (1082796623/2000000000 : ℝ), (655083751/1250000000 : ℝ)] ![(11860892500891/100000000000000 : ℝ), (11250578462963/25000000000000 : ℝ), (21568396817897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-388601971/2000000000 : ℝ)|^4423 ≤ (11860892500891/100000000000000 : ℝ)^3399
        have hw : |(-388601971/2000000000 : ℝ)|=(388601971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082796623/2000000000 : ℝ)|^4423 ≤ (11250578462963/25000000000000 : ℝ)^3399
        have hw : |(1082796623/2000000000 : ℝ)|=(1082796623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655083751/1250000000 : ℝ)|^4423 ≤ (21568396817897/50000000000000 : ℝ)^3399
        have hw : |(655083751/1250000000 : ℝ)|=(655083751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s3_1 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267426903/500000000 : ℝ)*x 0 + (-2031363277/10000000000 : ℝ)*x 1 + (655083777/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267426903/500000000 : ℝ)^4423 ≤ (5536965620611/12500000000000 : ℝ)^3399 := by
    have hnat : (267426903 : ℕ)^4423*12500000000000^3399 ≤ 5536965620611^3399*500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267426903 500000000 5536965620611 12500000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2031363277/10000000000 : ℝ)^4423 ≤ (12567479151911/100000000000000 : ℝ)^3399 := by
    have hnat : (2031363277 : ℕ)^4423*100000000000000^3399 ≤ 12567479151911^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031363277 10000000000 12567479151911 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655083777/1250000000 : ℝ)^4423 ≤ (8627359172733/20000000000000 : ℝ)^3399 := by
    have hnat : (655083777 : ℕ)^4423*20000000000000^3399 ≤ 8627359172733^3399*1250000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655083777 1250000000 8627359172733 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267426903/500000000 : ℝ), (-2031363277/10000000000 : ℝ), (655083777/1250000000 : ℝ)] ![(5536965620611/12500000000000 : ℝ), (12567479151911/100000000000000 : ℝ), (8627359172733/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267426903/500000000 : ℝ)|^4423 ≤ (5536965620611/12500000000000 : ℝ)^3399
        have hw : |(267426903/500000000 : ℝ)|=(267426903/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2031363277/10000000000 : ℝ)|^4423 ≤ (12567479151911/100000000000000 : ℝ)^3399
        have hw : |(-2031363277/10000000000 : ℝ)|=(2031363277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655083777/1250000000 : ℝ)|^4423 ≤ (8627359172733/20000000000000 : ℝ)^3399
        have hw : |(655083777/1250000000 : ℝ)|=(655083777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s3_2 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674268961/5000000000 : ℝ)*x 0 + (209626827/400000000 : ℝ)*x 1 + (-2031362851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674268961/5000000000 : ℝ)^4423 ≤ (44295723477681/100000000000000 : ℝ)^3399 := by
    have hnat : (2674268961 : ℕ)^4423*100000000000000^3399 ≤ 44295723477681^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674268961 5000000000 44295723477681 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209626827/400000000 : ℝ)^4423 ≤ (21568400389989/50000000000000 : ℝ)^3399 := by
    have hnat : (209626827 : ℕ)^4423*50000000000000^3399 ≤ 21568400389989^3399*400000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209626827 400000000 21568400389989 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2031362851/10000000000 : ℝ)^4423 ≤ (1256747572237/10000000000000 : ℝ)^3399 := by
    have hnat : (2031362851 : ℕ)^4423*10000000000000^3399 ≤ 1256747572237^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031362851 10000000000 1256747572237 10000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674268961/5000000000 : ℝ), (209626827/400000000 : ℝ), (-2031362851/10000000000 : ℝ)] ![(44295723477681/100000000000000 : ℝ), (21568400389989/50000000000000 : ℝ), (1256747572237/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674268961/5000000000 : ℝ)|^4423 ≤ (44295723477681/100000000000000 : ℝ)^3399
        have hw : |(2674268961/5000000000 : ℝ)|=(2674268961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209626827/400000000 : ℝ)|^4423 ≤ (21568400389989/50000000000000 : ℝ)^3399
        have hw : |(209626827/400000000 : ℝ)|=(209626827/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2031362851/10000000000 : ℝ)|^4423 ≤ (1256747572237/10000000000000 : ℝ)^3399
        have hw : |(-2031362851/10000000000 : ℝ)|=(2031362851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s3_3 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4295413951/10000000000 : ℝ)*x 0 + (256832823/625000000 : ℝ)*x 1 + (4488934059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4295413951/10000000000 : ℝ)^4423 ≤ (665996962989/2000000000000 : ℝ)^3399 := by
    have hnat : (4295413951 : ℕ)^4423*2000000000000^3399 ≤ 665996962989^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4295413951 10000000000 665996962989 2000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256832823/625000000 : ℝ)^4423 ≤ (15717484993207/50000000000000 : ℝ)^3399 := by
    have hnat : (256832823 : ℕ)^4423*50000000000000^3399 ≤ 15717484993207^3399*625000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256832823 625000000 15717484993207 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4488934059/10000000000 : ℝ)^4423 ≤ (7053036368609/20000000000000 : ℝ)^3399 := by
    have hnat : (4488934059 : ℕ)^4423*20000000000000^3399 ≤ 7053036368609^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488934059 10000000000 7053036368609 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4295413951/10000000000 : ℝ), (256832823/625000000 : ℝ), (4488934059/10000000000 : ℝ)] ![(665996962989/2000000000000 : ℝ), (15717484993207/50000000000000 : ℝ), (7053036368609/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4295413951/10000000000 : ℝ)|^4423 ≤ (665996962989/2000000000000 : ℝ)^3399
        have hw : |(4295413951/10000000000 : ℝ)|=(4295413951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(256832823/625000000 : ℝ)|^4423 ≤ (15717484993207/50000000000000 : ℝ)^3399
        have hw : |(256832823/625000000 : ℝ)|=(256832823/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4488934059/10000000000 : ℝ)|^4423 ≤ (7053036368609/20000000000000 : ℝ)^3399
        have hw : |(4488934059/10000000000 : ℝ)|=(4488934059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s3_4 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1943023923/10000000000 : ℝ)*x 0 + (1048270807/2000000000 : ℝ)*x 1 + (2706647701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1943023923/10000000000 : ℝ)^4423 ≤ (2965251062301/25000000000000 : ℝ)^3399 := by
    have hnat : (1943023923 : ℕ)^4423*25000000000000^3399 ≤ 2965251062301^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943023923 10000000000 2965251062301 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048270807/2000000000 : ℝ)^4423 ≤ (21572060169543/50000000000000 : ℝ)^3399 := by
    have hnat : (1048270807 : ℕ)^4423*50000000000000^3399 ≤ 21572060169543^3399*2000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048270807 2000000000 21572060169543 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706647701/5000000000 : ℝ)^4423 ≤ (22497437699233/50000000000000 : ℝ)^3399 := by
    have hnat : (2706647701 : ℕ)^4423*50000000000000^3399 ≤ 22497437699233^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706647701 5000000000 22497437699233 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1943023923/10000000000 : ℝ), (1048270807/2000000000 : ℝ), (2706647701/5000000000 : ℝ)] ![(2965251062301/25000000000000 : ℝ), (21572060169543/50000000000000 : ℝ), (22497437699233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1943023923/10000000000 : ℝ)|^4423 ≤ (2965251062301/25000000000000 : ℝ)^3399
        have hw : |(-1943023923/10000000000 : ℝ)|=(1943023923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048270807/2000000000 : ℝ)|^4423 ≤ (21572060169543/50000000000000 : ℝ)^3399
        have hw : |(1048270807/2000000000 : ℝ)|=(1048270807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706647701/5000000000 : ℝ)|^4423 ≤ (22497437699233/50000000000000 : ℝ)^3399
        have hw : |(2706647701/5000000000 : ℝ)|=(2706647701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s3_5 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325834297/2500000000 : ℝ)*x 0 + (-1858737863/10000000000 : ℝ)*x 1 + (5413295393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325834297/2500000000 : ℝ)^4423 ≤ (43809222543657/100000000000000 : ℝ)^3399 := by
    have hnat : (1325834297 : ℕ)^4423*100000000000000^3399 ≤ 43809222543657^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325834297 2500000000 43809222543657 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1858737863/10000000000 : ℝ)^4423 ≤ (699743883187/6250000000000 : ℝ)^3399 := by
    have hnat : (1858737863 : ℕ)^4423*6250000000000^3399 ≤ 699743883187^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1858737863 10000000000 699743883187 6250000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413295393/10000000000 : ℝ)^4423 ≤ (22497437650561/50000000000000 : ℝ)^3399 := by
    have hnat : (5413295393 : ℕ)^4423*50000000000000^3399 ≤ 22497437650561^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413295393 10000000000 22497437650561 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325834297/2500000000 : ℝ), (-1858737863/10000000000 : ℝ), (5413295393/10000000000 : ℝ)] ![(43809222543657/100000000000000 : ℝ), (699743883187/6250000000000 : ℝ), (22497437650561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325834297/2500000000 : ℝ)|^4423 ≤ (43809222543657/100000000000000 : ℝ)^3399
        have hw : |(1325834297/2500000000 : ℝ)|=(1325834297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1858737863/10000000000 : ℝ)|^4423 ≤ (699743883187/6250000000000 : ℝ)^3399
        have hw : |(-1858737863/10000000000 : ℝ)|=(1858737863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413295393/10000000000 : ℝ)|^4423 ≤ (22497437650561/50000000000000 : ℝ)^3399
        have hw : |(5413295393/10000000000 : ℝ)|=(5413295393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s3_6 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530333621/1000000000 : ℝ)*x 0 + (5413296141/10000000000 : ℝ)*x 1 + (-1858738173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530333621/1000000000 : ℝ)^4423 ≤ (10952303007699/25000000000000 : ℝ)^3399 := by
    have hnat : (530333621 : ℕ)^4423*25000000000000^3399 ≤ 10952303007699^3399*1000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530333621 1000000000 10952303007699 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413296141/10000000000 : ℝ)^4423 ≤ (22497441695749/50000000000000 : ℝ)^3399 := by
    have hnat : (5413296141 : ℕ)^4423*50000000000000^3399 ≤ 22497441695749^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413296141 10000000000 22497441695749 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1858738173/10000000000 : ℝ)^4423 ≤ (559795228039/5000000000000 : ℝ)^3399 := by
    have hnat : (1858738173 : ℕ)^4423*5000000000000^3399 ≤ 559795228039^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1858738173 10000000000 559795228039 5000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530333621/1000000000 : ℝ), (5413296141/10000000000 : ℝ), (-1858738173/10000000000 : ℝ)] ![(10952303007699/25000000000000 : ℝ), (22497441695749/50000000000000 : ℝ), (559795228039/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530333621/1000000000 : ℝ)|^4423 ≤ (10952303007699/25000000000000 : ℝ)^3399
        have hw : |(530333621/1000000000 : ℝ)|=(530333621/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413296141/10000000000 : ℝ)|^4423 ≤ (22497441695749/50000000000000 : ℝ)^3399
        have hw : |(5413296141/10000000000 : ℝ)|=(5413296141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1858738173/10000000000 : ℝ)|^4423 ≤ (559795228039/5000000000000 : ℝ)^3399
        have hw : |(-1858738173/10000000000 : ℝ)|=(1858738173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s3_7 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4295444327/10000000000 : ℝ)*x 0 + (4487437031/10000000000 : ℝ)*x 1 + (4110831637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4295444327/10000000000 : ℝ)^4423 ≤ (8325038645351/25000000000000 : ℝ)^3399 := by
    have hnat : (4295444327 : ℕ)^4423*25000000000000^3399 ≤ 8325038645351^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4295444327 10000000000 8325038645351 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4487437031/10000000000 : ℝ)^4423 ≤ (35249878835903/100000000000000 : ℝ)^3399 := by
    have hnat : (4487437031 : ℕ)^4423*100000000000000^3399 ≤ 35249878835903^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487437031 10000000000 35249878835903 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4110831637/10000000000 : ℝ)^4423 ≤ (31449966575637/100000000000000 : ℝ)^3399 := by
    have hnat : (4110831637 : ℕ)^4423*100000000000000^3399 ≤ 31449966575637^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4110831637 10000000000 31449966575637 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4295444327/10000000000 : ℝ), (4487437031/10000000000 : ℝ), (4110831637/10000000000 : ℝ)] ![(8325038645351/25000000000000 : ℝ), (35249878835903/100000000000000 : ℝ), (31449966575637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4295444327/10000000000 : ℝ)|^4423 ≤ (8325038645351/25000000000000 : ℝ)^3399
        have hw : |(4295444327/10000000000 : ℝ)|=(4295444327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4487437031/10000000000 : ℝ)|^4423 ≤ (35249878835903/100000000000000 : ℝ)^3399
        have hw : |(4487437031/10000000000 : ℝ)|=(4487437031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4110831637/10000000000 : ℝ)|^4423 ≤ (31449966575637/100000000000000 : ℝ)^3399
        have hw : |(4110831637/10000000000 : ℝ)|=(4110831637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1463_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (157/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5271/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11259/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14931/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (157/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5271/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (157/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5271/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (157/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5271/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (157/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5271/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (157/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5271/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (157/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5271/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (5271/50000 : ℝ) ^ (2211/512 : ℝ) ≤ (1508587263955059/25000000000000000000 : ℝ) := by
    have hpowers : (5271/50000 : ℝ)^2211 ≤ (1508587263955059/25000000000000000000 : ℝ)^512 := by
      have hnat : (5271 : ℕ)^2211*25000000000000000000^512 ≤ 1508587263955059^512*50000^2211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5271 50000 1508587263955059 25000000000000000000 2211 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5271/50000 : ℝ)) (X := (1508587263955059/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hpowhi : (157/1000 : ℝ) ^ (2211/512 : ℝ) ≤ (33698124116232899/100000000000000000000 : ℝ) := by
    have hpowers : (157/1000 : ℝ)^2211 ≤ (33698124116232899/100000000000000000000 : ℝ)^512 := by
      have hnat : (157 : ℕ)^2211*100000000000000000000^512 ≤ 33698124116232899^512*1000^2211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        157 1000 33698124116232899 100000000000000000000 2211 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (157/1000 : ℝ)) (X := (33698124116232899/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501508587263955059/12500000000000000000 : ℝ) ≤ (10000279461190711/10000000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (12501508587263955059/12500000000000000000 : ℝ)^512 ≤ (10000279461190711/10000000000000000 : ℝ)^2211 := by
      have hnat : (12501508587263955059 : ℕ)^512*10000000000000000^2211 ≤ 10000279461190711^2211*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501508587263955059 12500000000000000000 10000279461190711 10000000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000279461190711/10000000000000000 : ℝ)) (X := (12501508587263955059/12500000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007946494634410627/20000000000000000000 : ℝ) ≤ (10000919942173711/10000000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (20007946494634410627/20000000000000000000 : ℝ)^512 ≤ (10000919942173711/10000000000000000 : ℝ)^2211 := by
      have hnat : (20007946494634410627 : ℕ)^512*10000000000000000^2211 ≤ 10000919942173711^2211*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007946494634410627 20000000000000000000 10000919942173711 10000000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000919942173711/10000000000000000 : ℝ)) (X := (20007946494634410627/20000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033698124116232899/50000000000000000000 : ℝ) ≤ (10001560423156711/10000000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (50033698124116232899/50000000000000000000 : ℝ)^512 ≤ (10001560423156711/10000000000000000 : ℝ)^2211 := by
      have hnat : (50033698124116232899 : ℕ)^512*10000000000000000^2211 ≤ 10001560423156711^2211*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033698124116232899 50000000000000000000 10001560423156711 10000000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001560423156711/10000000000000000 : ℝ)) (X := (50033698124116232899/50000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1508587263955059/25000000000000000000 : ℝ) ≤ ((25783968779888057669/25790000000000000000 : ℝ)+2*(640480983/515800000000 : ℝ)*(5271/50000 : ℝ))^(2211/512 : ℝ) := by
    rw [show (25783968779888057669/25790000000000000000 : ℝ)+2*(640480983/515800000000 : ℝ)*(5271/50000 : ℝ)=(10000279461190711/10000000000000000 : ℝ) by norm_num, show 1+2*(1508587263955059/25000000000000000000 : ℝ)=(12501508587263955059/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33698124116232899/100000000000000000000 : ℝ)+(1508587263955059/25000000000000000000 : ℝ) ≤ ((25783968779888057669/25790000000000000000 : ℝ)+(640480983/515800000000 : ℝ)*((157/1000 : ℝ)+(5271/50000 : ℝ)))^(2211/512 : ℝ) := by
    rw [show (25783968779888057669/25790000000000000000 : ℝ)+(640480983/515800000000 : ℝ)*((157/1000 : ℝ)+(5271/50000 : ℝ))=(10000919942173711/10000000000000000 : ℝ) by norm_num, show 1+(33698124116232899/100000000000000000000 : ℝ)+(1508587263955059/25000000000000000000 : ℝ)=(20007946494634410627/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33698124116232899/100000000000000000000 : ℝ) ≤ ((25783968779888057669/25790000000000000000 : ℝ)+2*(640480983/515800000000 : ℝ)*(157/1000 : ℝ))^(2211/512 : ℝ) := by
    rw [show (25783968779888057669/25790000000000000000 : ℝ)+2*(640480983/515800000000 : ℝ)*(157/1000 : ℝ)=(10001560423156711/10000000000000000 : ℝ) by norm_num, show 1+2*(33698124116232899/100000000000000000000 : ℝ)=(50033698124116232899/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (25783968779888057669/25790000000000000000 : ℝ)*(X 1 0+X 2 0)+(640480983/515800000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (5271/50000 : ℝ)) (hi := (157/1000 : ℝ)) (c := (25783968779888057669/25790000000000000000 : ℝ)) (alpha := (640480983/515800000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (25783968779888057669/25790000000000000000 : ℝ)*(X 0 1+X 2 1)+(640480983/515800000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (5271/50000 : ℝ)) (hi := (157/1000 : ℝ)) (c := (25783968779888057669/25790000000000000000 : ℝ)) (alpha := (640480983/515800000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (25783968779888057669/25790000000000000000 : ℝ)*(X 0 2+X 1 2)+(640480983/515800000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (5271/50000 : ℝ)) (hi := (157/1000 : ℝ)) (c := (25783968779888057669/25790000000000000000 : ℝ)) (alpha := (640480983/515800000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-388601971/2000000000 : ℝ)*X 0 0+(1082796623/2000000000 : ℝ)*X 0 1+(655083751/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267426903/500000000 : ℝ)*X 1 0+(-2031363277/10000000000 : ℝ)*X 1 1+(655083777/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674268961/5000000000 : ℝ)*X 2 0+(209626827/400000000 : ℝ)*X 2 1+(-2031362851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4295413951/10000000000 : ℝ)*X 0 0+(256832823/625000000 : ℝ)*X 0 1+(4488934059/10000000000 : ℝ)*X 0 2+(4295413951/10000000000 : ℝ)*X 1 0+(256832823/625000000 : ℝ)*X 1 1+(4488934059/10000000000 : ℝ)*X 1 2+(4295413951/10000000000 : ℝ)*X 2 0+(256832823/625000000 : ℝ)*X 2 1+(4488934059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1943023923/10000000000 : ℝ)*X 0 0+(1048270807/2000000000 : ℝ)*X 0 1+(2706647701/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325834297/2500000000 : ℝ)*X 1 0+(-1858737863/10000000000 : ℝ)*X 1 1+(5413295393/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530333621/1000000000 : ℝ)*X 2 0+(5413296141/10000000000 : ℝ)*X 2 1+(-1858738173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4295444327/10000000000 : ℝ)*X 0 0+(4487437031/10000000000 : ℝ)*X 0 1+(4110831637/10000000000 : ℝ)*X 0 2+(4295444327/10000000000 : ℝ)*X 1 0+(4487437031/10000000000 : ℝ)*X 1 1+(4110831637/10000000000 : ℝ)*X 1 2+(4295444327/10000000000 : ℝ)*X 2 0+(4487437031/10000000000 : ℝ)*X 2 1+(4110831637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1808718594484910531286428271/128950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (432108803/25000000000000 : ℝ)*(base19) + (1137632389/100000000000000 : ℝ)*(base23) + (236367427/100000000000000 : ℝ)*(lower2) + (97641453/50000000000000 : ℝ)*(upper3) + (70934383/20000000000000 : ℝ)*(upper5) + (420214961477247/10000000000000 : ℝ)*(major0) + (420214961477247/10000000000000 : ℝ)*(major1) + (420214961477247/10000000000000 : ℝ)*(major2) + (5769936872755041/100000000000000 : ℝ)*(sp0) + (5769978437602637/100000000000000 : ℝ)*(sp1) + (288498951420273/5000000000000 : ℝ)*(sp2) + (329288101316083/12500000000000 : ℝ)*(sp3) + (5411660351/12500000000000 : ℝ)*(sp4) + (2757085611/20000000000000 : ℝ)*(sp7) + (32928982449459/1250000000000 : ℝ)*(f.failure) + (5769980166037849/100000000000000 : ℝ)*(f.sum) + (176086013219/257900000000000000000000000 : ℝ)*base66 + (10957428873442757/257900000000000000000000000000000 : ℝ)*base68 + (92481334462857243/257900000000000000000000000000000 : ℝ)*base69 + (760455922182257243/257900000000000000000000000000000 : ℝ)*base71 + (146544682349/80593750000000000000000000 : ℝ)*base73 + (1011275758923657243/257900000000000000000000000000000 : ℝ)*base75 + (1522214373027742757/257900000000000000000000000000000 : ℝ)*base78 + (860790347087057243/257900000000000000000000000000000 : ℝ)*base79 + (7337525039829/2579000000000000000000000000 : ℝ)*base82 + (1100121/125000000000000000000 : ℝ)*base89 + (1100121/125000000000000000000 : ℝ)*base91 + (1100121/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (843701386061737287789052257/80593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2105279/50000000000000 : ℝ)*(base8) + (1772581/390625000000 : ℝ)*(base21) + (1985351/1562500000000 : ℝ)*(upper2) + (111026411/50000000000000 : ℝ)*(lower4) + (529451478079749/12500000000000 : ℝ)*(major0) + (529451478079749/12500000000000 : ℝ)*(major1) + (529451478079749/12500000000000 : ℝ)*(major2) + (78743073/20000000000000 : ℝ)*(sp0) + (3477089/1562500000000 : ℝ)*(sp1) + (836552827/50000000000000 : ℝ)*(sp2) + (181747716210149/3125000000000 : ℝ)*(sp4) + (2907963547058497/50000000000000 : ℝ)*(sp5) + (58159251897643/1000000000000 : ℝ)*(sp6) + (663823995918229/25000000000000 : ℝ)*(sp7) + (663823995918229/25000000000000 : ℝ)*(f.failure) + (5815927316650691/100000000000000 : ℝ)*(f.sum) + (329487715747/2579000000000000000000000000 : ℝ)*base66 + (2214346499051920081/322375000000000000000000000000000 : ℝ)*base67 + (2646335479756545081/322375000000000000000000000000000 : ℝ)*base69 + (2072586311723545081/322375000000000000000000000000000 : ℝ)*base71 + (1277012321411/1289500000000000000000000000 : ℝ)*base73 + (4469489470576795081/322375000000000000000000000000000 : ℝ)*base75 + (3889891266666954919/322375000000000000000000000000000 : ℝ)*base78 + (3198634133151295081/322375000000000000000000000000000 : ℝ)*base79 + (3165571137799/1289500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (27681249/2500000000000000000000 : ℝ)*base90 + (27681249/2500000000000000000000 : ℝ)*base92 + (27681249/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1463_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (157/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5271/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11259/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14931/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1463_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1463_s4_0 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1943754419/10000000000 : ℝ)*x 0 + (2703771241/5000000000 : ℝ)*x 1 + (5246619683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1943754419/10000000000 : ℝ)^4423 ≤ (11866807235201/100000000000000 : ℝ)^3399 := by
    have hnat : (1943754419 : ℕ)^4423*100000000000000^3399 ≤ 11866807235201^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943754419 10000000000 11866807235201 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703771241/5000000000 : ℝ)^4423 ≤ (22466330859307/50000000000000 : ℝ)^3399 := by
    have hnat : (2703771241 : ℕ)^4423*50000000000000^3399 ≤ 22466330859307^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703771241 5000000000 22466330859307 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246619683/10000000000 : ℝ)^4423 ≤ (43200531030561/100000000000000 : ℝ)^3399 := by
    have hnat : (5246619683 : ℕ)^4423*100000000000000^3399 ≤ 43200531030561^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246619683 10000000000 43200531030561 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1943754419/10000000000 : ℝ), (2703771241/5000000000 : ℝ), (5246619683/10000000000 : ℝ)] ![(11866807235201/100000000000000 : ℝ), (22466330859307/50000000000000 : ℝ), (43200531030561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1943754419/10000000000 : ℝ)|^4423 ≤ (11866807235201/100000000000000 : ℝ)^3399
        have hw : |(-1943754419/10000000000 : ℝ)|=(1943754419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703771241/5000000000 : ℝ)|^4423 ≤ (22466330859307/50000000000000 : ℝ)^3399
        have hw : |(2703771241/5000000000 : ℝ)|=(2703771241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246619683/10000000000 : ℝ)|^4423 ≤ (43200531030561/100000000000000 : ℝ)^3399
        have hw : |(5246619683/10000000000 : ℝ)|=(5246619683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s4_1 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346868613/10000000000 : ℝ)*x 0 + (-1012839361/5000000000 : ℝ)*x 1 + (5246619681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346868613/10000000000 : ℝ)^4423 ≤ (5534716800451/12500000000000 : ℝ)^3399 := by
    have hnat : (5346868613 : ℕ)^4423*12500000000000^3399 ≤ 5534716800451^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346868613 10000000000 5534716800451 12500000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1012839361/5000000000 : ℝ)^4423 ≤ (12521734576799/100000000000000 : ℝ)^3399 := by
    have hnat : (1012839361 : ℕ)^4423*100000000000000^3399 ≤ 12521734576799^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012839361 5000000000 12521734576799 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246619681/10000000000 : ℝ)^4423 ≤ (43200531009131/100000000000000 : ℝ)^3399 := by
    have hnat : (5246619681 : ℕ)^4423*100000000000000^3399 ≤ 43200531009131^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246619681 10000000000 43200531009131 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346868613/10000000000 : ℝ), (-1012839361/5000000000 : ℝ), (5246619681/10000000000 : ℝ)] ![(5534716800451/12500000000000 : ℝ), (12521734576799/100000000000000 : ℝ), (43200531009131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346868613/10000000000 : ℝ)|^4423 ≤ (5534716800451/12500000000000 : ℝ)^3399
        have hw : |(5346868613/10000000000 : ℝ)|=(5346868613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1012839361/5000000000 : ℝ)|^4423 ≤ (12521734576799/100000000000000 : ℝ)^3399
        have hw : |(-1012839361/5000000000 : ℝ)|=(1012839361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246619681/10000000000 : ℝ)|^4423 ≤ (43200531009131/100000000000000 : ℝ)^3399
        have hw : |(5246619681/10000000000 : ℝ)|=(5246619681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s4_2 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668358577/1250000000 : ℝ)*x 0 + (5246619681/10000000000 : ℝ)*x 1 + (-1012839359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668358577/1250000000 : ℝ)^4423 ≤ (8855546887187/20000000000000 : ℝ)^3399 := by
    have hnat : (668358577 : ℕ)^4423*20000000000000^3399 ≤ 8855546887187^3399*1250000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668358577 1250000000 8855546887187 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246619681/10000000000 : ℝ)^4423 ≤ (43200531009131/100000000000000 : ℝ)^3399 := by
    have hnat : (5246619681 : ℕ)^4423*100000000000000^3399 ≤ 43200531009131^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246619681 10000000000 43200531009131 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1012839359/5000000000 : ℝ)^4423 ≤ (782608409039/6250000000000 : ℝ)^3399 := by
    have hnat : (1012839359 : ℕ)^4423*6250000000000^3399 ≤ 782608409039^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012839359 5000000000 782608409039 6250000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668358577/1250000000 : ℝ), (5246619681/10000000000 : ℝ), (-1012839359/5000000000 : ℝ)] ![(8855546887187/20000000000000 : ℝ), (43200531009131/100000000000000 : ℝ), (782608409039/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668358577/1250000000 : ℝ)|^4423 ≤ (8855546887187/20000000000000 : ℝ)^3399
        have hw : |(668358577/1250000000 : ℝ)|=(668358577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246619681/10000000000 : ℝ)|^4423 ≤ (43200531009131/100000000000000 : ℝ)^3399
        have hw : |(5246619681/10000000000 : ℝ)|=(5246619681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1012839359/5000000000 : ℝ)|^4423 ≤ (782608409039/6250000000000 : ℝ)^3399
        have hw : |(-1012839359/5000000000 : ℝ)|=(1012839359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s4_3 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2147935511/5000000000 : ℝ)*x 0 + (4122839629/10000000000 : ℝ)*x 1 + (2237655397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147935511/5000000000 : ℝ)^4423 ≤ (6660891826727/20000000000000 : ℝ)^3399 := by
    have hnat : (2147935511 : ℕ)^4423*20000000000000^3399 ≤ 6660891826727^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147935511 5000000000 6660891826727 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4122839629/10000000000 : ℝ)^4423 ≤ (631391256629/2000000000000 : ℝ)^3399 := by
    have hnat : (4122839629 : ℕ)^4423*2000000000000^3399 ≤ 631391256629^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4122839629 10000000000 631391256629 2000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237655397/5000000000 : ℝ)^4423 ≤ (35125978021399/100000000000000 : ℝ)^3399 := by
    have hnat : (2237655397 : ℕ)^4423*100000000000000^3399 ≤ 35125978021399^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237655397 5000000000 35125978021399 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2147935511/5000000000 : ℝ), (4122839629/10000000000 : ℝ), (2237655397/5000000000 : ℝ)] ![(6660891826727/20000000000000 : ℝ), (631391256629/2000000000000 : ℝ), (35125978021399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2147935511/5000000000 : ℝ)|^4423 ≤ (6660891826727/20000000000000 : ℝ)^3399
        have hw : |(2147935511/5000000000 : ℝ)|=(2147935511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4122839629/10000000000 : ℝ)|^4423 ≤ (631391256629/2000000000000 : ℝ)^3399
        have hw : |(4122839629/10000000000 : ℝ)|=(4122839629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2237655397/5000000000 : ℝ)|^4423 ≤ (35125978021399/100000000000000 : ℝ)^3399
        have hw : |(2237655397/5000000000 : ℝ)|=(2237655397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s4_4 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-388753179/2000000000 : ℝ)*x 0 + (2623604711/5000000000 : ℝ)*x 1 + (1081389927/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (388753179/2000000000 : ℝ)^4423 ≤ (5933449202311/50000000000000 : ℝ)^3399 := by
    have hnat : (388753179 : ℕ)^4423*50000000000000^3399 ≤ 5933449202311^3399*2000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388753179 2000000000 5933449202311 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623604711/5000000000 : ℝ)^4423 ≤ (8641369989009/20000000000000 : ℝ)^3399 := by
    have hnat : (2623604711 : ℕ)^4423*20000000000000^3399 ≤ 8641369989009^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623604711 5000000000 8641369989009 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081389927/2000000000 : ℝ)^4423 ≤ (4492625163883/10000000000000 : ℝ)^3399 := by
    have hnat : (1081389927 : ℕ)^4423*10000000000000^3399 ≤ 4492625163883^3399*2000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081389927 2000000000 4492625163883 10000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-388753179/2000000000 : ℝ), (2623604711/5000000000 : ℝ), (1081389927/2000000000 : ℝ)] ![(5933449202311/50000000000000 : ℝ), (8641369989009/20000000000000 : ℝ), (4492625163883/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-388753179/2000000000 : ℝ)|^4423 ≤ (5933449202311/50000000000000 : ℝ)^3399
        have hw : |(-388753179/2000000000 : ℝ)|=(388753179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623604711/5000000000 : ℝ)|^4423 ≤ (8641369989009/20000000000000 : ℝ)^3399
        have hw : |(2623604711/5000000000 : ℝ)|=(2623604711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081389927/2000000000 : ℝ)|^4423 ≤ (4492625163883/10000000000000 : ℝ)^3399
        have hw : |(1081389927/2000000000 : ℝ)|=(1081389927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s4_5 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304898099/10000000000 : ℝ)*x 0 + (-932674381/5000000000 : ℝ)*x 1 + (1351737409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304898099/10000000000 : ℝ)^4423 ≤ (43826002061381/100000000000000 : ℝ)^3399 := by
    have hnat : (5304898099 : ℕ)^4423*100000000000000^3399 ≤ 43826002061381^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304898099 10000000000 43826002061381 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (932674381/5000000000 : ℝ)^4423 ≤ (5623873134779/50000000000000 : ℝ)^3399 := by
    have hnat : (932674381 : ℕ)^4423*50000000000000^3399 ≤ 5623873134779^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932674381 5000000000 5623873134779 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351737409/2500000000 : ℝ)^4423 ≤ (22463125824821/50000000000000 : ℝ)^3399 := by
    have hnat : (1351737409 : ℕ)^4423*50000000000000^3399 ≤ 22463125824821^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351737409 2500000000 22463125824821 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304898099/10000000000 : ℝ), (-932674381/5000000000 : ℝ), (1351737409/2500000000 : ℝ)] ![(43826002061381/100000000000000 : ℝ), (5623873134779/50000000000000 : ℝ), (22463125824821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304898099/10000000000 : ℝ)|^4423 ≤ (43826002061381/100000000000000 : ℝ)^3399
        have hw : |(5304898099/10000000000 : ℝ)|=(5304898099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-932674381/5000000000 : ℝ)|^4423 ≤ (5623873134779/50000000000000 : ℝ)^3399
        have hw : |(-932674381/5000000000 : ℝ)|=(932674381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351737409/2500000000 : ℝ)|^4423 ≤ (22463125824821/50000000000000 : ℝ)^3399
        have hw : |(1351737409/2500000000 : ℝ)|=(1351737409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s4_6 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060979619/2000000000 : ℝ)*x 0 + (2703474819/5000000000 : ℝ)*x 1 + (-373069753/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060979619/2000000000 : ℝ)^4423 ≤ (43826002018379/100000000000000 : ℝ)^3399 := by
    have hnat : (1060979619 : ℕ)^4423*100000000000000^3399 ≤ 43826002018379^3399*2000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060979619 2000000000 43826002018379 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703474819/5000000000 : ℝ)^4423 ≤ (44926251671267/100000000000000 : ℝ)^3399 := by
    have hnat : (2703474819 : ℕ)^4423*100000000000000^3399 ≤ 44926251671267^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703474819 5000000000 44926251671267 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (373069753/2000000000 : ℝ)^4423 ≤ (5623873146549/50000000000000 : ℝ)^3399 := by
    have hnat : (373069753 : ℕ)^4423*50000000000000^3399 ≤ 5623873146549^3399*2000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373069753 2000000000 5623873146549 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060979619/2000000000 : ℝ), (2703474819/5000000000 : ℝ), (-373069753/2000000000 : ℝ)] ![(43826002018379/100000000000000 : ℝ), (44926251671267/100000000000000 : ℝ), (5623873146549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060979619/2000000000 : ℝ)|^4423 ≤ (43826002018379/100000000000000 : ℝ)^3399
        have hw : |(1060979619/2000000000 : ℝ)|=(1060979619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703474819/5000000000 : ℝ)|^4423 ≤ (44926251671267/100000000000000 : ℝ)^3399
        have hw : |(2703474819/5000000000 : ℝ)|=(2703474819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-373069753/2000000000 : ℝ)|^4423 ≤ (5623873146549/50000000000000 : ℝ)^3399
        have hw : |(-373069753/2000000000 : ℝ)|=(373069753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s4_7 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4295896127/10000000000 : ℝ)*x 0 + (4474019093/10000000000 : ℝ)*x 1 + (4124138113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4295896127/10000000000 : ℝ)^4423 ≤ (3330471240001/10000000000000 : ℝ)^3399 := by
    have hnat : (4295896127 : ℕ)^4423*10000000000000^3399 ≤ 3330471240001^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4295896127 10000000000 3330471240001 10000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4474019093/10000000000 : ℝ)^4423 ≤ (35112785916027/100000000000000 : ℝ)^3399 := by
    have hnat : (4474019093 : ℕ)^4423*100000000000000^3399 ≤ 35112785916027^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474019093 10000000000 35112785916027 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4124138113/10000000000 : ℝ)^4423 ≤ (31582501664377/100000000000000 : ℝ)^3399 := by
    have hnat : (4124138113 : ℕ)^4423*100000000000000^3399 ≤ 31582501664377^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124138113 10000000000 31582501664377 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4295896127/10000000000 : ℝ), (4474019093/10000000000 : ℝ), (4124138113/10000000000 : ℝ)] ![(3330471240001/10000000000000 : ℝ), (35112785916027/100000000000000 : ℝ), (31582501664377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4295896127/10000000000 : ℝ)|^4423 ≤ (3330471240001/10000000000000 : ℝ)^3399
        have hw : |(4295896127/10000000000 : ℝ)|=(4295896127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4474019093/10000000000 : ℝ)|^4423 ≤ (35112785916027/100000000000000 : ℝ)^3399
        have hw : |(4474019093/10000000000 : ℝ)|=(4474019093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4124138113/10000000000 : ℝ)|^4423 ≤ (31582501664377/100000000000000 : ℝ)^3399
        have hw : |(4124138113/10000000000 : ℝ)|=(4124138113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1463_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14931/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11259/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11387/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3699/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14931/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11259/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14931/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11259/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14931/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11259/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14931/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11259/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14931/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11259/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14931/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11259/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11259/100000 : ℝ) ^ (2211/512 : ℝ) ≤ (8017433229922549/100000000000000000000 : ℝ) := by
    have hpowers : (11259/100000 : ℝ)^2211 ≤ (8017433229922549/100000000000000000000 : ℝ)^512 := by
      have hnat : (11259 : ℕ)^2211*100000000000000000000^512 ≤ 8017433229922549^512*100000^2211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11259 100000 8017433229922549 100000000000000000000 2211 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11259/100000 : ℝ)) (X := (8017433229922549/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14931/100000 : ℝ) ^ (2211/512 : ℝ) ≤ (13564039416391867/50000000000000000000 : ℝ) := by
    have hpowers : (14931/100000 : ℝ)^2211 ≤ (13564039416391867/50000000000000000000 : ℝ)^512 := by
      have hnat : (14931 : ℕ)^2211*50000000000000000000^512 ≤ 13564039416391867^512*100000^2211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14931 100000 13564039416391867 50000000000000000000 2211 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14931/100000 : ℝ)) (X := (13564039416391867/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008017433229922549/50000000000000000000 : ℝ) ≤ (10000371295607389/10000000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (50008017433229922549/50000000000000000000 : ℝ)^512 ≤ (10000371295607389/10000000000000000 : ℝ)^2211 := by
      have hnat : (50008017433229922549 : ℕ)^512*10000000000000000^2211 ≤ 10000371295607389^2211*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008017433229922549 50000000000000000000 10000371295607389 10000000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000371295607389/10000000000000000 : ℝ)) (X := (50008017433229922549/50000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035145512062706283/100000000000000000000 : ℝ) ≤ (5000406876363683/5000000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (100035145512062706283/100000000000000000000 : ℝ)^512 ≤ (5000406876363683/5000000000000000 : ℝ)^2211 := by
      have hnat : (100035145512062706283 : ℕ)^512*5000000000000000^2211 ≤ 5000406876363683^2211*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035145512062706283 100000000000000000000 5000406876363683 5000000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000406876363683/5000000000000000 : ℝ)) (X := (100035145512062706283/100000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013564039416391867/25000000000000000000 : ℝ) ≤ (10001256209847343/10000000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (25013564039416391867/25000000000000000000 : ℝ)^512 ≤ (10001256209847343/10000000000000000 : ℝ)^2211 := by
      have hnat : (25013564039416391867 : ℕ)^512*10000000000000000^2211 ≤ 10001256209847343^2211*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013564039416391867 25000000000000000000 10001256209847343 10000000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001256209847343/10000000000000000 : ℝ)) (X := (25013564039416391867/25000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8017433229922549/100000000000000000000 : ℝ) ≤ ((679840743482272043/680000000000000000 : ℝ)+2*(147485706659/122400000000000 : ℝ)*(11259/100000 : ℝ))^(2211/512 : ℝ) := by
    rw [show (679840743482272043/680000000000000000 : ℝ)+2*(147485706659/122400000000000 : ℝ)*(11259/100000 : ℝ)=(10000371295607389/10000000000000000 : ℝ) by norm_num, show 1+2*(8017433229922549/100000000000000000000 : ℝ)=(50008017433229922549/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13564039416391867/50000000000000000000 : ℝ)+(8017433229922549/100000000000000000000 : ℝ) ≤ ((679840743482272043/680000000000000000 : ℝ)+(147485706659/122400000000000 : ℝ)*((14931/100000 : ℝ)+(11259/100000 : ℝ)))^(2211/512 : ℝ) := by
    rw [show (679840743482272043/680000000000000000 : ℝ)+(147485706659/122400000000000 : ℝ)*((14931/100000 : ℝ)+(11259/100000 : ℝ))=(5000406876363683/5000000000000000 : ℝ) by norm_num, show 1+(13564039416391867/50000000000000000000 : ℝ)+(8017433229922549/100000000000000000000 : ℝ)=(100035145512062706283/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13564039416391867/50000000000000000000 : ℝ) ≤ ((679840743482272043/680000000000000000 : ℝ)+2*(147485706659/122400000000000 : ℝ)*(14931/100000 : ℝ))^(2211/512 : ℝ) := by
    rw [show (679840743482272043/680000000000000000 : ℝ)+2*(147485706659/122400000000000 : ℝ)*(14931/100000 : ℝ)=(10001256209847343/10000000000000000 : ℝ) by norm_num, show 1+2*(13564039416391867/50000000000000000000 : ℝ)=(25013564039416391867/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (679840743482272043/680000000000000000 : ℝ)*(X 1 0+X 2 0)+(147485706659/122400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (11259/100000 : ℝ)) (hi := (14931/100000 : ℝ)) (c := (679840743482272043/680000000000000000 : ℝ)) (alpha := (147485706659/122400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (679840743482272043/680000000000000000 : ℝ)*(X 0 1+X 2 1)+(147485706659/122400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (11259/100000 : ℝ)) (hi := (14931/100000 : ℝ)) (c := (679840743482272043/680000000000000000 : ℝ)) (alpha := (147485706659/122400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (679840743482272043/680000000000000000 : ℝ)*(X 0 2+X 1 2)+(147485706659/122400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (11259/100000 : ℝ)) (hi := (14931/100000 : ℝ)) (c := (679840743482272043/680000000000000000 : ℝ)) (alpha := (147485706659/122400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1943754419/10000000000 : ℝ)*X 0 0+(2703771241/5000000000 : ℝ)*X 0 1+(5246619683/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346868613/10000000000 : ℝ)*X 1 0+(-1012839361/5000000000 : ℝ)*X 1 1+(5246619681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668358577/1250000000 : ℝ)*X 2 0+(5246619681/10000000000 : ℝ)*X 2 1+(-1012839359/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2147935511/5000000000 : ℝ)*X 0 0+(4122839629/10000000000 : ℝ)*X 0 1+(2237655397/5000000000 : ℝ)*X 0 2+(2147935511/5000000000 : ℝ)*X 1 0+(4122839629/10000000000 : ℝ)*X 1 1+(2237655397/5000000000 : ℝ)*X 1 2+(2147935511/5000000000 : ℝ)*X 2 0+(4122839629/10000000000 : ℝ)*X 2 1+(2237655397/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-388753179/2000000000 : ℝ)*X 0 0+(2623604711/5000000000 : ℝ)*X 0 1+(1081389927/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304898099/10000000000 : ℝ)*X 1 0+(-932674381/5000000000 : ℝ)*X 1 1+(1351737409/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060979619/2000000000 : ℝ)*X 2 0+(2703474819/5000000000 : ℝ)*X 2 1+(-373069753/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4295896127/10000000000 : ℝ)*X 0 0+(4474019093/10000000000 : ℝ)*X 0 1+(4124138113/10000000000 : ℝ)*X 0 2+(4295896127/10000000000 : ℝ)*X 1 0+(4474019093/10000000000 : ℝ)*X 1 1+(4124138113/10000000000 : ℝ)*X 1 2+(4295896127/10000000000 : ℝ)*X 2 0+(4474019093/10000000000 : ℝ)*X 2 1+(4124138113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (59464303423387127227/25500000000000000000000000 : ℝ) := by norm_num
    linear_combination (406153033/100000000000000 : ℝ)*(base19) + (182587211/50000000000000 : ℝ)*(base23) + (23774977/100000000000000 : ℝ)*(lower2) + (28232779/50000000000000 : ℝ)*(upper3) + (7469683/25000000000000 : ℝ)*(upper5) + (4525648185201041/100000000000000 : ℝ)*(major0) + (4525648185201041/100000000000000 : ℝ)*(major1) + (2262824092600521/50000000000000 : ℝ)*(major2) + (6214168693515007/100000000000000 : ℝ)*(sp0) + (6214176729427083/100000000000000 : ℝ)*(sp1) + (1242835354081139/20000000000000 : ℝ)*(sp2) + (2837115024891473/100000000000000 : ℝ)*(sp3) + (8442065109/100000000000000 : ℝ)*(sp4) + (413219937/10000000000000 : ℝ)*(sp7) + (709279789272711/25000000000000 : ℝ)*(f.failure) + (1553544283895029/25000000000000 : ℝ)*(f.sum) + (30042373183223/12240000000000000000000000000 : ℝ)*base66 + (905143769541690289/204000000000000000000000000000000 : ℝ)*base67 + (1277186074202284627/306000000000000000000000000000000 : ℝ)*base69 + (1796554006437690289/204000000000000000000000000000000 : ℝ)*base71 + (5455890078457/12240000000000000000000000000 : ℝ)*base73 + (432237799059715373/306000000000000000000000000000000 : ℝ)*base76 + (209654439853639949/36000000000000000000000000000000 : ℝ)*base78 + (503181689269639949/36000000000000000000000000000000 : ℝ)*base80 + (222598509613/360000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (29973109/2500000000000000000000 : ℝ)*base89 + (29973109/2500000000000000000000 : ℝ)*base91 + (4973109/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (491201337799782195453336191/102000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (201982871/25000000000000 : ℝ)*(base19) + (43571129/5000000000000 : ℝ)*(base23) + (19988021/20000000000000 : ℝ)*(upper3) + (15532053/50000000000000 : ℝ)*(lower4) + (97299907/100000000000000 : ℝ)*(upper5) + (4559139164992693/100000000000000 : ℝ)*(major0) + (4559139164992693/100000000000000 : ℝ)*(major1) + (4559139164992693/100000000000000 : ℝ)*(major2) + (4237712661/25000000000000 : ℝ)*(sp1) + (3634214099/20000000000000 : ℝ)*(sp2) + (6260163588849939/100000000000000 : ℝ)*(sp4) + (1565036457516953/25000000000000 : ℝ)*(sp5) + (48907379268413/781250000000 : ℝ)*(sp6) + (285811458061213/10000000000000 : ℝ)*(sp7) + (285811458061213/10000000000000 : ℝ)*(f.failure) + (6260163588849939/100000000000000 : ℝ)*(f.sum) + (19192086999913/6120000000000000000000000000 : ℝ)*base66 + (2340567085356986191/612000000000000000000000000000000 : ℝ)*base67 + (3299508394127013809/612000000000000000000000000000000 : ℝ)*base70 + (5611591587707013809/612000000000000000000000000000000 : ℝ)*base72 + (4205200110673/6120000000000000000000000000 : ℝ)*base74 + (58857457499013809/612000000000000000000000000000000 : ℝ)*base76 + (35373685787013809/612000000000000000000000000000000 : ℝ)*base78 + (2423736619128986191/612000000000000000000000000000000 : ℝ)*base79 + (12405337044287/6120000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1585847/1000000000000000000000 : ℝ)*base89 + (1585847/1000000000000000000000 : ℝ)*base91 + (1585847/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1463_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14931/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11259/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3699/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1463_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1463_s5_0 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-388771749/2000000000 : ℝ)*x 0 + (5406598299/10000000000 : ℝ)*x 1 + (2623747549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (388771749/2000000000 : ℝ)^4423 ≤ (185431813187/1562500000000 : ℝ)^3399 := by
    have hnat : (388771749 : ℕ)^4423*1562500000000^3399 ≤ 185431813187^3399*2000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388771749 2000000000 185431813187 1562500000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406598299/10000000000 : ℝ)^4423 ≤ (22461226482357/50000000000000 : ℝ)^3399 := by
    have hnat : (5406598299 : ℕ)^4423*50000000000000^3399 ≤ 22461226482357^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406598299 10000000000 22461226482357 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623747549/5000000000 : ℝ)^4423 ≤ (21604955486513/50000000000000 : ℝ)^3399 := by
    have hnat : (2623747549 : ℕ)^4423*50000000000000^3399 ≤ 21604955486513^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623747549 5000000000 21604955486513 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-388771749/2000000000 : ℝ), (5406598299/10000000000 : ℝ), (2623747549/5000000000 : ℝ)] ![(185431813187/1562500000000 : ℝ), (22461226482357/50000000000000 : ℝ), (21604955486513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-388771749/2000000000 : ℝ)|^4423 ≤ (185431813187/1562500000000 : ℝ)^3399
        have hw : |(-388771749/2000000000 : ℝ)|=(388771749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406598299/10000000000 : ℝ)|^4423 ≤ (22461226482357/50000000000000 : ℝ)^3399
        have hw : |(5406598299/10000000000 : ℝ)|=(5406598299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623747549/5000000000 : ℝ)|^4423 ≤ (21604955486513/50000000000000 : ℝ)^3399
        have hw : |(2623747549/5000000000 : ℝ)|=(2623747549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s5_1 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673311953/5000000000 : ℝ)*x 0 + (-2024840383/10000000000 : ℝ)*x 1 + (5247495091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673311953/5000000000 : ℝ)^4423 ≤ (44275097495157/100000000000000 : ℝ)^3399 := by
    have hnat : (2673311953 : ℕ)^4423*100000000000000^3399 ≤ 44275097495157^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673311953 5000000000 44275097495157 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2024840383/10000000000 : ℝ)^4423 ≤ (6257495795111/50000000000000 : ℝ)^3399 := by
    have hnat : (2024840383 : ℕ)^4423*50000000000000^3399 ≤ 6257495795111^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024840383 10000000000 6257495795111 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247495091/10000000000 : ℝ)^4423 ≤ (2160495544901/5000000000000 : ℝ)^3399 := by
    have hnat : (5247495091 : ℕ)^4423*5000000000000^3399 ≤ 2160495544901^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247495091 10000000000 2160495544901 5000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673311953/5000000000 : ℝ), (-2024840383/10000000000 : ℝ), (5247495091/10000000000 : ℝ)] ![(44275097495157/100000000000000 : ℝ), (6257495795111/50000000000000 : ℝ), (2160495544901/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673311953/5000000000 : ℝ)|^4423 ≤ (44275097495157/100000000000000 : ℝ)^3399
        have hw : |(2673311953/5000000000 : ℝ)|=(2673311953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2024840383/10000000000 : ℝ)|^4423 ≤ (6257495795111/50000000000000 : ℝ)^3399
        have hw : |(-2024840383/10000000000 : ℝ)|=(2024840383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247495091/10000000000 : ℝ)|^4423 ≤ (2160495544901/5000000000000 : ℝ)^3399
        have hw : |(5247495091/10000000000 : ℝ)|=(5247495091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s5_2 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53466239/100000000 : ℝ)*x 0 + (5247495103/10000000000 : ℝ)*x 1 + (-253105047/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53466239/100000000 : ℝ)^4423 ≤ (44275097430503/100000000000000 : ℝ)^3399 := by
    have hnat : (53466239 : ℕ)^4423*100000000000000^3399 ≤ 44275097430503^3399*100000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53466239 100000000 44275097430503 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247495103/10000000000 : ℝ)^4423 ≤ (21604955513301/50000000000000 : ℝ)^3399 := by
    have hnat : (5247495103 : ℕ)^4423*50000000000000^3399 ≤ 21604955513301^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247495103 10000000000 21604955513301 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253105047/1250000000 : ℝ)^4423 ≤ (6257495766961/50000000000000 : ℝ)^3399 := by
    have hnat : (253105047 : ℕ)^4423*50000000000000^3399 ≤ 6257495766961^3399*1250000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253105047 1250000000 6257495766961 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53466239/100000000 : ℝ), (5247495103/10000000000 : ℝ), (-253105047/1250000000 : ℝ)] ![(44275097430503/100000000000000 : ℝ), (21604955513301/50000000000000 : ℝ), (6257495766961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53466239/100000000 : ℝ)|^4423 ≤ (44275097430503/100000000000000 : ℝ)^3399
        have hw : |(53466239/100000000 : ℝ)|=(53466239/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247495103/10000000000 : ℝ)|^4423 ≤ (21604955513301/50000000000000 : ℝ)^3399
        have hw : |(5247495103/10000000000 : ℝ)|=(5247495103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-253105047/1250000000 : ℝ)|^4423 ≤ (6257495766961/50000000000000 : ℝ)^3399
        have hw : |(-253105047/1250000000 : ℝ)|=(253105047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s5_3 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073983833/2500000000 : ℝ)*x 0 + (1031206173/2500000000 : ℝ)*x 1 + (559163799/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073983833/2500000000 : ℝ)^4423 ≤ (8326276978021/25000000000000 : ℝ)^3399 := by
    have hnat : (1073983833 : ℕ)^4423*25000000000000^3399 ≤ 8326276978021^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073983833 2500000000 8326276978021 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031206173/2500000000 : ℝ)^4423 ≤ (3158934362401/10000000000000 : ℝ)^3399 := by
    have hnat : (1031206173 : ℕ)^4423*10000000000000^3399 ≤ 3158934362401^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031206173 2500000000 3158934362401 10000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559163799/1250000000 : ℝ)^4423 ≤ (35105548460423/100000000000000 : ℝ)^3399 := by
    have hnat : (559163799 : ℕ)^4423*100000000000000^3399 ≤ 35105548460423^3399*1250000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559163799 1250000000 35105548460423 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073983833/2500000000 : ℝ), (1031206173/2500000000 : ℝ), (559163799/1250000000 : ℝ)] ![(8326276978021/25000000000000 : ℝ), (3158934362401/10000000000000 : ℝ), (35105548460423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073983833/2500000000 : ℝ)|^4423 ≤ (8326276978021/25000000000000 : ℝ)^3399
        have hw : |(1073983833/2500000000 : ℝ)|=(1073983833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031206173/2500000000 : ℝ)|^4423 ≤ (3158934362401/10000000000000 : ℝ)^3399
        have hw : |(1031206173/2500000000 : ℝ)|=(1031206173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(559163799/1250000000 : ℝ)|^4423 ≤ (35105548460423/100000000000000 : ℝ)^3399
        have hw : |(559163799/1250000000 : ℝ)|=(559163799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s5_4 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1943869847/10000000000 : ℝ)*x 0 + (1312017897/2500000000 : ℝ)*x 1 + (5406018797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1943869847/10000000000 : ℝ)^4423 ≤ (11867724243623/100000000000000 : ℝ)^3399 := by
    have hnat : (1943869847 : ℕ)^4423*100000000000000^3399 ≤ 11867724243623^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943869847 10000000000 11867724243623 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1312017897/2500000000 : ℝ)^4423 ≤ (10804022058927/25000000000000 : ℝ)^3399 := by
    have hnat : (1312017897 : ℕ)^4423*25000000000000^3399 ≤ 10804022058927^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312017897 2500000000 10804022058927 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406018797/10000000000 : ℝ)^4423 ≤ (44916187503281/100000000000000 : ℝ)^3399 := by
    have hnat : (5406018797 : ℕ)^4423*100000000000000^3399 ≤ 44916187503281^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406018797 10000000000 44916187503281 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1943869847/10000000000 : ℝ), (1312017897/2500000000 : ℝ), (5406018797/10000000000 : ℝ)] ![(11867724243623/100000000000000 : ℝ), (10804022058927/25000000000000 : ℝ), (44916187503281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1943869847/10000000000 : ℝ)|^4423 ≤ (11867724243623/100000000000000 : ℝ)^3399
        have hw : |(-1943869847/10000000000 : ℝ)|=(1943869847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1312017897/2500000000 : ℝ)|^4423 ≤ (10804022058927/25000000000000 : ℝ)^3399
        have hw : |(1312017897/2500000000 : ℝ)|=(1312017897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406018797/10000000000 : ℝ)|^4423 ≤ (44916187503281/100000000000000 : ℝ)^3399
        have hw : |(5406018797/10000000000 : ℝ)|=(5406018797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s5_5 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652563863/5000000000 : ℝ)*x 0 + (-373263341/2000000000 : ℝ)*x 1 + (2703009403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652563863/5000000000 : ℝ)^4423 ≤ (10957117659153/25000000000000 : ℝ)^3399 := by
    have hnat : (2652563863 : ℕ)^4423*25000000000000^3399 ≤ 10957117659153^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652563863 5000000000 10957117659153 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (373263341/2000000000 : ℝ)^4423 ≤ (11255341745049/100000000000000 : ℝ)^3399 := by
    have hnat : (373263341 : ℕ)^4423*100000000000000^3399 ≤ 11255341745049^3399*2000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373263341 2000000000 11255341745049 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703009403/5000000000 : ℝ)^4423 ≤ (22458093800293/50000000000000 : ℝ)^3399 := by
    have hnat : (2703009403 : ℕ)^4423*50000000000000^3399 ≤ 22458093800293^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703009403 5000000000 22458093800293 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652563863/5000000000 : ℝ), (-373263341/2000000000 : ℝ), (2703009403/5000000000 : ℝ)] ![(10957117659153/25000000000000 : ℝ), (11255341745049/100000000000000 : ℝ), (22458093800293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652563863/5000000000 : ℝ)|^4423 ≤ (10957117659153/25000000000000 : ℝ)^3399
        have hw : |(2652563863/5000000000 : ℝ)|=(2652563863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-373263341/2000000000 : ℝ)|^4423 ≤ (11255341745049/100000000000000 : ℝ)^3399
        have hw : |(-373263341/2000000000 : ℝ)|=(373263341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703009403/5000000000 : ℝ)|^4423 ≤ (22458093800293/50000000000000 : ℝ)^3399
        have hw : |(2703009403/5000000000 : ℝ)|=(2703009403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s5_6 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82892621/156250000 : ℝ)*x 0 + (5406018773/10000000000 : ℝ)*x 1 + (-1866316727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82892621/156250000 : ℝ)^4423 ≤ (1095711770753/2500000000000 : ℝ)^3399 := by
    have hnat : (82892621 : ℕ)^4423*2500000000000^3399 ≤ 1095711770753^3399*156250000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82892621 156250000 1095711770753 2500000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406018773/10000000000 : ℝ)^4423 ≤ (22458093621901/50000000000000 : ℝ)^3399 := by
    have hnat : (5406018773 : ℕ)^4423*50000000000000^3399 ≤ 22458093621901^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406018773 10000000000 22458093621901 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1866316727/10000000000 : ℝ)^4423 ≤ (11255341917697/100000000000000 : ℝ)^3399 := by
    have hnat : (1866316727 : ℕ)^4423*100000000000000^3399 ≤ 11255341917697^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866316727 10000000000 11255341917697 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82892621/156250000 : ℝ), (5406018773/10000000000 : ℝ), (-1866316727/10000000000 : ℝ)] ![(1095711770753/2500000000000 : ℝ), (22458093621901/50000000000000 : ℝ), (11255341917697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82892621/156250000 : ℝ)|^4423 ≤ (1095711770753/2500000000000 : ℝ)^3399
        have hw : |(82892621/156250000 : ℝ)|=(82892621/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406018773/10000000000 : ℝ)|^4423 ≤ (22458093621901/50000000000000 : ℝ)^3399
        have hw : |(5406018773/10000000000 : ℝ)|=(5406018773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1866316727/10000000000 : ℝ)|^4423 ≤ (11255341917697/100000000000000 : ℝ)^3399
        have hw : |(-1866316727/10000000000 : ℝ)|=(1866316727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s5_7 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2147979797/5000000000 : ℝ)*x 0 + (4472047629/10000000000 : ℝ)*x 1 + (4126094013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147979797/5000000000 : ℝ)^4423 ≤ (8326338168783/25000000000000 : ℝ)^3399 := by
    have hnat : (2147979797 : ℕ)^4423*25000000000000^3399 ≤ 8326338168783^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147979797 5000000000 8326338168783 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4472047629/10000000000 : ℝ)^4423 ≤ (35092653622641/100000000000000 : ℝ)^3399 := by
    have hnat : (4472047629 : ℕ)^4423*100000000000000^3399 ≤ 35092653622641^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4472047629 10000000000 35092653622641 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4126094013/10000000000 : ℝ)^4423 ≤ (31601993680819/100000000000000 : ℝ)^3399 := by
    have hnat : (4126094013 : ℕ)^4423*100000000000000^3399 ≤ 31601993680819^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126094013 10000000000 31601993680819 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2147979797/5000000000 : ℝ), (4472047629/10000000000 : ℝ), (4126094013/10000000000 : ℝ)] ![(8326338168783/25000000000000 : ℝ), (35092653622641/100000000000000 : ℝ), (31601993680819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2147979797/5000000000 : ℝ)|^4423 ≤ (8326338168783/25000000000000 : ℝ)^3399
        have hw : |(2147979797/5000000000 : ℝ)|=(2147979797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4472047629/10000000000 : ℝ)|^4423 ≤ (35092653622641/100000000000000 : ℝ)^3399
        have hw : |(4472047629/10000000000 : ℝ)|=(4472047629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4126094013/10000000000 : ℝ)|^4423 ≤ (31601993680819/100000000000000 : ℝ)^3399
        have hw : |(4126094013/10000000000 : ℝ)|=(4126094013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1463_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3699/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2281/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1847/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3699/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11387/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3699/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11387/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3699/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11387/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3699/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11387/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3699/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11387/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3699/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11387/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11387/100000 : ℝ) ^ (2211/512 : ℝ) ≤ (4209265773376597/50000000000000000000 : ℝ) := by
    have hpowers : (11387/100000 : ℝ)^2211 ≤ (4209265773376597/50000000000000000000 : ℝ)^512 := by
      have hnat : (11387 : ℕ)^2211*50000000000000000000^512 ≤ 4209265773376597^512*100000^2211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11387 100000 4209265773376597 50000000000000000000 2211 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11387/100000 : ℝ)) (X := (4209265773376597/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3699/25000 : ℝ) ^ (2211/512 : ℝ) ≤ (5216929303183333/20000000000000000000 : ℝ) := by
    have hpowers : (3699/25000 : ℝ)^2211 ≤ (5216929303183333/20000000000000000000 : ℝ)^512 := by
      have hnat : (3699 : ℕ)^2211*20000000000000000000^512 ≤ 5216929303183333^512*25000^2211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3699 25000 5216929303183333 20000000000000000000 2211 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3699/25000 : ℝ)) (X := (5216929303183333/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004209265773376597/25000000000000000000 : ℝ) ≤ (5000194934841457/5000000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (25004209265773376597/25000000000000000000 : ℝ)^512 ≤ (5000194934841457/5000000000000000 : ℝ)^2211 := by
      have hnat : (25004209265773376597 : ℕ)^512*5000000000000000^2211 ≤ 5000194934841457^2211*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004209265773376597 25000000000000000000 5000194934841457 5000000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000194934841457/5000000000000000 : ℝ)) (X := (25004209265773376597/25000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034503178062669859/100000000000000000000 : ℝ) ≤ (400031955288601/400000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (100034503178062669859/100000000000000000000 : ℝ)^512 ≤ (400031955288601/400000000000000 : ℝ)^2211 := by
      have hnat : (100034503178062669859 : ℕ)^512*400000000000000^2211 ≤ 400031955288601^2211*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034503178062669859 100000000000000000000 400031955288601 400000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400031955288601/400000000000000 : ℝ)) (X := (100034503178062669859/100000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005216929303183333/10000000000000000000 : ℝ) ≤ (4883402292357/4882812500000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (10005216929303183333/10000000000000000000 : ℝ)^512 ≤ (4883402292357/4882812500000 : ℝ)^2211 := by
      have hnat : (10005216929303183333 : ℕ)^512*4882812500000^2211 ≤ 4883402292357^2211*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005216929303183333 10000000000000000000 4883402292357 4882812500000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (4883402292357/4882812500000 : ℝ)) (X := (10005216929303183333/10000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4209265773376597/50000000000000000000 : ℝ) ≤ ((4260251776792844739/4261250000000000000 : ℝ)+2*(409012532111/340900000000000 : ℝ)*(11387/100000 : ℝ))^(2211/512 : ℝ) := by
    rw [show (4260251776792844739/4261250000000000000 : ℝ)+2*(409012532111/340900000000000 : ℝ)*(11387/100000 : ℝ)=(5000194934841457/5000000000000000 : ℝ) by norm_num, show 1+2*(4209265773376597/50000000000000000000 : ℝ)=(25004209265773376597/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5216929303183333/20000000000000000000 : ℝ)+(4209265773376597/50000000000000000000 : ℝ) ≤ ((4260251776792844739/4261250000000000000 : ℝ)+(409012532111/340900000000000 : ℝ)*((3699/25000 : ℝ)+(11387/100000 : ℝ)))^(2211/512 : ℝ) := by
    rw [show (4260251776792844739/4261250000000000000 : ℝ)+(409012532111/340900000000000 : ℝ)*((3699/25000 : ℝ)+(11387/100000 : ℝ))=(400031955288601/400000000000000 : ℝ) by norm_num, show 1+(5216929303183333/20000000000000000000 : ℝ)+(4209265773376597/50000000000000000000 : ℝ)=(100034503178062669859/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5216929303183333/20000000000000000000 : ℝ) ≤ ((4260251776792844739/4261250000000000000 : ℝ)+2*(409012532111/340900000000000 : ℝ)*(3699/25000 : ℝ))^(2211/512 : ℝ) := by
    rw [show (4260251776792844739/4261250000000000000 : ℝ)+2*(409012532111/340900000000000 : ℝ)*(3699/25000 : ℝ)=(4883402292357/4882812500000 : ℝ) by norm_num, show 1+2*(5216929303183333/20000000000000000000 : ℝ)=(10005216929303183333/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4260251776792844739/4261250000000000000 : ℝ)*(X 1 0+X 2 0)+(409012532111/340900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (11387/100000 : ℝ)) (hi := (3699/25000 : ℝ)) (c := (4260251776792844739/4261250000000000000 : ℝ)) (alpha := (409012532111/340900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4260251776792844739/4261250000000000000 : ℝ)*(X 0 1+X 2 1)+(409012532111/340900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (11387/100000 : ℝ)) (hi := (3699/25000 : ℝ)) (c := (4260251776792844739/4261250000000000000 : ℝ)) (alpha := (409012532111/340900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4260251776792844739/4261250000000000000 : ℝ)*(X 0 2+X 1 2)+(409012532111/340900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (11387/100000 : ℝ)) (hi := (3699/25000 : ℝ)) (c := (4260251776792844739/4261250000000000000 : ℝ)) (alpha := (409012532111/340900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-388771749/2000000000 : ℝ)*X 0 0+(5406598299/10000000000 : ℝ)*X 0 1+(2623747549/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673311953/5000000000 : ℝ)*X 1 0+(-2024840383/10000000000 : ℝ)*X 1 1+(5247495091/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53466239/100000000 : ℝ)*X 2 0+(5247495103/10000000000 : ℝ)*X 2 1+(-253105047/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1073983833/2500000000 : ℝ)*X 0 0+(1031206173/2500000000 : ℝ)*X 0 1+(559163799/1250000000 : ℝ)*X 0 2+(1073983833/2500000000 : ℝ)*X 1 0+(1031206173/2500000000 : ℝ)*X 1 1+(559163799/1250000000 : ℝ)*X 1 2+(1073983833/2500000000 : ℝ)*X 2 0+(1031206173/2500000000 : ℝ)*X 2 1+(559163799/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1943869847/10000000000 : ℝ)*X 0 0+(1312017897/2500000000 : ℝ)*X 0 1+(5406018797/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652563863/5000000000 : ℝ)*X 1 0+(-373263341/2000000000 : ℝ)*X 1 1+(2703009403/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((82892621/156250000 : ℝ)*X 2 0+(5406018773/10000000000 : ℝ)*X 2 1+(-1866316727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2147979797/5000000000 : ℝ)*X 0 0+(4472047629/10000000000 : ℝ)*X 0 1+(4126094013/10000000000 : ℝ)*X 0 2+(2147979797/5000000000 : ℝ)*X 1 0+(4472047629/10000000000 : ℝ)*X 1 1+(4126094013/10000000000 : ℝ)*X 1 2+(2147979797/5000000000 : ℝ)*X 2 0+(4472047629/10000000000 : ℝ)*X 2 1+(4126094013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (978505329148532495952892623/106531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (827920917/50000000000000 : ℝ)*(base19) + (762487889/50000000000000 : ℝ)*(base23) + (66197979/100000000000000 : ℝ)*(lower2) + (225690179/100000000000000 : ℝ)*(upper3) + (144458769/100000000000000 : ℝ)*(upper5) + (4577445810403731/100000000000000 : ℝ)*(major0) + (4577445810403731/100000000000000 : ℝ)*(major1) + (4577445810403731/100000000000000 : ℝ)*(major2) + (6285265209988967/100000000000000 : ℝ)*(sp0) + (3142649340685731/50000000000000 : ℝ)*(sp1) + (3142649406118759/50000000000000 : ℝ)*(sp2) + (2869573680289711/100000000000000 : ℝ)*(sp3) + (35127224329/100000000000000 : ℝ)*(sp4) + (17297132839/100000000000000 : ℝ)*(sp7) + (57391819548451/2000000000000 : ℝ)*(f.failure) + (392831271075831/6250000000000 : ℝ)*(f.sum) + (68303427679159/17045000000000000000000000000 : ℝ)*base66 + (2168563605147083709/426125000000000000000000000000000 : ℝ)*base67 + (1971267188968333709/426125000000000000000000000000000 : ℝ)*base69 + (3140391668302333709/426125000000000000000000000000000 : ℝ)*base71 + (1495179982819/4261250000000000000000000000 : ℝ)*base73 + (4853634784502541291/426125000000000000000000000000000 : ℝ)*base76 + (2876147453070833709/426125000000000000000000000000000 : ℝ)*base77 + (6830523330206958709/426125000000000000000000000000000 : ℝ)*base79 + (3735256594577/8522500000000000000000000000 : ℝ)*base82 + (243831/200000000000000000000 : ℝ)*base90 + (243831/200000000000000000000 : ℝ)*base92 + (243831/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54155645623485292050985677/21306250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12328899/3125000000000 : ℝ)*(base19) + (419185313/100000000000000 : ℝ)*(base23) + (8681451/20000000000000 : ℝ)*(upper3) + (1835953/25000000000000 : ℝ)*(lower4) + (70985001/100000000000000 : ℝ)*(upper5) + (461089542728631/10000000000000 : ℝ)*(major0) + (461089542728631/10000000000000 : ℝ)*(major1) + (461089542728631/10000000000000 : ℝ)*(major2) + (90544679/1000000000000 : ℝ)*(sp1) + (307645743/4000000000000 : ℝ)*(sp2) + (791403787402769/12500000000000 : ℝ)*(sp4) + (1582805212557371/25000000000000 : ℝ)*(sp5) + (395701386805829/6250000000000 : ℝ)*(sp6) + (45165007353511/1562500000000 : ℝ)*(sp7) + (45165007353511/1562500000000 : ℝ)*(f.failure) + (791403787402769/12500000000000 : ℝ)*(f.sum) + (3713711781803/1704500000000000000000000000 : ℝ)*base66 + (180932691713065191/42612500000000000000000000000000 : ℝ)*base68 + (240353441094765191/42612500000000000000000000000000 : ℝ)*base70 + (607801568239465191/42612500000000000000000000000000 : ℝ)*base72 + (1339567362191/1704500000000000000000000000 : ℝ)*base74 + (180523951079015191/42612500000000000000000000000000 : ℝ)*base76 + (216883763485684809/42612500000000000000000000000000 : ℝ)*base77 + (281487892040822309/42612500000000000000000000000000 : ℝ)*base79 + (2956106857867/1704500000000000000000000000 : ℝ)*base82 + (386691/156250000000000000000 : ℝ)*base90 + (386691/156250000000000000000 : ℝ)*base92 + (386691/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1463_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3699/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2281/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1463_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1463_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (157/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5271/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2281/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1463_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1463_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1463_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (157/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5271/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2281/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1463_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
