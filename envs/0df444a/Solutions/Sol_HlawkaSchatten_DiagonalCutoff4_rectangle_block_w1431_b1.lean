-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1431_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:54:24.141877+00:00
-- url     : https://prove2.me/submissions/56e1b97c-6aaf-4ca7-a1be-c3f41bccff43

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
theorem support_rectangle_w1431_s3_0 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1968465597/10000000000 : ℝ)*x 0 + (1083415401/2000000000 : ℝ)*x 1 + (523867709/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1968465597/10000000000 : ℝ)^4391 ≤ (6003743466593/50000000000000 : ℝ)^3367 := by
    have hnat : (1968465597 : ℕ)^4391*50000000000000^3367 ≤ 6003743466593^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968465597 10000000000 6003743466593 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083415401/2000000000 : ℝ)^4391 ≤ (11239200573547/25000000000000 : ℝ)^3367 := by
    have hnat : (1083415401 : ℕ)^4391*25000000000000^3367 ≤ 11239200573547^3367*2000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083415401 2000000000 11239200573547 25000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523867709/1000000000 : ℝ)^4391 ≤ (21517855374851/50000000000000 : ℝ)^3367 := by
    have hnat : (523867709 : ℕ)^4391*50000000000000^3367 ≤ 21517855374851^3367*1000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523867709 1000000000 21517855374851 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1968465597/10000000000 : ℝ), (1083415401/2000000000 : ℝ), (523867709/1000000000 : ℝ)] ![(6003743466593/50000000000000 : ℝ), (11239200573547/25000000000000 : ℝ), (21517855374851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1968465597/10000000000 : ℝ)|^4391 ≤ (6003743466593/50000000000000 : ℝ)^3367
        have hw : |(-1968465597/10000000000 : ℝ)|=(1968465597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083415401/2000000000 : ℝ)|^4391 ≤ (11239200573547/25000000000000 : ℝ)^3367
        have hw : |(1083415401/2000000000 : ℝ)|=(1083415401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523867709/1000000000 : ℝ)|^4391 ≤ (21517855374851/50000000000000 : ℝ)^3367
        have hw : |(523867709/1000000000 : ℝ)|=(523867709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s3_1 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349599021/10000000000 : ℝ)*x 0 + (-1029731833/5000000000 : ℝ)*x 1 + (523867707/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349599021/10000000000 : ℝ)^4391 ≤ (8845574060143/20000000000000 : ℝ)^3367 := by
    have hnat : (5349599021 : ℕ)^4391*20000000000000^3367 ≤ 8845574060143^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349599021 10000000000 8845574060143 20000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029731833/5000000000 : ℝ)^4391 ≤ (2547283829581/20000000000000 : ℝ)^3367 := by
    have hnat : (1029731833 : ℕ)^4391*20000000000000^3367 ≤ 2547283829581^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029731833 5000000000 2547283829581 20000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523867707/1000000000 : ℝ)^4391 ≤ (21517855267717/50000000000000 : ℝ)^3367 := by
    have hnat : (523867707 : ℕ)^4391*50000000000000^3367 ≤ 21517855267717^3367*1000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523867707 1000000000 21517855267717 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349599021/10000000000 : ℝ), (-1029731833/5000000000 : ℝ), (523867707/1000000000 : ℝ)] ![(8845574060143/20000000000000 : ℝ), (2547283829581/20000000000000 : ℝ), (21517855267717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349599021/10000000000 : ℝ)|^4391 ≤ (8845574060143/20000000000000 : ℝ)^3367
        have hw : |(5349599021/10000000000 : ℝ)|=(5349599021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1029731833/5000000000 : ℝ)|^4391 ≤ (2547283829581/20000000000000 : ℝ)^3367
        have hw : |(-1029731833/5000000000 : ℝ)|=(1029731833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523867707/1000000000 : ℝ)|^4391 ≤ (21517855267717/50000000000000 : ℝ)^3367
        have hw : |(523867707/1000000000 : ℝ)|=(523867707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s3_2 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349599057/10000000000 : ℝ)*x 0 + (5238676981/10000000000 : ℝ)*x 1 + (-257432967/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349599057/10000000000 : ℝ)^4391 ≤ (44227870688863/100000000000000 : ℝ)^3367 := by
    have hnat : (5349599057 : ℕ)^4391*100000000000000^3367 ≤ 44227870688863^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349599057 10000000000 44227870688863 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238676981/10000000000 : ℝ)^4391 ≤ (2151785479097/5000000000000 : ℝ)^3367 := by
    have hnat : (5238676981 : ℕ)^4391*5000000000000^3367 ≤ 2151785479097^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238676981 10000000000 2151785479097 5000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257432967/1250000000 : ℝ)^4391 ≤ (12736419712467/100000000000000 : ℝ)^3367 := by
    have hnat : (257432967 : ℕ)^4391*100000000000000^3367 ≤ 12736419712467^3367*1250000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257432967 1250000000 12736419712467 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349599057/10000000000 : ℝ), (5238676981/10000000000 : ℝ), (-257432967/1250000000 : ℝ)] ![(44227870688863/100000000000000 : ℝ), (2151785479097/5000000000000 : ℝ), (12736419712467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349599057/10000000000 : ℝ)|^4391 ≤ (44227870688863/100000000000000 : ℝ)^3367
        have hw : |(5349599057/10000000000 : ℝ)|=(5349599057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238676981/10000000000 : ℝ)|^4391 ≤ (2151785479097/5000000000000 : ℝ)^3367
        have hw : |(5238676981/10000000000 : ℝ)|=(5238676981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-257432967/1250000000 : ℝ)|^4391 ≤ (12736419712467/100000000000000 : ℝ)^3367
        have hw : |(-257432967/1250000000 : ℝ)|=(257432967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s3_3 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2151617587/5000000000 : ℝ)*x 0 + (4114017339/10000000000 : ℝ)*x 1 + (281264899/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151617587/5000000000 : ℝ)^4391 ≤ (4162284993409/12500000000000 : ℝ)^3367 := by
    have hnat : (2151617587 : ℕ)^4391*12500000000000^3367 ≤ 4162284993409^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151617587 5000000000 4162284993409 12500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4114017339/10000000000 : ℝ)^4391 ≤ (1256069058827/4000000000000 : ℝ)^3367 := by
    have hnat : (4114017339 : ℕ)^4391*4000000000000^3367 ≤ 1256069058827^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4114017339 10000000000 1256069058827 4000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281264899/625000000 : ℝ)^4391 ≤ (17649996782401/50000000000000 : ℝ)^3367 := by
    have hnat : (281264899 : ℕ)^4391*50000000000000^3367 ≤ 17649996782401^3367*625000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281264899 625000000 17649996782401 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151617587/5000000000 : ℝ), (4114017339/10000000000 : ℝ), (281264899/625000000 : ℝ)] ![(4162284993409/12500000000000 : ℝ), (1256069058827/4000000000000 : ℝ), (17649996782401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151617587/5000000000 : ℝ)|^4391 ≤ (4162284993409/12500000000000 : ℝ)^3367
        have hw : |(2151617587/5000000000 : ℝ)|=(2151617587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4114017339/10000000000 : ℝ)|^4391 ≤ (1256069058827/4000000000000 : ℝ)^3367
        have hw : |(4114017339/10000000000 : ℝ)|=(4114017339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(281264899/625000000 : ℝ)|^4391 ≤ (17649996782401/50000000000000 : ℝ)^3367
        have hw : |(281264899/625000000 : ℝ)|=(281264899/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s3_4 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1968480533/10000000000 : ℝ)*x 0 + (163730909/312500000 : ℝ)*x 1 + (1083272243/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1968480533/10000000000 : ℝ)^4391 ≤ (2401521150083/20000000000000 : ℝ)^3367 := by
    have hnat : (1968480533 : ℕ)^4391*20000000000000^3367 ≤ 2401521150083^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968480533 10000000000 2401521150083 20000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163730909/312500000 : ℝ)^4391 ≤ (43043338832881/100000000000000 : ℝ)^3367 := by
    have hnat : (163730909 : ℕ)^4391*100000000000000^3367 ≤ 43043338832881^3367*312500000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163730909 312500000 43043338832881 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083272243/2000000000 : ℝ)^4391 ≤ (44949055399993/100000000000000 : ℝ)^3367 := by
    have hnat : (1083272243 : ℕ)^4391*100000000000000^3367 ≤ 44949055399993^3367*2000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083272243 2000000000 44949055399993 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1968480533/10000000000 : ℝ), (163730909/312500000 : ℝ), (1083272243/2000000000 : ℝ)] ![(2401521150083/20000000000000 : ℝ), (43043338832881/100000000000000 : ℝ), (44949055399993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1968480533/10000000000 : ℝ)|^4391 ≤ (2401521150083/20000000000000 : ℝ)^3367
        have hw : |(-1968480533/10000000000 : ℝ)|=(1968480533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163730909/312500000 : ℝ)|^4391 ≤ (43043338832881/100000000000000 : ℝ)^3367
        have hw : |(163730909/312500000 : ℝ)|=(163730909/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083272243/2000000000 : ℝ)|^4391 ≤ (44949055399993/100000000000000 : ℝ)^3367
        have hw : |(1083272243/2000000000 : ℝ)|=(1083272243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s3_5 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165725361/312500000 : ℝ)*x 0 + (-1881779603/10000000000 : ℝ)*x 1 + (2708180587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165725361/312500000 : ℝ)^4391 ≤ (43728386270533/100000000000000 : ℝ)^3367 := by
    have hnat : (165725361 : ℕ)^4391*100000000000000^3367 ≤ 43728386270533^3367*312500000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165725361 312500000 43728386270533 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1881779603/10000000000 : ℝ)^4391 ≤ (11322558756593/100000000000000 : ℝ)^3367 := by
    have hnat : (1881779603 : ℕ)^4391*100000000000000^3367 ≤ 11322558756593^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1881779603 10000000000 11322558756593 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708180587/5000000000 : ℝ)^4391 ≤ (5618631869533/12500000000000 : ℝ)^3367 := by
    have hnat : (2708180587 : ℕ)^4391*12500000000000^3367 ≤ 5618631869533^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708180587 5000000000 5618631869533 12500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165725361/312500000 : ℝ), (-1881779603/10000000000 : ℝ), (2708180587/5000000000 : ℝ)] ![(43728386270533/100000000000000 : ℝ), (11322558756593/100000000000000 : ℝ), (5618631869533/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165725361/312500000 : ℝ)|^4391 ≤ (43728386270533/100000000000000 : ℝ)^3367
        have hw : |(165725361/312500000 : ℝ)|=(165725361/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1881779603/10000000000 : ℝ)|^4391 ≤ (11322558756593/100000000000000 : ℝ)^3367
        have hw : |(-1881779603/10000000000 : ℝ)|=(1881779603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708180587/5000000000 : ℝ)|^4391 ≤ (5618631869533/12500000000000 : ℝ)^3367
        have hw : |(2708180587/5000000000 : ℝ)|=(2708180587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s3_6 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060642247/2000000000 : ℝ)*x 0 + (677045189/1250000000 : ℝ)*x 1 + (-470444893/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060642247/2000000000 : ℝ)^4391 ≤ (43728382861713/100000000000000 : ℝ)^3367 := by
    have hnat : (1060642247 : ℕ)^4391*100000000000000^3367 ≤ 43728382861713^3367*2000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060642247 2000000000 43728382861713 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677045189/1250000000 : ℝ)^4391 ≤ (44949058614317/100000000000000 : ℝ)^3367 := by
    have hnat : (677045189 : ℕ)^4391*100000000000000^3367 ≤ 44949058614317^3367*1250000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677045189 1250000000 44949058614317 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (470444893/2500000000 : ℝ)^4391 ≤ (566127925667/5000000000000 : ℝ)^3367 := by
    have hnat : (470444893 : ℕ)^4391*5000000000000^3367 ≤ 566127925667^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470444893 2500000000 566127925667 5000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060642247/2000000000 : ℝ), (677045189/1250000000 : ℝ), (-470444893/2500000000 : ℝ)] ![(43728382861713/100000000000000 : ℝ), (44949058614317/100000000000000 : ℝ), (566127925667/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060642247/2000000000 : ℝ)|^4391 ≤ (43728382861713/100000000000000 : ℝ)^3367
        have hw : |(1060642247/2000000000 : ℝ)|=(1060642247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677045189/1250000000 : ℝ)|^4391 ≤ (44949058614317/100000000000000 : ℝ)^3367
        have hw : |(677045189/1250000000 : ℝ)|=(677045189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-470444893/2500000000 : ℝ)|^4391 ≤ (566127925667/5000000000000 : ℝ)^3367
        have hw : |(-470444893/2500000000 : ℝ)|=(470444893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s3_7 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2151633987/5000000000 : ℝ)*x 0 + (2249348853/5000000000 : ℝ)*x 1 + (2057783609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151633987/5000000000 : ℝ)^4391 ≤ (33298610942237/100000000000000 : ℝ)^3367 := by
    have hnat : (2151633987 : ℕ)^4391*100000000000000^3367 ≤ 33298610942237^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151633987 5000000000 33298610942237 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249348853/5000000000 : ℝ)^4391 ≤ (35284233837559/100000000000000 : ℝ)^3367 := by
    have hnat : (2249348853 : ℕ)^4391*100000000000000^3367 ≤ 35284233837559^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249348853 5000000000 35284233837559 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2057783609/5000000000 : ℝ)^4391 ≤ (15708577604259/50000000000000 : ℝ)^3367 := by
    have hnat : (2057783609 : ℕ)^4391*50000000000000^3367 ≤ 15708577604259^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057783609 5000000000 15708577604259 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151633987/5000000000 : ℝ), (2249348853/5000000000 : ℝ), (2057783609/5000000000 : ℝ)] ![(33298610942237/100000000000000 : ℝ), (35284233837559/100000000000000 : ℝ), (15708577604259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151633987/5000000000 : ℝ)|^4391 ≤ (33298610942237/100000000000000 : ℝ)^3367
        have hw : |(2151633987/5000000000 : ℝ)|=(2151633987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249348853/5000000000 : ℝ)|^4391 ≤ (35284233837559/100000000000000 : ℝ)^3367
        have hw : |(2249348853/5000000000 : ℝ)|=(2249348853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2057783609/5000000000 : ℝ)|^4391 ≤ (15708577604259/50000000000000 : ℝ)^3367
        have hw : |(2057783609/5000000000 : ℝ)|=(2057783609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1431_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15793/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5189/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11167/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7473/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15793/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5189/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15793/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5189/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15793/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5189/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15793/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5189/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15793/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5189/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15793/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5189/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5189/50000 : ℝ) ^ (2195/512 : ℝ) ≤ (6053013954293539/100000000000000000000 : ℝ) := by
    have hpowers : (5189/50000 : ℝ)^2195 ≤ (6053013954293539/100000000000000000000 : ℝ)^512 := by
      have hnat : (5189 : ℕ)^2195*100000000000000000000^512 ≤ 6053013954293539^512*50000^2195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5189 50000 6053013954293539 100000000000000000000 2195 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5189/50000 : ℝ)) (X := (6053013954293539/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hpowhi : (15793/100000 : ℝ) ^ (2195/512 : ℝ) ≤ (18310501037859197/50000000000000000000 : ℝ) := by
    have hpowers : (15793/100000 : ℝ)^2195 ≤ (18310501037859197/50000000000000000000 : ℝ)^512 := by
      have hnat : (15793 : ℕ)^2195*50000000000000000000^512 ≤ 18310501037859197^512*100000^2195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15793 100000 18310501037859197 50000000000000000000 2195 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15793/100000 : ℝ)) (X := (18310501037859197/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006053013954293539/50000000000000000000 : ℝ) ≤ (500014118447929/500000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (50006053013954293539/50000000000000000000 : ℝ)^512 ≤ (500014118447929/500000000000000 : ℝ)^2195 := by
      have hnat : (50006053013954293539 : ℕ)^512*500000000000000^2195 ≤ 500014118447929^2195*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006053013954293539 50000000000000000000 500014118447929 500000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500014118447929/500000000000000 : ℝ)) (X := (50006053013954293539/50000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042674016030011933/100000000000000000000 : ℝ) ≤ (2500248810052333/2500000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (100042674016030011933/100000000000000000000 : ℝ)^512 ≤ (2500248810052333/2500000000000000 : ℝ)^2195 := by
      have hnat : (100042674016030011933 : ℕ)^512*2500000000000000^2195 ≤ 2500248810052333^2195*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042674016030011933 100000000000000000000 2500248810052333 2500000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500248810052333/2500000000000000 : ℝ)) (X := (100042674016030011933/100000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018310501037859197/25000000000000000000 : ℝ) ≤ (2500427027865021/2500000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (25018310501037859197/25000000000000000000 : ℝ)^512 ≤ (2500427027865021/2500000000000000 : ℝ)^2195 := by
      have hnat : (25018310501037859197 : ℕ)^512*2500000000000000^2195 ≤ 2500427027865021^2195*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018310501037859197 25000000000000000000 2500427027865021 2500000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500427027865021/2500000000000000 : ℝ)) (X := (25018310501037859197/25000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6053013954293539/100000000000000000000 : ℝ) ≤ ((13534183168057525547/13537500000000000000 : ℝ)+2*(11138613293/8460937500000 : ℝ)*(5189/50000 : ℝ))^(2195/512 : ℝ) := by
    rw [show (13534183168057525547/13537500000000000000 : ℝ)+2*(11138613293/8460937500000 : ℝ)*(5189/50000 : ℝ)=(500014118447929/500000000000000 : ℝ) by norm_num, show 1+2*(6053013954293539/100000000000000000000 : ℝ)=(50006053013954293539/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18310501037859197/50000000000000000000 : ℝ)+(6053013954293539/100000000000000000000 : ℝ) ≤ ((13534183168057525547/13537500000000000000 : ℝ)+(11138613293/8460937500000 : ℝ)*((15793/100000 : ℝ)+(5189/50000 : ℝ)))^(2195/512 : ℝ) := by
    rw [show (13534183168057525547/13537500000000000000 : ℝ)+(11138613293/8460937500000 : ℝ)*((15793/100000 : ℝ)+(5189/50000 : ℝ))=(2500248810052333/2500000000000000 : ℝ) by norm_num, show 1+(18310501037859197/50000000000000000000 : ℝ)+(6053013954293539/100000000000000000000 : ℝ)=(100042674016030011933/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18310501037859197/50000000000000000000 : ℝ) ≤ ((13534183168057525547/13537500000000000000 : ℝ)+2*(11138613293/8460937500000 : ℝ)*(15793/100000 : ℝ))^(2195/512 : ℝ) := by
    rw [show (13534183168057525547/13537500000000000000 : ℝ)+2*(11138613293/8460937500000 : ℝ)*(15793/100000 : ℝ)=(2500427027865021/2500000000000000 : ℝ) by norm_num, show 1+2*(18310501037859197/50000000000000000000 : ℝ)=(25018310501037859197/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13534183168057525547/13537500000000000000 : ℝ)*(X 1 0+X 2 0)+(11138613293/8460937500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (5189/50000 : ℝ)) (hi := (15793/100000 : ℝ)) (c := (13534183168057525547/13537500000000000000 : ℝ)) (alpha := (11138613293/8460937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13534183168057525547/13537500000000000000 : ℝ)*(X 0 1+X 2 1)+(11138613293/8460937500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (5189/50000 : ℝ)) (hi := (15793/100000 : ℝ)) (c := (13534183168057525547/13537500000000000000 : ℝ)) (alpha := (11138613293/8460937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13534183168057525547/13537500000000000000 : ℝ)*(X 0 2+X 1 2)+(11138613293/8460937500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (5189/50000 : ℝ)) (hi := (15793/100000 : ℝ)) (c := (13534183168057525547/13537500000000000000 : ℝ)) (alpha := (11138613293/8460937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1968465597/10000000000 : ℝ)*X 0 0+(1083415401/2000000000 : ℝ)*X 0 1+(523867709/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349599021/10000000000 : ℝ)*X 1 0+(-1029731833/5000000000 : ℝ)*X 1 1+(523867707/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349599057/10000000000 : ℝ)*X 2 0+(5238676981/10000000000 : ℝ)*X 2 1+(-257432967/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2151617587/5000000000 : ℝ)*X 0 0+(4114017339/10000000000 : ℝ)*X 0 1+(281264899/625000000 : ℝ)*X 0 2+(2151617587/5000000000 : ℝ)*X 1 0+(4114017339/10000000000 : ℝ)*X 1 1+(281264899/625000000 : ℝ)*X 1 2+(2151617587/5000000000 : ℝ)*X 2 0+(4114017339/10000000000 : ℝ)*X 2 1+(281264899/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1968480533/10000000000 : ℝ)*X 0 0+(163730909/312500000 : ℝ)*X 0 1+(1083272243/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165725361/312500000 : ℝ)*X 1 0+(-1881779603/10000000000 : ℝ)*X 1 1+(2708180587/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060642247/2000000000 : ℝ)*X 2 0+(677045189/1250000000 : ℝ)*X 2 1+(-470444893/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2151633987/5000000000 : ℝ)*X 0 0+(2249348853/5000000000 : ℝ)*X 0 1+(2057783609/5000000000 : ℝ)*X 0 2+(2151633987/5000000000 : ℝ)*X 1 0+(2249348853/5000000000 : ℝ)*X 1 1+(2057783609/5000000000 : ℝ)*X 1 2+(2151633987/5000000000 : ℝ)*X 2 0+(2249348853/5000000000 : ℝ)*X 2 1+(2057783609/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20061142506228418752363/1805000000000000000000000000 : ℝ) := by norm_num
    linear_combination (242293681/12500000000000 : ℝ)*(base19) + (97083411/5000000000000 : ℝ)*(base23) + (40393761/12500000000000 : ℝ)*(upper3) + (18404211/100000000000000 : ℝ)*(upper4) + (44689531/20000000000000 : ℝ)*(upper5) + (409733640201649/10000000000000 : ℝ)*(major0) + (409733640201649/10000000000000 : ℝ)*(major1) + (409733640201649/10000000000000 : ℝ)*(major2) + (5605419575760043/100000000000000 : ℝ)*(sp0) + (5605450760784797/100000000000000 : ℝ)*(sp1) + (224218030298641/4000000000000 : ℝ)*(sp2) + (647301111217737/25000000000000 : ℝ)*(sp3) + (33123374203/100000000000000 : ℝ)*(sp4) + (3822388557/25000000000000 : ℝ)*(sp7) + (103568789377007/4000000000000 : ℝ)*(f.failure) + (1121090539826849/20000000000000 : ℝ)*(f.sum) + (3064128036907/2707500000000000000000000000 : ℝ)*base66 + (1642758252421897997/135375000000000000000000000000000 : ℝ)*base68 + (1662447305053897997/135375000000000000000000000000000 : ℝ)*base70 + (1012388669029852003/135375000000000000000000000000000 : ℝ)*base71 + (19657026581587/2707500000000000000000000000 : ℝ)*base74 + (2184063657842977003/135375000000000000000000000000000 : ℝ)*base75 + (1400894709358147997/135375000000000000000000000000000 : ℝ)*base78 + (10838918950852003/135375000000000000000000000000000 : ℝ)*base79 + (1468117086209/338437500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (404807/40000000000000000000 : ℝ)*base90 + (404807/40000000000000000000 : ℝ)*base92 + (404807/40000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (815439657421918682573320273/56406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1420578413/100000000000000 : ℝ)*(base19) + (677487411/50000000000000 : ℝ)*(base23) + (91055563/50000000000000 : ℝ)*(upper3) + (124096427/100000000000000 : ℝ)*(lower4) + (179960571/100000000000000 : ℝ)*(upper5) + (2065169490354059/50000000000000 : ℝ)*(major0) + (2065169490354059/50000000000000 : ℝ)*(major1) + (2065169490354059/50000000000000 : ℝ)*(major2) + (3136628637/12500000000000 : ℝ)*(sp1) + (29455331817/100000000000000 : ℝ)*(sp2) + (2825301253283961/50000000000000 : ℝ)*(sp4) + (5650575992960413/100000000000000 : ℝ)*(sp5) + (5650571696261283/100000000000000 : ℝ)*(sp6) + (2610074972963371/100000000000000 : ℝ)*(sp7) + (2610074972963371/100000000000000 : ℝ)*(f.failure) + (2825301253283961/50000000000000 : ℝ)*(f.sum) + (10923013388017/3384375000000000000000000000 : ℝ)*base65 + (7926251830189404727/676875000000000000000000000000000 : ℝ)*base68 + (12624478464450654727/676875000000000000000000000000000 : ℝ)*base70 + (4000133857578095273/676875000000000000000000000000000 : ℝ)*base71 + (131298692043589/27075000000000000000000000000 : ℝ)*base74 + (22687097392710654727/676875000000000000000000000000000 : ℝ)*base76 + (440169582300654727/676875000000000000000000000000000 : ℝ)*base78 + (18833489519983779727/676875000000000000000000000000000 : ℝ)*base80 + (20202980288507/13537500000000000000000000000 : ℝ)*base82 + (7763229/1000000000000000000000 : ℝ)*base89 + (7763229/1000000000000000000000 : ℝ)*base91 + (7763229/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1431_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15793/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5189/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7473/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1431_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1431_s4_0 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-196935461/1000000000 : ℝ)*x 0 + (5409474671/10000000000 : ℝ)*x 1 + (5245694009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196935461/1000000000 : ℝ)^4391 ≤ (12014559589387/100000000000000 : ℝ)^3367 := by
    have hnat : (196935461 : ℕ)^4391*100000000000000^3367 ≤ 12014559589387^3367*1000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196935461 1000000000 12014559589387 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409474671/10000000000 : ℝ)^4391 ≤ (44874539217413/100000000000000 : ℝ)^3367 := by
    have hnat : (5409474671 : ℕ)^4391*100000000000000^3367 ≤ 44874539217413^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409474671 10000000000 44874539217413 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245694009/10000000000 : ℝ)^4391 ≤ (21555450588739/50000000000000 : ℝ)^3367 := by
    have hnat : (5245694009 : ℕ)^4391*50000000000000^3367 ≤ 21555450588739^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245694009 10000000000 21555450588739 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-196935461/1000000000 : ℝ), (5409474671/10000000000 : ℝ), (5245694009/10000000000 : ℝ)] ![(12014559589387/100000000000000 : ℝ), (44874539217413/100000000000000 : ℝ), (21555450588739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-196935461/1000000000 : ℝ)|^4391 ≤ (12014559589387/100000000000000 : ℝ)^3367
        have hw : |(-196935461/1000000000 : ℝ)|=(196935461/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409474671/10000000000 : ℝ)|^4391 ≤ (44874539217413/100000000000000 : ℝ)^3367
        have hw : |(5409474671/10000000000 : ℝ)|=(5409474671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245694009/10000000000 : ℝ)|^4391 ≤ (21555450588739/50000000000000 : ℝ)^3367
        have hw : |(5245694009/10000000000 : ℝ)|=(5245694009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s4_1 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336909147/2500000000 : ℝ)*x 0 + (-256595079/1250000000 : ℝ)*x 1 + (2622847063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336909147/2500000000 : ℝ)^4391 ≤ (44206712733623/100000000000000 : ℝ)^3367 := by
    have hnat : (1336909147 : ℕ)^4391*100000000000000^3367 ≤ 44206712733623^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336909147 2500000000 44206712733623 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256595079/1250000000 : ℝ)^4391 ≤ (6341192407737/50000000000000 : ℝ)^3367 := by
    have hnat : (256595079 : ℕ)^4391*50000000000000^3367 ≤ 6341192407737^3367*1250000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256595079 1250000000 6341192407737 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622847063/5000000000 : ℝ)^4391 ≤ (21555451215729/50000000000000 : ℝ)^3367 := by
    have hnat : (2622847063 : ℕ)^4391*50000000000000^3367 ≤ 21555451215729^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622847063 5000000000 21555451215729 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336909147/2500000000 : ℝ), (-256595079/1250000000 : ℝ), (2622847063/5000000000 : ℝ)] ![(44206712733623/100000000000000 : ℝ), (6341192407737/50000000000000 : ℝ), (21555451215729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336909147/2500000000 : ℝ)|^4391 ≤ (44206712733623/100000000000000 : ℝ)^3367
        have hw : |(1336909147/2500000000 : ℝ)|=(1336909147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-256595079/1250000000 : ℝ)|^4391 ≤ (6341192407737/50000000000000 : ℝ)^3367
        have hw : |(-256595079/1250000000 : ℝ)|=(256595079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622847063/5000000000 : ℝ)|^4391 ≤ (21555451215729/50000000000000 : ℝ)^3367
        have hw : |(2622847063/5000000000 : ℝ)|=(2622847063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s4_2 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347636567/10000000000 : ℝ)*x 0 + (2622847079/5000000000 : ℝ)*x 1 + (-1026380309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347636567/10000000000 : ℝ)^4391 ≤ (11051678126807/25000000000000 : ℝ)^3367 := by
    have hnat : (5347636567 : ℕ)^4391*25000000000000^3367 ≤ 11051678126807^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347636567 10000000000 11051678126807 25000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622847079/5000000000 : ℝ)^4391 ≤ (21555451387213/50000000000000 : ℝ)^3367 := by
    have hnat : (2622847079 : ℕ)^4391*50000000000000^3367 ≤ 21555451387213^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622847079 5000000000 21555451387213 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026380309/5000000000 : ℝ)^4391 ≤ (12682384702673/100000000000000 : ℝ)^3367 := by
    have hnat : (1026380309 : ℕ)^4391*100000000000000^3367 ≤ 12682384702673^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026380309 5000000000 12682384702673 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347636567/10000000000 : ℝ), (2622847079/5000000000 : ℝ), (-1026380309/5000000000 : ℝ)] ![(11051678126807/25000000000000 : ℝ), (21555451387213/50000000000000 : ℝ), (12682384702673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347636567/10000000000 : ℝ)|^4391 ≤ (11051678126807/25000000000000 : ℝ)^3367
        have hw : |(5347636567/10000000000 : ℝ)|=(5347636567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622847079/5000000000 : ℝ)|^4391 ≤ (21555451387213/50000000000000 : ℝ)^3367
        have hw : |(2622847079/5000000000 : ℝ)|=(2622847079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1026380309/5000000000 : ℝ)|^4391 ≤ (12682384702673/100000000000000 : ℝ)^3367
        have hw : |(-1026380309/5000000000 : ℝ)|=(1026380309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s4_3 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075945167/2500000000 : ℝ)*x 0 + (2064888131/5000000000 : ℝ)*x 1 + (4484348109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075945167/2500000000 : ℝ)^4391 ≤ (33303784795999/100000000000000 : ℝ)^3367 := by
    have hnat : (1075945167 : ℕ)^4391*100000000000000^3367 ≤ 33303784795999^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075945167 2500000000 33303784795999 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064888131/5000000000 : ℝ)^4391 ≤ (15779342864221/50000000000000 : ℝ)^3367 := by
    have hnat : (2064888131 : ℕ)^4391*50000000000000^3367 ≤ 15779342864221^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064888131 5000000000 15779342864221 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4484348109/10000000000 : ℝ)^4391 ≤ (35137529468879/100000000000000 : ℝ)^3367 := by
    have hnat : (4484348109 : ℕ)^4391*100000000000000^3367 ≤ 35137529468879^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484348109 10000000000 35137529468879 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075945167/2500000000 : ℝ), (2064888131/5000000000 : ℝ), (4484348109/10000000000 : ℝ)] ![(33303784795999/100000000000000 : ℝ), (15779342864221/50000000000000 : ℝ), (35137529468879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075945167/2500000000 : ℝ)|^4391 ≤ (33303784795999/100000000000000 : ℝ)^3367
        have hw : |(1075945167/2500000000 : ℝ)|=(1075945167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2064888131/5000000000 : ℝ)|^4391 ≤ (15779342864221/50000000000000 : ℝ)^3367
        have hw : |(2064888131/5000000000 : ℝ)|=(2064888131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4484348109/10000000000 : ℝ)|^4391 ≤ (35137529468879/100000000000000 : ℝ)^3367
        have hw : |(4484348109/10000000000 : ℝ)|=(4484348109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s4_4 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1969366509/10000000000 : ℝ)*x 0 + (2623147159/5000000000 : ℝ)*x 1 + (5408871177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1969366509/10000000000 : ℝ)^4391 ≤ (750915891249/6250000000000 : ℝ)^3367 := by
    have hnat : (1969366509 : ℕ)^4391*6250000000000^3367 ≤ 750915891249^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1969366509 10000000000 750915891249 6250000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623147159/5000000000 : ℝ)^4391 ≤ (5389666907969/12500000000000 : ℝ)^3367 := by
    have hnat : (2623147159 : ℕ)^4391*12500000000000^3367 ≤ 5389666907969^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623147159 5000000000 5389666907969 12500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408871177/10000000000 : ℝ)^4391 ≤ (4486801045567/10000000000000 : ℝ)^3367 := by
    have hnat : (5408871177 : ℕ)^4391*10000000000000^3367 ≤ 4486801045567^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408871177 10000000000 4486801045567 10000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1969366509/10000000000 : ℝ), (2623147159/5000000000 : ℝ), (5408871177/10000000000 : ℝ)] ![(750915891249/6250000000000 : ℝ), (5389666907969/12500000000000 : ℝ), (4486801045567/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1969366509/10000000000 : ℝ)|^4391 ≤ (750915891249/6250000000000 : ℝ)^3367
        have hw : |(-1969366509/10000000000 : ℝ)|=(1969366509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623147159/5000000000 : ℝ)|^4391 ≤ (5389666907969/12500000000000 : ℝ)^3367
        have hw : |(2623147159/5000000000 : ℝ)|=(2623147159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408871177/10000000000 : ℝ)|^4391 ≤ (4486801045567/10000000000000 : ℝ)^3367
        have hw : |(5408871177/10000000000 : ℝ)|=(5408871177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s4_5 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326262471/2500000000 : ℝ)*x 0 + (-59049487/312500000 : ℝ)*x 1 + (5408871161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326262471/2500000000 : ℝ)^4391 ≤ (683564931049/1562500000000 : ℝ)^3367 := by
    have hnat : (1326262471 : ℕ)^4391*1562500000000^3367 ≤ 683564931049^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326262471 2500000000 683564931049 1562500000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (59049487/312500000 : ℝ)^4391 ≤ (11383834117811/100000000000000 : ℝ)^3367 := by
    have hnat : (59049487 : ℕ)^4391*100000000000000^3367 ≤ 11383834117811^3367*312500000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59049487 312500000 11383834117811 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408871161/10000000000 : ℝ)^4391 ≤ (2243400514129/5000000000000 : ℝ)^3367 := by
    have hnat : (5408871161 : ℕ)^4391*5000000000000^3367 ≤ 2243400514129^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408871161 10000000000 2243400514129 5000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326262471/2500000000 : ℝ), (-59049487/312500000 : ℝ), (5408871161/10000000000 : ℝ)] ![(683564931049/1562500000000 : ℝ), (11383834117811/100000000000000 : ℝ), (2243400514129/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326262471/2500000000 : ℝ)|^4391 ≤ (683564931049/1562500000000 : ℝ)^3367
        have hw : |(1326262471/2500000000 : ℝ)|=(1326262471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-59049487/312500000 : ℝ)|^4391 ≤ (11383834117811/100000000000000 : ℝ)^3367
        have hw : |(-59049487/312500000 : ℝ)|=(59049487/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408871161/10000000000 : ℝ)|^4391 ≤ (2243400514129/5000000000000 : ℝ)^3367
        have hw : |(5408871161/10000000000 : ℝ)|=(5408871161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s4_6 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305049967/10000000000 : ℝ)*x 0 + (1081774221/2000000000 : ℝ)*x 1 + (-1889583547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305049967/10000000000 : ℝ)^4391 ≤ (546851955997/1250000000000 : ℝ)^3367 := by
    have hnat : (5305049967 : ℕ)^4391*1250000000000^3367 ≤ 546851955997^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305049967 10000000000 546851955997 1250000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081774221/2000000000 : ℝ)^4391 ≤ (1402125302399/3125000000000 : ℝ)^3367 := by
    have hnat : (1081774221 : ℕ)^4391*3125000000000^3367 ≤ 1402125302399^3367*2000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081774221 2000000000 1402125302399 3125000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1889583547/10000000000 : ℝ)^4391 ≤ (11383833827111/100000000000000 : ℝ)^3367 := by
    have hnat : (1889583547 : ℕ)^4391*100000000000000^3367 ≤ 11383833827111^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889583547 10000000000 11383833827111 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305049967/10000000000 : ℝ), (1081774221/2000000000 : ℝ), (-1889583547/10000000000 : ℝ)] ![(546851955997/1250000000000 : ℝ), (1402125302399/3125000000000 : ℝ), (11383833827111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305049967/10000000000 : ℝ)|^4391 ≤ (546851955997/1250000000000 : ℝ)^3367
        have hw : |(5305049967/10000000000 : ℝ)|=(5305049967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081774221/2000000000 : ℝ)|^4391 ≤ (1402125302399/3125000000000 : ℝ)^3367
        have hw : |(1081774221/2000000000 : ℝ)|=(1081774221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1889583547/10000000000 : ℝ)|^4391 ≤ (11383833827111/100000000000000 : ℝ)^3367
        have hw : |(-1889583547/10000000000 : ℝ)|=(1889583547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s4_7 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4202936/9765625 : ℝ)*x 0 + (2241524149/5000000000 : ℝ)*x 1 + (4131082801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4202936/9765625 : ℝ)^4391 ≤ (166520225607/500000000000 : ℝ)^3367 := by
    have hnat : (4202936 : ℕ)^4391*500000000000^3367 ≤ 166520225607^3367*9765625^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4202936 9765625 166520225607 500000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241524149/5000000000 : ℝ)^4391 ≤ (548816371569/1562500000000 : ℝ)^3367 := by
    have hnat : (2241524149 : ℕ)^4391*1562500000000^3367 ≤ 548816371569^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241524149 5000000000 548816371569 1562500000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4131082801/10000000000 : ℝ)^4391 ≤ (15785853538657/50000000000000 : ℝ)^3367 := by
    have hnat : (4131082801 : ℕ)^4391*50000000000000^3367 ≤ 15785853538657^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131082801 10000000000 15785853538657 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4202936/9765625 : ℝ), (2241524149/5000000000 : ℝ), (4131082801/10000000000 : ℝ)] ![(166520225607/500000000000 : ℝ), (548816371569/1562500000000 : ℝ), (15785853538657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4202936/9765625 : ℝ)|^4391 ≤ (166520225607/500000000000 : ℝ)^3367
        have hw : |(4202936/9765625 : ℝ)|=(4202936/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2241524149/5000000000 : ℝ)|^4391 ≤ (548816371569/1562500000000 : ℝ)^3367
        have hw : |(2241524149/5000000000 : ℝ)|=(2241524149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4131082801/10000000000 : ℝ)|^4391 ≤ (15785853538657/50000000000000 : ℝ)^3367
        have hw : |(4131082801/10000000000 : ℝ)|=(4131082801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1431_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7473/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11317/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7393/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7473/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11167/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7473/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11167/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7473/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11167/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7473/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11167/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7473/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11167/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7473/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11167/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11167/100000 : ℝ) ^ (2195/512 : ℝ) ≤ (8287045297687439/100000000000000000000 : ℝ) := by
    have hpowers : (11167/100000 : ℝ)^2195 ≤ (8287045297687439/100000000000000000000 : ℝ)^512 := by
      have hnat : (11167 : ℕ)^2195*100000000000000000000^512 ≤ 8287045297687439^512*100000^2195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11167 100000 8287045297687439 100000000000000000000 2195 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11167/100000 : ℝ)) (X := (8287045297687439/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7473/50000 : ℝ) ^ (2195/512 : ℝ) ≤ (14456671024695781/50000000000000000000 : ℝ) := by
    have hpowers : (7473/50000 : ℝ)^2195 ≤ (14456671024695781/50000000000000000000 : ℝ)^512 := by
      have hnat : (7473 : ℕ)^2195*50000000000000000000^512 ≤ 14456671024695781^512*50000^2195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7473 50000 14456671024695781 50000000000000000000 2195 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7473/50000 : ℝ)) (X := (14456671024695781/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008287045297687439/50000000000000000000 : ℝ) ≤ (10000386578370779/10000000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (50008287045297687439/50000000000000000000 : ℝ)^512 ≤ (10000386578370779/10000000000000000 : ℝ)^2195 := by
      have hnat : (50008287045297687439 : ℕ)^512*10000000000000000^2195 ≤ 10000386578370779^2195*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008287045297687439 50000000000000000000 10000386578370779 10000000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000386578370779/10000000000000000 : ℝ)) (X := (50008287045297687439/50000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037200387347079001/100000000000000000000 : ℝ) ≤ (2500216900712693/2500000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (100037200387347079001/100000000000000000000 : ℝ)^512 ≤ (2500216900712693/2500000000000000 : ℝ)^2195 := by
      have hnat : (100037200387347079001 : ℕ)^512*2500000000000000^2195 ≤ 2500216900712693^2195*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037200387347079001 100000000000000000000 2500216900712693 2500000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500216900712693/2500000000000000 : ℝ)) (X := (100037200387347079001/100000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014456671024695781/25000000000000000000 : ℝ) ≤ (2000269725466153/2000000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (25014456671024695781/25000000000000000000 : ℝ)^512 ≤ (2000269725466153/2000000000000000 : ℝ)^2195 := by
      have hnat : (25014456671024695781 : ℕ)^512*2000000000000000^2195 ≤ 2000269725466153^2195*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014456671024695781 25000000000000000000 2000269725466153 2000000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000269725466153/2000000000000000 : ℝ)) (X := (25014456671024695781/25000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8287045297687439/100000000000000000000 : ℝ) ≤ ((37780717678927010179/37790000000000000000 : ℝ)+2*(481024479993/377900000000000 : ℝ)*(11167/100000 : ℝ))^(2195/512 : ℝ) := by
    rw [show (37780717678927010179/37790000000000000000 : ℝ)+2*(481024479993/377900000000000 : ℝ)*(11167/100000 : ℝ)=(10000386578370779/10000000000000000 : ℝ) by norm_num, show 1+2*(8287045297687439/100000000000000000000 : ℝ)=(50008287045297687439/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14456671024695781/50000000000000000000 : ℝ)+(8287045297687439/100000000000000000000 : ℝ) ≤ ((37780717678927010179/37790000000000000000 : ℝ)+(481024479993/377900000000000 : ℝ)*((7473/50000 : ℝ)+(11167/100000 : ℝ)))^(2195/512 : ℝ) := by
    rw [show (37780717678927010179/37790000000000000000 : ℝ)+(481024479993/377900000000000 : ℝ)*((7473/50000 : ℝ)+(11167/100000 : ℝ))=(2500216900712693/2500000000000000 : ℝ) by norm_num, show 1+(14456671024695781/50000000000000000000 : ℝ)+(8287045297687439/100000000000000000000 : ℝ)=(100037200387347079001/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14456671024695781/50000000000000000000 : ℝ) ≤ ((37780717678927010179/37790000000000000000 : ℝ)+2*(481024479993/377900000000000 : ℝ)*(7473/50000 : ℝ))^(2195/512 : ℝ) := by
    rw [show (37780717678927010179/37790000000000000000 : ℝ)+2*(481024479993/377900000000000 : ℝ)*(7473/50000 : ℝ)=(2000269725466153/2000000000000000 : ℝ) by norm_num, show 1+2*(14456671024695781/50000000000000000000 : ℝ)=(25014456671024695781/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37780717678927010179/37790000000000000000 : ℝ)*(X 1 0+X 2 0)+(481024479993/377900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (11167/100000 : ℝ)) (hi := (7473/50000 : ℝ)) (c := (37780717678927010179/37790000000000000000 : ℝ)) (alpha := (481024479993/377900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37780717678927010179/37790000000000000000 : ℝ)*(X 0 1+X 2 1)+(481024479993/377900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (11167/100000 : ℝ)) (hi := (7473/50000 : ℝ)) (c := (37780717678927010179/37790000000000000000 : ℝ)) (alpha := (481024479993/377900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37780717678927010179/37790000000000000000 : ℝ)*(X 0 2+X 1 2)+(481024479993/377900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (11167/100000 : ℝ)) (hi := (7473/50000 : ℝ)) (c := (37780717678927010179/37790000000000000000 : ℝ)) (alpha := (481024479993/377900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-196935461/1000000000 : ℝ)*X 0 0+(5409474671/10000000000 : ℝ)*X 0 1+(5245694009/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336909147/2500000000 : ℝ)*X 1 0+(-256595079/1250000000 : ℝ)*X 1 1+(2622847063/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347636567/10000000000 : ℝ)*X 2 0+(2622847079/5000000000 : ℝ)*X 2 1+(-1026380309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1075945167/2500000000 : ℝ)*X 0 0+(2064888131/5000000000 : ℝ)*X 0 1+(4484348109/10000000000 : ℝ)*X 0 2+(1075945167/2500000000 : ℝ)*X 1 0+(2064888131/5000000000 : ℝ)*X 1 1+(4484348109/10000000000 : ℝ)*X 1 2+(1075945167/2500000000 : ℝ)*X 2 0+(2064888131/5000000000 : ℝ)*X 2 1+(4484348109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1969366509/10000000000 : ℝ)*X 0 0+(2623147159/5000000000 : ℝ)*X 0 1+(5408871177/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326262471/2500000000 : ℝ)*X 1 0+(-59049487/312500000 : ℝ)*X 1 1+(5408871161/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305049967/10000000000 : ℝ)*X 2 0+(1081774221/2000000000 : ℝ)*X 2 1+(-1889583547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4202936/9765625 : ℝ)*X 0 0+(2241524149/5000000000 : ℝ)*X 0 1+(4131082801/10000000000 : ℝ)*X 0 2+(4202936/9765625 : ℝ)*X 1 0+(2241524149/5000000000 : ℝ)*X 1 1+(4131082801/10000000000 : ℝ)*X 1 2+(4202936/9765625 : ℝ)*X 2 0+(2241524149/5000000000 : ℝ)*X 2 1+(4131082801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9336226611590068913374388397/944750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (394128783/25000000000000 : ℝ)*(base19) + (719180821/50000000000000 : ℝ)*(base23) + (61057287/100000000000000 : ℝ)*(lower2) + (222601731/100000000000000 : ℝ)*(upper3) + (153072899/100000000000000 : ℝ)*(upper5) + (4463069001652219/100000000000000 : ℝ)*(major0) + (4463069001652219/100000000000000 : ℝ)*(major1) + (4463069001652219/100000000000000 : ℝ)*(major2) + (6105764766255877/100000000000000 : ℝ)*(sp0) + (1526449964766449/25000000000000 : ℝ)*(sp1) + (6105799997219287/100000000000000 : ℝ)*(sp2) + (1410159396084661/50000000000000 : ℝ)*(sp3) + (36669325051/100000000000000 : ℝ)*(sp4) + (2180768359/12500000000000 : ℝ)*(sp7) + (2820336238316193/100000000000000 : ℝ)*(f.failure) + (11925393428869/195312500000 : ℝ)*(f.sum) + (36852125727079/9447500000000000000000000000 : ℝ)*base66 + (43355920881282637201/3779000000000000000000000000000000 : ℝ)*base67 + (55980628036567637201/3779000000000000000000000000000000 : ℝ)*base69 + (15639113218530362799/3779000000000000000000000000000000 : ℝ)*base72 + (43412109833007/18895000000000000000000000000 : ℝ)*base73 + (70390641393663637201/3779000000000000000000000000000000 : ℝ)*base75 + (9718265190970637201/3779000000000000000000000000000000 : ℝ)*base77 + (51034570516363637201/3779000000000000000000000000000000 : ℝ)*base79 + (23905221095113/18895000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (568393/1000000000000000000000 : ℝ)*base90 + (568393/1000000000000000000000 : ℝ)*base92 + (568393/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (467034692552473378821816039/236187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (321289943/100000000000000 : ℝ)*(base19) + (452276247/100000000000000 : ℝ)*(base23) + (7901379/100000000000000 : ℝ)*(upper3) + (19256513/100000000000000 : ℝ)*(lower4) + (98829393/100000000000000 : ℝ)*(upper5) + (1124015902231553/25000000000000 : ℝ)*(major0) + (1124015902231553/25000000000000 : ℝ)*(major1) + (1124015902231553/25000000000000 : ℝ)*(major2) + (1590486891/20000000000000 : ℝ)*(sp1) + (7759804223/100000000000000 : ℝ)*(sp2) + (246037628497737/4000000000000 : ℝ)*(sp4) + (6150932438719027/100000000000000 : ℝ)*(sp5) + (1537733125090739/25000000000000 : ℝ)*(sp6) + (284118643949601/10000000000000 : ℝ)*(sp7) + (284118643949601/10000000000000 : ℝ)*(f.failure) + (246037628497737/4000000000000 : ℝ)*(f.sum) + (11777991599591/18895000000000000000000000000 : ℝ)*base65 + (5930224474041377987/944750000000000000000000000000000 : ℝ)*base67 + (6870028608592627987/944750000000000000000000000000000 : ℝ)*base69 + (5707130341760877987/944750000000000000000000000000000 : ℝ)*base71 + (1296097639593/590468750000000000000000000 : ℝ)*base73 + (1021902864065627987/944750000000000000000000000000000 : ℝ)*base75 + (307962990942872013/944750000000000000000000000000000 : ℝ)*base78 + (3982474529677377987/944750000000000000000000000000000 : ℝ)*base79 + (19568347483309/4723750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (34999/100000000000000000000 : ℝ)*base89 + (34999/100000000000000000000 : ℝ)*base91 + (34999/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1431_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7473/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7393/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1431_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1431_s5_0 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-984744917/5000000000 : ℝ)*x 0 + (2704146321/5000000000 : ℝ)*x 1 + (1049357337/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (984744917/5000000000 : ℝ)^4391 ≤ (3003908866561/25000000000000 : ℝ)^3367 := by
    have hnat : (984744917 : ℕ)^4391*25000000000000^3367 ≤ 3003908866561^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984744917 5000000000 3003908866561 25000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704146321/5000000000 : ℝ)^4391 ≤ (2243087595757/5000000000000 : ℝ)^3367 := by
    have hnat : (2704146321 : ℕ)^4391*5000000000000^3367 ≤ 2243087595757^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704146321 5000000000 2243087595757 5000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049357337/2000000000 : ℝ)^4391 ≤ (4312261259941/10000000000000 : ℝ)^3367 := by
    have hnat : (1049357337 : ℕ)^4391*10000000000000^3367 ≤ 4312261259941^3367*2000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049357337 2000000000 4312261259941 10000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-984744917/5000000000 : ℝ), (2704146321/5000000000 : ℝ), (1049357337/2000000000 : ℝ)] ![(3003908866561/25000000000000 : ℝ), (2243087595757/5000000000000 : ℝ), (4312261259941/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-984744917/5000000000 : ℝ)|^4391 ≤ (3003908866561/25000000000000 : ℝ)^3367
        have hw : |(-984744917/5000000000 : ℝ)|=(984744917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704146321/5000000000 : ℝ)|^4391 ≤ (2243087595757/5000000000000 : ℝ)^3367
        have hw : |(2704146321/5000000000 : ℝ)|=(2704146321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049357337/2000000000 : ℝ)|^4391 ≤ (4312261259941/10000000000000 : ℝ)^3367
        have hw : |(1049357337/2000000000 : ℝ)|=(1049357337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s5_1 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336832587/2500000000 : ℝ)*x 0 + (-2051716691/10000000000 : ℝ)*x 1 + (2623393429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336832587/2500000000 : ℝ)^4391 ≤ (22101705641561/50000000000000 : ℝ)^3367 := by
    have hnat : (1336832587 : ℕ)^4391*50000000000000^3367 ≤ 22101705641561^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336832587 2500000000 22101705641561 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2051716691/10000000000 : ℝ)^4391 ≤ (3168493561991/25000000000000 : ℝ)^3367 := by
    have hnat : (2051716691 : ℕ)^4391*25000000000000^3367 ≤ 3168493561991^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051716691 10000000000 3168493561991 25000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623393429/5000000000 : ℝ)^4391 ≤ (21561307226851/50000000000000 : ℝ)^3367 := by
    have hnat : (2623393429 : ℕ)^4391*50000000000000^3367 ≤ 21561307226851^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623393429 5000000000 21561307226851 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336832587/2500000000 : ℝ), (-2051716691/10000000000 : ℝ), (2623393429/5000000000 : ℝ)] ![(22101705641561/50000000000000 : ℝ), (3168493561991/25000000000000 : ℝ), (21561307226851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336832587/2500000000 : ℝ)|^4391 ≤ (22101705641561/50000000000000 : ℝ)^3367
        have hw : |(1336832587/2500000000 : ℝ)|=(1336832587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2051716691/10000000000 : ℝ)|^4391 ≤ (3168493561991/25000000000000 : ℝ)^3367
        have hw : |(-2051716691/10000000000 : ℝ)|=(2051716691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623393429/5000000000 : ℝ)|^4391 ≤ (21561307226851/50000000000000 : ℝ)^3367
        have hw : |(2623393429/5000000000 : ℝ)|=(2623393429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s5_2 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347330579/10000000000 : ℝ)*x 0 + (5246786677/10000000000 : ℝ)*x 1 + (-2051716623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347330579/10000000000 : ℝ)^4391 ≤ (22101706886709/50000000000000 : ℝ)^3367 := by
    have hnat : (5347330579 : ℕ)^4391*50000000000000^3367 ≤ 22101706886709^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347330579 10000000000 22101706886709 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246786677/10000000000 : ℝ)^4391 ≤ (21561306256831/50000000000000 : ℝ)^3367 := by
    have hnat : (5246786677 : ℕ)^4391*50000000000000^3367 ≤ 21561306256831^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246786677 10000000000 21561306256831 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2051716623/10000000000 : ℝ)^4391 ≤ (12673973700161/100000000000000 : ℝ)^3367 := by
    have hnat : (2051716623 : ℕ)^4391*100000000000000^3367 ≤ 12673973700161^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051716623 10000000000 12673973700161 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347330579/10000000000 : ℝ), (5246786677/10000000000 : ℝ), (-2051716623/10000000000 : ℝ)] ![(22101706886709/50000000000000 : ℝ), (21561306256831/50000000000000 : ℝ), (12673973700161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347330579/10000000000 : ℝ)|^4391 ≤ (22101706886709/50000000000000 : ℝ)^3367
        have hw : |(5347330579/10000000000 : ℝ)|=(5347330579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246786677/10000000000 : ℝ)|^4391 ≤ (21561306256831/50000000000000 : ℝ)^3367
        have hw : |(5246786677/10000000000 : ℝ)|=(5246786677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2051716623/10000000000 : ℝ)|^4391 ≤ (12673973700161/100000000000000 : ℝ)^3367
        have hw : |(-2051716623/10000000000 : ℝ)|=(2051716623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s5_3 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4303861673/10000000000 : ℝ)*x 0 + (165289151/400000000 : ℝ)*x 1 + (4481875847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4303861673/10000000000 : ℝ)^4391 ≤ (16652301137731/50000000000000 : ℝ)^3367 := by
    have hnat : (4303861673 : ℕ)^4391*50000000000000^3367 ≤ 16652301137731^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303861673 10000000000 16652301137731 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (165289151/400000000 : ℝ)^4391 ≤ (15791564609833/50000000000000 : ℝ)^3367 := by
    have hnat : (165289151 : ℕ)^4391*50000000000000^3367 ≤ 15791564609833^3367*400000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165289151 400000000 15791564609833 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4481875847/10000000000 : ℝ)^4391 ≤ (35112268482557/100000000000000 : ℝ)^3367 := by
    have hnat : (4481875847 : ℕ)^4391*100000000000000^3367 ≤ 35112268482557^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481875847 10000000000 35112268482557 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4303861673/10000000000 : ℝ), (165289151/400000000 : ℝ), (4481875847/10000000000 : ℝ)] ![(16652301137731/50000000000000 : ℝ), (15791564609833/50000000000000 : ℝ), (35112268482557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4303861673/10000000000 : ℝ)|^4391 ≤ (16652301137731/50000000000000 : ℝ)^3367
        have hw : |(4303861673/10000000000 : ℝ)|=(4303861673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(165289151/400000000 : ℝ)|^4391 ≤ (15791564609833/50000000000000 : ℝ)^3367
        have hw : |(165289151/400000000 : ℝ)|=(165289151/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4481875847/10000000000 : ℝ)|^4391 ≤ (35112268482557/100000000000000 : ℝ)^3367
        have hw : |(4481875847/10000000000 : ℝ)|=(4481875847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s5_4 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-246187623/1250000000 : ℝ)*x 0 + (5247370809/10000000000 : ℝ)*x 1 + (270385283/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (246187623/1250000000 : ℝ)^4391 ≤ (12015724179509/100000000000000 : ℝ)^3367 := by
    have hnat : (246187623 : ℕ)^4391*100000000000000^3367 ≤ 12015724179509^3367*1250000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246187623 1250000000 12015724179509 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247370809/10000000000 : ℝ)^4391 ≤ (8625774721833/20000000000000 : ℝ)^3367 := by
    have hnat : (5247370809 : ℕ)^4391*20000000000000^3367 ≤ 8625774721833^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247370809 10000000000 8625774721833 20000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270385283/500000000 : ℝ)^4391 ≤ (22427701101899/50000000000000 : ℝ)^3367 := by
    have hnat : (270385283 : ℕ)^4391*50000000000000^3367 ≤ 22427701101899^3367*500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270385283 500000000 22427701101899 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-246187623/1250000000 : ℝ), (5247370809/10000000000 : ℝ), (270385283/500000000 : ℝ)] ![(12015724179509/100000000000000 : ℝ), (8625774721833/20000000000000 : ℝ), (22427701101899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-246187623/1250000000 : ℝ)|^4391 ≤ (12015724179509/100000000000000 : ℝ)^3367
        have hw : |(-246187623/1250000000 : ℝ)|=(246187623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247370809/10000000000 : ℝ)|^4391 ≤ (8625774721833/20000000000000 : ℝ)^3367
        have hw : |(5247370809/10000000000 : ℝ)|=(5247370809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270385283/500000000 : ℝ)|^4391 ≤ (22427701101899/50000000000000 : ℝ)^3367
        have hw : |(270385283/500000000 : ℝ)|=(270385283/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s5_5 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652667691/5000000000 : ℝ)*x 0 + (-945398757/5000000000 : ℝ)*x 1 + (1081541117/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652667691/5000000000 : ℝ)^4391 ≤ (43751226003139/100000000000000 : ℝ)^3367 := by
    have hnat : (2652667691 : ℕ)^4391*100000000000000^3367 ≤ 43751226003139^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652667691 5000000000 43751226003139 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (945398757/5000000000 : ℝ)^4391 ≤ (11393372590371/100000000000000 : ℝ)^3367 := by
    have hnat : (945398757 : ℕ)^4391*100000000000000^3367 ≤ 11393372590371^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945398757 5000000000 11393372590371 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081541117/2000000000 : ℝ)^4391 ≤ (22427700696247/50000000000000 : ℝ)^3367 := by
    have hnat : (1081541117 : ℕ)^4391*50000000000000^3367 ≤ 22427700696247^3367*2000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081541117 2000000000 22427700696247 50000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652667691/5000000000 : ℝ), (-945398757/5000000000 : ℝ), (1081541117/2000000000 : ℝ)] ![(43751226003139/100000000000000 : ℝ), (11393372590371/100000000000000 : ℝ), (22427700696247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652667691/5000000000 : ℝ)|^4391 ≤ (43751226003139/100000000000000 : ℝ)^3367
        have hw : |(2652667691/5000000000 : ℝ)|=(2652667691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-945398757/5000000000 : ℝ)|^4391 ≤ (11393372590371/100000000000000 : ℝ)^3367
        have hw : |(-945398757/5000000000 : ℝ)|=(945398757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081541117/2000000000 : ℝ)|^4391 ≤ (22427700696247/50000000000000 : ℝ)^3367
        have hw : |(1081541117/2000000000 : ℝ)|=(1081541117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s5_6 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305335671/10000000000 : ℝ)*x 0 + (5407705373/10000000000 : ℝ)*x 1 + (-189079741/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305335671/10000000000 : ℝ)^4391 ≤ (43751229111243/100000000000000 : ℝ)^3367 := by
    have hnat : (5305335671 : ℕ)^4391*100000000000000^3367 ≤ 43751229111243^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305335671 10000000000 43751229111243 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407705373/10000000000 : ℝ)^4391 ≤ (4485539909921/10000000000000 : ℝ)^3367 := by
    have hnat : (5407705373 : ℕ)^4391*10000000000000^3367 ≤ 4485539909921^3367*10000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407705373 10000000000 4485539909921 10000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (189079741/1000000000 : ℝ)^4391 ≤ (1139337177311/10000000000000 : ℝ)^3367 := by
    have hnat : (189079741 : ℕ)^4391*10000000000000^3367 ≤ 1139337177311^3367*1000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189079741 1000000000 1139337177311 10000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305335671/10000000000 : ℝ), (5407705373/10000000000 : ℝ), (-189079741/1000000000 : ℝ)] ![(43751229111243/100000000000000 : ℝ), (4485539909921/10000000000000 : ℝ), (1139337177311/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305335671/10000000000 : ℝ)|^4391 ≤ (43751229111243/100000000000000 : ℝ)^3367
        have hw : |(5305335671/10000000000 : ℝ)|=(5305335671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407705373/10000000000 : ℝ)|^4391 ≤ (4485539909921/10000000000000 : ℝ)^3367
        have hw : |(5407705373/10000000000 : ℝ)|=(5407705373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-189079741/1000000000 : ℝ)|^4391 ≤ (1139337177311/10000000000000 : ℝ)^3367
        have hw : |(-189079741/1000000000 : ℝ)|=(189079741/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1431_s5_7 (p : ℝ) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075971543/2500000000 : ℝ)*x 0 + (2240305947/5000000000 : ℝ)*x 1 + (2066749711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075971543/2500000000 : ℝ)^4391 ≤ (33304849513337/100000000000000 : ℝ)^3367 := by
    have hnat : (1075971543 : ℕ)^4391*100000000000000^3367 ≤ 33304849513337^3367*2500000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075971543 2500000000 33304849513337 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2240305947/5000000000 : ℝ)^4391 ≤ (35099355347703/100000000000000 : ℝ)^3367 := by
    have hnat : (2240305947 : ℕ)^4391*100000000000000^3367 ≤ 35099355347703^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240305947 5000000000 35099355347703 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066749711/5000000000 : ℝ)^4391 ≤ (31595795128013/100000000000000 : ℝ)^3367 := by
    have hnat : (2066749711 : ℕ)^4391*100000000000000^3367 ≤ 31595795128013^3367*5000000000^4391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066749711 5000000000 31595795128013 100000000000000 4391 3367 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4391/1024 : ℝ)) 4391 3367 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075971543/2500000000 : ℝ), (2240305947/5000000000 : ℝ), (2066749711/5000000000 : ℝ)] ![(33304849513337/100000000000000 : ℝ), (35099355347703/100000000000000 : ℝ), (31595795128013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075971543/2500000000 : ℝ)|^4391 ≤ (33304849513337/100000000000000 : ℝ)^3367
        have hw : |(1075971543/2500000000 : ℝ)|=(1075971543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2240305947/5000000000 : ℝ)|^4391 ≤ (35099355347703/100000000000000 : ℝ)^3367
        have hw : |(2240305947/5000000000 : ℝ)|=(2240305947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2066749711/5000000000 : ℝ)|^4391 ≤ (31595795128013/100000000000000 : ℝ)^3367
        have hw : |(2066749711/5000000000 : ℝ)|=(2066749711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1431_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7393/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11341/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7381/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7393/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11317/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7393/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11317/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7393/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11317/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7393/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11317/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7393/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11317/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7393/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11317/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11317/100000 : ℝ) ^ (2195/512 : ℝ) ≤ (877490964156791/10000000000000000000 : ℝ) := by
    have hpowers : (11317/100000 : ℝ)^2195 ≤ (877490964156791/10000000000000000000 : ℝ)^512 := by
      have hnat : (11317 : ℕ)^2195*10000000000000000000^512 ≤ 877490964156791^512*100000^2195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11317 100000 877490964156791 10000000000000000000 2195 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11317/100000 : ℝ)) (X := (877490964156791/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7393/50000 : ℝ) ^ (2195/512 : ℝ) ≤ (27609539385979473/100000000000000000000 : ℝ) := by
    have hpowers : (7393/50000 : ℝ)^2195 ≤ (27609539385979473/100000000000000000000 : ℝ)^512 := by
      have hnat : (7393 : ℕ)^2195*100000000000000000000^512 ≤ 27609539385979473^512*50000^2195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7393 50000 27609539385979473 100000000000000000000 2195 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7393/50000 : ℝ)) (X := (27609539385979473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000877490964156791/5000000000000000000 : ℝ) ≤ (10000409334987781/10000000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (5000877490964156791/5000000000000000000 : ℝ)^512 ≤ (10000409334987781/10000000000000000 : ℝ)^2195 := by
      have hnat : (5000877490964156791 : ℕ)^512*10000000000000000^2195 ≤ 10000409334987781^2195*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000877490964156791 5000000000000000000 10000409334987781 10000000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000409334987781/10000000000000000 : ℝ)) (X := (5000877490964156791/5000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036384449027547383/100000000000000000000 : ℝ) ≤ (250021214396319/250000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (100036384449027547383/100000000000000000000 : ℝ)^512 ≤ (250021214396319/250000000000000 : ℝ)^2195 := by
      have hnat : (100036384449027547383 : ℕ)^512*250000000000000^2195 ≤ 250021214396319^2195*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036384449027547383 100000000000000000000 250021214396319 250000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250021214396319/250000000000000 : ℝ)) (X := (100036384449027547383/100000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027609539385979473/50000000000000000000 : ℝ) ≤ (10001287816717739/10000000000000000 : ℝ) ^ (2195/512 : ℝ) := by
    have hpowers : (50027609539385979473/50000000000000000000 : ℝ)^512 ≤ (10001287816717739/10000000000000000 : ℝ)^2195 := by
      have hnat : (50027609539385979473 : ℕ)^512*10000000000000000^2195 ≤ 10001287816717739^2195*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027609539385979473 50000000000000000000 10001287816717739 10000000000000000 512 2195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001287816717739/10000000000000000 : ℝ)) (X := (50027609539385979473/50000000000000000000 : ℝ)) (by norm_num) 2195 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(877490964156791/10000000000000000000 : ℝ) ≤ ((34681478205334677603/34690000000000000000 : ℝ)+2*(439240864979/346900000000000 : ℝ)*(11317/100000 : ℝ))^(2195/512 : ℝ) := by
    rw [show (34681478205334677603/34690000000000000000 : ℝ)+2*(439240864979/346900000000000 : ℝ)*(11317/100000 : ℝ)=(10000409334987781/10000000000000000 : ℝ) by norm_num, show 1+2*(877490964156791/10000000000000000000 : ℝ)=(5000877490964156791/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27609539385979473/100000000000000000000 : ℝ)+(877490964156791/10000000000000000000 : ℝ) ≤ ((34681478205334677603/34690000000000000000 : ℝ)+(439240864979/346900000000000 : ℝ)*((7393/50000 : ℝ)+(11317/100000 : ℝ)))^(2195/512 : ℝ) := by
    rw [show (34681478205334677603/34690000000000000000 : ℝ)+(439240864979/346900000000000 : ℝ)*((7393/50000 : ℝ)+(11317/100000 : ℝ))=(250021214396319/250000000000000 : ℝ) by norm_num, show 1+(27609539385979473/100000000000000000000 : ℝ)+(877490964156791/10000000000000000000 : ℝ)=(100036384449027547383/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27609539385979473/100000000000000000000 : ℝ) ≤ ((34681478205334677603/34690000000000000000 : ℝ)+2*(439240864979/346900000000000 : ℝ)*(7393/50000 : ℝ))^(2195/512 : ℝ) := by
    rw [show (34681478205334677603/34690000000000000000 : ℝ)+2*(439240864979/346900000000000 : ℝ)*(7393/50000 : ℝ)=(10001287816717739/10000000000000000 : ℝ) by norm_num, show 1+2*(27609539385979473/100000000000000000000 : ℝ)=(50027609539385979473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34681478205334677603/34690000000000000000 : ℝ)*(X 1 0+X 2 0)+(439240864979/346900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (11317/100000 : ℝ)) (hi := (7393/50000 : ℝ)) (c := (34681478205334677603/34690000000000000000 : ℝ)) (alpha := (439240864979/346900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34681478205334677603/34690000000000000000 : ℝ)*(X 0 1+X 2 1)+(439240864979/346900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (11317/100000 : ℝ)) (hi := (7393/50000 : ℝ)) (c := (34681478205334677603/34690000000000000000 : ℝ)) (alpha := (439240864979/346900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34681478205334677603/34690000000000000000 : ℝ)*(X 0 2+X 1 2)+(439240864979/346900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2195/512 : ℝ)) (lo := (11317/100000 : ℝ)) (hi := (7393/50000 : ℝ)) (c := (34681478205334677603/34690000000000000000 : ℝ)) (alpha := (439240864979/346900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-984744917/5000000000 : ℝ)*X 0 0+(2704146321/5000000000 : ℝ)*X 0 1+(1049357337/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336832587/2500000000 : ℝ)*X 1 0+(-2051716691/10000000000 : ℝ)*X 1 1+(2623393429/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347330579/10000000000 : ℝ)*X 2 0+(5246786677/10000000000 : ℝ)*X 2 1+(-2051716623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4303861673/10000000000 : ℝ)*X 0 0+(165289151/400000000 : ℝ)*X 0 1+(4481875847/10000000000 : ℝ)*X 0 2+(4303861673/10000000000 : ℝ)*X 1 0+(165289151/400000000 : ℝ)*X 1 1+(4481875847/10000000000 : ℝ)*X 1 2+(4303861673/10000000000 : ℝ)*X 2 0+(165289151/400000000 : ℝ)*X 2 1+(4481875847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-246187623/1250000000 : ℝ)*X 0 0+(5247370809/10000000000 : ℝ)*X 0 1+(270385283/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652667691/5000000000 : ℝ)*X 1 0+(-945398757/5000000000 : ℝ)*X 1 1+(1081541117/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305335671/10000000000 : ℝ)*X 2 0+(5407705373/10000000000 : ℝ)*X 2 1+(-189079741/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1075971543/2500000000 : ℝ)*X 0 0+(2240305947/5000000000 : ℝ)*X 0 1+(2066749711/5000000000 : ℝ)*X 0 2+(1075971543/2500000000 : ℝ)*X 1 0+(2240305947/5000000000 : ℝ)*X 1 1+(2066749711/5000000000 : ℝ)*X 1 2+(1075971543/2500000000 : ℝ)*X 2 0+(2240305947/5000000000 : ℝ)*X 2 1+(2066749711/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1431_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1903522391641744528130499753/867250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (561189317/100000000000000 : ℝ)*(base19) + (40809859/6250000000000 : ℝ)*(base23) + (46978953/50000000000000 : ℝ)*(lower2) + (18869807/25000000000000 : ℝ)*(upper3) + (39566877/50000000000000 : ℝ)*(upper5) + (4525896722288017/100000000000000 : ℝ)*(major0) + (4525896722288017/100000000000000 : ℝ)*(major1) + (4525896722288017/100000000000000 : ℝ)*(major2) + (6191736023363947/100000000000000 : ℝ)*(sp0) + (773969250579357/12500000000000 : ℝ)*(sp1) + (6191753912866429/100000000000000 : ℝ)*(sp2) + (1430015981989193/50000000000000 : ℝ)*(sp3) + (9271230113/50000000000000 : ℝ)*(sp4) + (1710402579/25000000000000 : ℝ)*(sp7) + (1430019402794351/50000000000000 : ℝ)*(f.failure) + (6191754565824173/100000000000000 : ℝ)*(f.sum) + (8563267626417/17345000000000000000000000000 : ℝ)*base66 + (18076145214191483251/3469000000000000000000000000000000 : ℝ)*base67 + (7644854801011516749/3469000000000000000000000000000000 : ℝ)*base70 + (16977002041572516749/3469000000000000000000000000000000 : ℝ)*base72 + (55438026886133/17345000000000000000000000000 : ℝ)*base73 + (18245416651128516749/3469000000000000000000000000000000 : ℝ)*base76 + (14156089304479516749/3469000000000000000000000000000000 : ℝ)*base78 + (6046051458933516749/3469000000000000000000000000000000 : ℝ)*base80 + (921279187083/1084062500000000000000000000 : ℝ)*base81 + (959751/500000000000000000000 : ℝ)*base90 + (959751/500000000000000000000 : ℝ)*base92 + (959751/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5238172703898758192469/693800000000000000000000000 : ℝ) := by norm_num
    linear_combination (111852087/6250000000000 : ℝ)*(base19) + (2708719101/100000000000000 : ℝ)*(base23) + (33003109/25000000000000 : ℝ)*(upper3) + (58363241/25000000000000 : ℝ)*(lower4) + (28266233/50000000000000 : ℝ)*(upper5) + (182357076402693/4000000000000 : ℝ)*(major0) + (182357076402693/4000000000000 : ℝ)*(major1) + (182357076402693/4000000000000 : ℝ)*(major2) + (19980982113/50000000000000 : ℝ)*(sp1) + (28780324337/50000000000000 : ℝ)*(sp2) + (1559235519349727/25000000000000 : ℝ)*(sp4) + (623690032580129/10000000000000 : ℝ)*(sp5) + (1559220452007783/25000000000000 : ℝ)*(sp6) + (28809114910699/1000000000000 : ℝ)*(sp7) + (28809114910699/1000000000000 : ℝ)*(f.failure) + (1559235519349727/25000000000000 : ℝ)*(f.sum) + (5516419888597/3469000000000000000000000000 : ℝ)*base66 + (282968399786035121/138760000000000000000000000000000 : ℝ)*base68 + (1458092137020115121/138760000000000000000000000000000 : ℝ)*base70 + (68048740403404879/138760000000000000000000000000000 : ℝ)*base71 + (9947734524171/3469000000000000000000000000 : ℝ)*base74 + (1944685614115395121/138760000000000000000000000000000 : ℝ)*base76 + (385012881407004879/138760000000000000000000000000000 : ℝ)*base77 + (993497056366844879/138760000000000000000000000000000 : ℝ)*base79 + (14150845705647/3469000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (15299/10000000000000000000 : ℝ)*base90 + (15299/10000000000000000000 : ℝ)*base92 + (15299/10000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1431_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7393/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1431_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1431_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15793/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5189/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1431_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1431_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1431_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2195/512 : ℝ) ≤ p) (hpb : p ≤ (4391/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15824599/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15793/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5189/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1431_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
