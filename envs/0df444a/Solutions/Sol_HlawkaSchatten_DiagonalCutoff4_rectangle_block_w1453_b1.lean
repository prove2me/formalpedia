-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1453_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:59:46.455338+00:00
-- url     : https://prove2.me/submissions/b879a839-f78e-4657-a5b8-1ae4b9354196

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
theorem support_rectangle_w1453_s3_0 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1950903703/10000000000 : ℝ)*x 0 + (5414930519/10000000000 : ℝ)*x 1 + (2620037601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1950903703/10000000000 : ℝ)^4413 ≤ (11906324951091/100000000000000 : ℝ)^3389 := by
    have hnat : (1950903703 : ℕ)^4413*100000000000000^3389 ≤ 11906324951091^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950903703 10000000000 11906324951091 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414930519/10000000000 : ℝ)^4413 ≤ (44988022804627/100000000000000 : ℝ)^3389 := by
    have hnat : (5414930519 : ℕ)^4413*100000000000000^3389 ≤ 44988022804627^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414930519 10000000000 44988022804627 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620037601/5000000000 : ℝ)^4413 ≤ (8621130448121/20000000000000 : ℝ)^3389 := by
    have hnat : (2620037601 : ℕ)^4413*20000000000000^3389 ≤ 8621130448121^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620037601 5000000000 8621130448121 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1950903703/10000000000 : ℝ), (5414930519/10000000000 : ℝ), (2620037601/5000000000 : ℝ)] ![(11906324951091/100000000000000 : ℝ), (44988022804627/100000000000000 : ℝ), (8621130448121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1950903703/10000000000 : ℝ)|^4413 ≤ (11906324951091/100000000000000 : ℝ)^3389
        have hw : |(-1950903703/10000000000 : ℝ)|=(1950903703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414930519/10000000000 : ℝ)|^4413 ≤ (44988022804627/100000000000000 : ℝ)^3389
        have hw : |(5414930519/10000000000 : ℝ)|=(5414930519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620037601/5000000000 : ℝ)|^4413 ≤ (8621130448121/20000000000000 : ℝ)^3389
        have hw : |(2620037601/5000000000 : ℝ)|=(2620037601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s3_1 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674434941/5000000000 : ℝ)*x 0 + (-408011683/2000000000 : ℝ)*x 1 + (5240075209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674434941/5000000000 : ℝ)^4413 ≤ (8854933576961/20000000000000 : ℝ)^3389 := by
    have hnat : (2674434941 : ℕ)^4413*20000000000000^3389 ≤ 8854933576961^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674434941 5000000000 8854933576961 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (408011683/2000000000 : ℝ)^4413 ≤ (12619679785339/100000000000000 : ℝ)^3389 := by
    have hnat : (408011683 : ℕ)^4413*100000000000000^3389 ≤ 12619679785339^3389*2000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408011683 2000000000 12619679785339 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240075209/10000000000 : ℝ)^4413 ≤ (43105652315587/100000000000000 : ℝ)^3389 := by
    have hnat : (5240075209 : ℕ)^4413*100000000000000^3389 ≤ 43105652315587^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240075209 10000000000 43105652315587 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674434941/5000000000 : ℝ), (-408011683/2000000000 : ℝ), (5240075209/10000000000 : ℝ)] ![(8854933576961/20000000000000 : ℝ), (12619679785339/100000000000000 : ℝ), (43105652315587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674434941/5000000000 : ℝ)|^4413 ≤ (8854933576961/20000000000000 : ℝ)^3389
        have hw : |(2674434941/5000000000 : ℝ)|=(2674434941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-408011683/2000000000 : ℝ)|^4413 ≤ (12619679785339/100000000000000 : ℝ)^3389
        have hw : |(-408011683/2000000000 : ℝ)|=(408011683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240075209/10000000000 : ℝ)|^4413 ≤ (43105652315587/100000000000000 : ℝ)^3389
        have hw : |(5240075209/10000000000 : ℝ)|=(5240075209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s3_2 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668608737/1250000000 : ℝ)*x 0 + (5240075227/10000000000 : ℝ)*x 1 + (-2040058371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668608737/1250000000 : ℝ)^4413 ≤ (44274668035703/100000000000000 : ℝ)^3389 := by
    have hnat : (668608737 : ℕ)^4413*100000000000000^3389 ≤ 44274668035703^3389*1250000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668608737 1250000000 44274668035703 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240075227/10000000000 : ℝ)^4413 ≤ (21552826254199/50000000000000 : ℝ)^3389 := by
    have hnat : (5240075227 : ℕ)^4413*50000000000000^3389 ≤ 21552826254199^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240075227 10000000000 21552826254199 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2040058371/10000000000 : ℝ)^4413 ≤ (12619679430917/100000000000000 : ℝ)^3389 := by
    have hnat : (2040058371 : ℕ)^4413*100000000000000^3389 ≤ 12619679430917^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040058371 10000000000 12619679430917 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668608737/1250000000 : ℝ), (5240075227/10000000000 : ℝ), (-2040058371/10000000000 : ℝ)] ![(44274668035703/100000000000000 : ℝ), (21552826254199/50000000000000 : ℝ), (12619679430917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668608737/1250000000 : ℝ)|^4413 ≤ (44274668035703/100000000000000 : ℝ)^3389
        have hw : |(668608737/1250000000 : ℝ)|=(668608737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240075227/10000000000 : ℝ)|^4413 ≤ (21552826254199/50000000000000 : ℝ)^3389
        have hw : |(5240075227/10000000000 : ℝ)|=(5240075227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2040058371/10000000000 : ℝ)|^4413 ≤ (12619679430917/100000000000000 : ℝ)^3389
        have hw : |(-2040058371/10000000000 : ℝ)|=(2040058371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s3_3 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (171913833/400000000 : ℝ)*x 0 + (4110815223/10000000000 : ℝ)*x 1 + (898482901/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171913833/400000000 : ℝ)^4413 ≤ (16649687947079/50000000000000 : ℝ)^3389 := by
    have hnat : (171913833 : ℕ)^4413*50000000000000^3389 ≤ 16649687947079^3389*400000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171913833 400000000 16649687947079 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4110815223/10000000000 : ℝ)^4413 ≤ (31424959964443/100000000000000 : ℝ)^3389 := by
    have hnat : (4110815223 : ℕ)^4413*100000000000000^3389 ≤ 31424959964443^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4110815223 10000000000 31424959964443 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898482901/2000000000 : ℝ)^4413 ≤ (1763783206701/5000000000000 : ℝ)^3389 := by
    have hnat : (898482901 : ℕ)^4413*5000000000000^3389 ≤ 1763783206701^3389*2000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898482901 2000000000 1763783206701 5000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171913833/400000000 : ℝ), (4110815223/10000000000 : ℝ), (898482901/2000000000 : ℝ)] ![(16649687947079/50000000000000 : ℝ), (31424959964443/100000000000000 : ℝ), (1763783206701/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171913833/400000000 : ℝ)|^4413 ≤ (16649687947079/50000000000000 : ℝ)^3389
        have hw : |(171913833/400000000 : ℝ)|=(171913833/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4110815223/10000000000 : ℝ)|^4413 ≤ (31424959964443/100000000000000 : ℝ)^3389
        have hw : |(4110815223/10000000000 : ℝ)|=(4110815223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898482901/2000000000 : ℝ)|^4413 ≤ (1763783206701/5000000000000 : ℝ)^3389
        have hw : |(898482901/2000000000 : ℝ)|=(898482901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s3_4 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-60966183/312500000 : ℝ)*x 0 + (5240767553/10000000000 : ℝ)*x 1 + (338389661/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (60966183/312500000 : ℝ)^4413 ≤ (372076169543/3125000000000 : ℝ)^3389 := by
    have hnat : (60966183 : ℕ)^4413*3125000000000^3389 ≤ 372076169543^3389*312500000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60966183 312500000 372076169543 3125000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240767553/10000000000 : ℝ)^4413 ≤ (8622613731219/20000000000000 : ℝ)^3389 := by
    have hnat : (5240767553 : ℕ)^4413*20000000000000^3389 ≤ 8622613731219^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240767553 10000000000 8622613731219 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338389661/625000000 : ℝ)^4413 ≤ (44980493903137/100000000000000 : ℝ)^3389 := by
    have hnat : (338389661 : ℕ)^4413*100000000000000^3389 ≤ 44980493903137^3389*625000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338389661 625000000 44980493903137 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-60966183/312500000 : ℝ), (5240767553/10000000000 : ℝ), (338389661/625000000 : ℝ)] ![(372076169543/3125000000000 : ℝ), (8622613731219/20000000000000 : ℝ), (44980493903137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-60966183/312500000 : ℝ)|^4413 ≤ (372076169543/3125000000000 : ℝ)^3389
        have hw : |(-60966183/312500000 : ℝ)|=(60966183/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240767553/10000000000 : ℝ)|^4413 ≤ (8622613731219/20000000000000 : ℝ)^3389
        have hw : |(5240767553/10000000000 : ℝ)|=(5240767553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338389661/625000000 : ℝ)|^4413 ≤ (44980493903137/100000000000000 : ℝ)^3389
        have hw : |(338389661/625000000 : ℝ)|=(338389661/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s3_5 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060661693/2000000000 : ℝ)*x 0 + (-233237411/1250000000 : ℝ)*x 1 + (5414234547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060661693/2000000000 : ℝ)^4413 ≤ (43784220403941/100000000000000 : ℝ)^3389 := by
    have hnat : (1060661693 : ℕ)^4413*100000000000000^3389 ≤ 43784220403941^3389*2000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060661693 2000000000 43784220403941 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (233237411/1250000000 : ℝ)^4413 ≤ (11235285988189/100000000000000 : ℝ)^3389 := by
    have hnat : (233237411 : ℕ)^4413*100000000000000^3389 ≤ 11235285988189^3389*1250000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233237411 1250000000 11235285988189 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414234547/10000000000 : ℝ)^4413 ≤ (44980493589413/100000000000000 : ℝ)^3389 := by
    have hnat : (5414234547 : ℕ)^4413*100000000000000^3389 ≤ 44980493589413^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414234547 10000000000 44980493589413 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060661693/2000000000 : ℝ), (-233237411/1250000000 : ℝ), (5414234547/10000000000 : ℝ)] ![(43784220403941/100000000000000 : ℝ), (11235285988189/100000000000000 : ℝ), (44980493589413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060661693/2000000000 : ℝ)|^4413 ≤ (43784220403941/100000000000000 : ℝ)^3389
        have hw : |(1060661693/2000000000 : ℝ)|=(1060661693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-233237411/1250000000 : ℝ)|^4413 ≤ (11235285988189/100000000000000 : ℝ)^3389
        have hw : |(-233237411/1250000000 : ℝ)|=(233237411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414234547/10000000000 : ℝ)|^4413 ≤ (44980493589413/100000000000000 : ℝ)^3389
        have hw : |(5414234547/10000000000 : ℝ)|=(5414234547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s3_6 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325826839/2500000000 : ℝ)*x 0 + (2707117709/5000000000 : ℝ)*x 1 + (-1865899607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325826839/2500000000 : ℝ)^4413 ≤ (10946052120379/25000000000000 : ℝ)^3389 := by
    have hnat : (1325826839 : ℕ)^4413*25000000000000^3389 ≤ 10946052120379^3389*2500000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325826839 2500000000 10946052120379 25000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707117709/5000000000 : ℝ)^4413 ≤ (22490251505973/50000000000000 : ℝ)^3389 := by
    have hnat : (2707117709 : ℕ)^4413*50000000000000^3389 ≤ 22490251505973^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707117709 5000000000 22490251505973 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1865899607/10000000000 : ℝ)^4413 ≤ (702205530587/6250000000000 : ℝ)^3389 := by
    have hnat : (1865899607 : ℕ)^4413*6250000000000^3389 ≤ 702205530587^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865899607 10000000000 702205530587 6250000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325826839/2500000000 : ℝ), (2707117709/5000000000 : ℝ), (-1865899607/10000000000 : ℝ)] ![(10946052120379/25000000000000 : ℝ), (22490251505973/50000000000000 : ℝ), (702205530587/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325826839/2500000000 : ℝ)|^4413 ≤ (10946052120379/25000000000000 : ℝ)^3389
        have hw : |(1325826839/2500000000 : ℝ)|=(1325826839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707117709/5000000000 : ℝ)|^4413 ≤ (22490251505973/50000000000000 : ℝ)^3389
        have hw : |(2707117709/5000000000 : ℝ)|=(2707117709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1865899607/10000000000 : ℝ)|^4413 ≤ (702205530587/6250000000000 : ℝ)^3389
        have hw : |(-1865899607/10000000000 : ℝ)|=(1865899607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s3_7 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2148938411/5000000000 : ℝ)*x 0 + (449090437/1000000000 : ℝ)*x 1 + (411233483/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148938411/5000000000 : ℝ)^4413 ≤ (3329968862287/10000000000000 : ℝ)^3389 := by
    have hnat : (2148938411 : ℕ)^4413*10000000000000^3389 ≤ 3329968862287^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148938411 5000000000 3329968862287 10000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449090437/1000000000 : ℝ)^4413 ≤ (17630111993131/50000000000000 : ℝ)^3389 := by
    have hnat : (449090437 : ℕ)^4413*50000000000000^3389 ≤ 17630111993131^3389*1000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449090437 1000000000 17630111993131 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411233483/1000000000 : ℝ)^4413 ≤ (15720043688869/50000000000000 : ℝ)^3389 := by
    have hnat : (411233483 : ℕ)^4413*50000000000000^3389 ≤ 15720043688869^3389*1000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411233483 1000000000 15720043688869 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148938411/5000000000 : ℝ), (449090437/1000000000 : ℝ), (411233483/1000000000 : ℝ)] ![(3329968862287/10000000000000 : ℝ), (17630111993131/50000000000000 : ℝ), (15720043688869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148938411/5000000000 : ℝ)|^4413 ≤ (3329968862287/10000000000000 : ℝ)^3389
        have hw : |(2148938411/5000000000 : ℝ)|=(2148938411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(449090437/1000000000 : ℝ)|^4413 ≤ (17630111993131/50000000000000 : ℝ)^3389
        have hw : |(449090437/1000000000 : ℝ)|=(449090437/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(411233483/1000000000 : ℝ)|^4413 ≤ (15720043688869/50000000000000 : ℝ)^3389
        have hw : |(411233483/1000000000 : ℝ)|=(411233483/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1453_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79559293/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15729/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2623/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11231/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2987/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15729/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2623/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15729/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2623/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15729/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2623/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15729/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2623/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15729/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2623/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15729/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2623/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (2623/25000 : ℝ) ^ (1103/256 : ℝ) ≤ (1510831815639237/25000000000000000000 : ℝ) := by
    have hpowers : (2623/25000 : ℝ)^1103 ≤ (1510831815639237/25000000000000000000 : ℝ)^256 := by
      have hnat : (2623 : ℕ)^1103*25000000000000000000^256 ≤ 1510831815639237^256*25000^1103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2623 25000 1510831815639237 25000000000000000000 1103 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2623/25000 : ℝ)) (X := (1510831815639237/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hpowhi : (15729/100000 : ℝ) ^ (1103/256 : ℝ) ≤ (1080840115818461/3125000000000000000 : ℝ) := by
    have hpowers : (15729/100000 : ℝ)^1103 ≤ (1080840115818461/3125000000000000000 : ℝ)^256 := by
      have hnat : (15729 : ℕ)^1103*3125000000000000000^256 ≤ 1080840115818461^256*100000^1103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15729 100000 1080840115818461 3125000000000000000 1103 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15729/100000 : ℝ)) (X := (1080840115818461/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501510831815639237/12500000000000000000 : ℝ) ≤ (5000140255665309/5000000000000000 : ℝ) ^ (1103/256 : ℝ) := by
    have hpowers : (12501510831815639237/12500000000000000000 : ℝ)^256 ≤ (5000140255665309/5000000000000000 : ℝ)^1103 := by
      have hnat : (12501510831815639237 : ℕ)^256*5000000000000000^1103 ≤ 5000140255665309^1103*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501510831815639237 12500000000000000000 5000140255665309 5000000000000000 256 1103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000140255665309/5000000000000000 : ℝ)) (X := (12501510831815639237/12500000000000000000 : ℝ)) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (1000406302109687477/1000000000000000000 : ℝ) ≤ (1000094285691563/1000000000000000 : ℝ) ^ (1103/256 : ℝ) := by
    have hpowers : (1000406302109687477/1000000000000000000 : ℝ)^256 ≤ (1000094285691563/1000000000000000 : ℝ)^1103 := by
      have hnat : (1000406302109687477 : ℕ)^256*1000000000000000^1103 ≤ 1000094285691563^1103*1000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000406302109687477 1000000000000000000 1000094285691563 1000000000000000 256 1103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000094285691563/1000000000000000 : ℝ)) (X := (1000406302109687477/1000000000000000000 : ℝ)) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563580840115818461/1562500000000000000 : ℝ) ≤ (5000802601250321/5000000000000000 : ℝ) ^ (1103/256 : ℝ) := by
    have hpowers : (1563580840115818461/1562500000000000000 : ℝ)^256 ≤ (5000802601250321/5000000000000000 : ℝ)^1103 := by
      have hnat : (1563580840115818461 : ℕ)^256*5000000000000000^1103 ≤ 5000802601250321^1103*1562500000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563580840115818461 1562500000000000000 5000802601250321 5000000000000000 256 1103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000802601250321/5000000000000000 : ℝ)) (X := (1563580840115818461/1562500000000000000 : ℝ)) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1510831815639237/25000000000000000000 : ℝ) ≤ ((26178785189041277329/26185000000000000000 : ℝ)+2*(165586396253/130925000000000 : ℝ)*(2623/25000 : ℝ))^(1103/256 : ℝ) := by
    rw [show (26178785189041277329/26185000000000000000 : ℝ)+2*(165586396253/130925000000000 : ℝ)*(2623/25000 : ℝ)=(5000140255665309/5000000000000000 : ℝ) by norm_num, show 1+2*(1510831815639237/25000000000000000000 : ℝ)=(12501510831815639237/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1080840115818461/3125000000000000000 : ℝ)+(1510831815639237/25000000000000000000 : ℝ) ≤ ((26178785189041277329/26185000000000000000 : ℝ)+(165586396253/130925000000000 : ℝ)*((15729/100000 : ℝ)+(2623/25000 : ℝ)))^(1103/256 : ℝ) := by
    rw [show (26178785189041277329/26185000000000000000 : ℝ)+(165586396253/130925000000000 : ℝ)*((15729/100000 : ℝ)+(2623/25000 : ℝ))=(1000094285691563/1000000000000000 : ℝ) by norm_num, show 1+(1080840115818461/3125000000000000000 : ℝ)+(1510831815639237/25000000000000000000 : ℝ)=(1000406302109687477/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1080840115818461/3125000000000000000 : ℝ) ≤ ((26178785189041277329/26185000000000000000 : ℝ)+2*(165586396253/130925000000000 : ℝ)*(15729/100000 : ℝ))^(1103/256 : ℝ) := by
    rw [show (26178785189041277329/26185000000000000000 : ℝ)+2*(165586396253/130925000000000 : ℝ)*(15729/100000 : ℝ)=(5000802601250321/5000000000000000 : ℝ) by norm_num, show 1+2*(1080840115818461/3125000000000000000 : ℝ)=(1563580840115818461/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26178785189041277329/26185000000000000000 : ℝ)*(X 1 0+X 2 0)+(165586396253/130925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1103/256 : ℝ)) (lo := (2623/25000 : ℝ)) (hi := (15729/100000 : ℝ)) (c := (26178785189041277329/26185000000000000000 : ℝ)) (alpha := (165586396253/130925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26178785189041277329/26185000000000000000 : ℝ)*(X 0 1+X 2 1)+(165586396253/130925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1103/256 : ℝ)) (lo := (2623/25000 : ℝ)) (hi := (15729/100000 : ℝ)) (c := (26178785189041277329/26185000000000000000 : ℝ)) (alpha := (165586396253/130925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26178785189041277329/26185000000000000000 : ℝ)*(X 0 2+X 1 2)+(165586396253/130925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1103/256 : ℝ)) (lo := (2623/25000 : ℝ)) (hi := (15729/100000 : ℝ)) (c := (26178785189041277329/26185000000000000000 : ℝ)) (alpha := (165586396253/130925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1950903703/10000000000 : ℝ)*X 0 0+(5414930519/10000000000 : ℝ)*X 0 1+(2620037601/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674434941/5000000000 : ℝ)*X 1 0+(-408011683/2000000000 : ℝ)*X 1 1+(5240075209/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668608737/1250000000 : ℝ)*X 2 0+(5240075227/10000000000 : ℝ)*X 2 1+(-2040058371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((171913833/400000000 : ℝ)*X 0 0+(4110815223/10000000000 : ℝ)*X 0 1+(898482901/2000000000 : ℝ)*X 0 2+(171913833/400000000 : ℝ)*X 1 0+(4110815223/10000000000 : ℝ)*X 1 1+(898482901/2000000000 : ℝ)*X 1 2+(171913833/400000000 : ℝ)*X 2 0+(4110815223/10000000000 : ℝ)*X 2 1+(898482901/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-60966183/312500000 : ℝ)*X 0 0+(5240767553/10000000000 : ℝ)*X 0 1+(338389661/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060661693/2000000000 : ℝ)*X 1 0+(-233237411/1250000000 : ℝ)*X 1 1+(5414234547/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325826839/2500000000 : ℝ)*X 2 0+(2707117709/5000000000 : ℝ)*X 2 1+(-1865899607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2148938411/5000000000 : ℝ)*X 0 0+(449090437/1000000000 : ℝ)*X 0 1+(411233483/1000000000 : ℝ)*X 0 2+(2148938411/5000000000 : ℝ)*X 1 0+(449090437/1000000000 : ℝ)*X 1 1+(411233483/1000000000 : ℝ)*X 1 2+(2148938411/5000000000 : ℝ)*X 2 0+(449090437/1000000000 : ℝ)*X 2 1+(411233483/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15238521368203024266425989437/1309250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1016733857/50000000000000 : ℝ)*(base19) + (1930807407/100000000000000 : ℝ)*(base23) + (31459197/50000000000000 : ℝ)*(lower2) + (128615551/50000000000000 : ℝ)*(upper3) + (112151369/50000000000000 : ℝ)*(upper5) + (4169841577126351/100000000000000 : ℝ)*(major0) + (4169841577126351/100000000000000 : ℝ)*(major1) + (4169841577126351/100000000000000 : ℝ)*(major2) + (5719054354157331/100000000000000 : ℝ)*(sp0) + (5719093357102909/100000000000000 : ℝ)*(sp1) + (357443341235201/6250000000000 : ℝ)*(sp2) + (52411362534469/2000000000000 : ℝ)*(sp3) + (10259103323/25000000000000 : ℝ)*(sp4) + (2406123483/12500000000000 : ℝ)*(sp7) + (524117475142263/20000000000000 : ℝ)*(f.failure) + (5719095390570623/100000000000000 : ℝ)*(f.sum) + (191646744737807/26185000000000000000000000000 : ℝ)*base65 + (30808810531632103521/2618500000000000000000000000000000 : ℝ)*base68 + (18041766852918603521/2618500000000000000000000000000000 : ℝ)*base70 + (15035036971900603521/2618500000000000000000000000000000 : ℝ)*base72 + (24465129740863/26185000000000000000000000000 : ℝ)*base74 + (31288958717731896479/2618500000000000000000000000000000 : ℝ)*base75 + (4274151765536396479/2618500000000000000000000000000000 : ℝ)*base77 + (33627496865021603521/2618500000000000000000000000000000 : ℝ)*base80 + (31089017558039/13092500000000000000000000000 : ℝ)*base82 + (8700059/1000000000000000000000 : ℝ)*base89 + (8700059/1000000000000000000000 : ℝ)*base91 + (8700059/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5130444106837083934513932423/1309250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7856533/3125000000000 : ℝ)*(base8) + (1040206919/100000000000000 : ℝ)*(base21) + (49131/781250000000 : ℝ)*(base29) + (40180931/25000000000000 : ℝ)*(upper2) + (4203155451467631/100000000000000 : ℝ)*(major0) + (4203155457756399/100000000000000 : ℝ)*(major1) + (4203155457756399/100000000000000 : ℝ)*(major2) + (106100473/25000000000000 : ℝ)*(sp0) + (7085195831/100000000000000 : ℝ)*(sp1) + (4898559409/100000000000000 : ℝ)*(sp2) + (144119655553453/2500000000000 : ℝ)*(sp4) + (1441194951616117/25000000000000 : ℝ)*(sp5) + (5764780952893971/100000000000000 : ℝ)*(sp6) + (330190485867911/12500000000000 : ℝ)*(sp7) + (330190485867911/12500000000000 : ℝ)*(f.failure) + (5764786897949067/100000000000000 : ℝ)*(f.sum) + (24910042021611/3273125000000000000000000000 : ℝ)*base65 + (5959520935785221729/2618500000000000000000000000000000 : ℝ)*base68 + (11053837498691221729/2618500000000000000000000000000000 : ℝ)*base70 + (16302350072785962401/2618500000000000000000000000000000 : ℝ)*base72 + (4830191015929/5237000000000000000000000000 : ℝ)*base73 + (17124198742415521729/2618500000000000000000000000000000 : ℝ)*base76 + (40094089719278962401/2618500000000000000000000000000000 : ℝ)*base78 + (17211508869986521729/2618500000000000000000000000000000 : ℝ)*base80 + (2679292708397/1309250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (3203077/625000000000000000000 : ℝ)*base90 + (3203077/625000000000000000000 : ℝ)*base92 + (3203077/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1453_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79559293/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15729/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2623/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2987/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1453_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1453_s4_0 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1951693917/10000000000 : ℝ)*x 0 + (5408138349/10000000000 : ℝ)*x 1 + (5246346341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1951693917/10000000000 : ℝ)^4413 ≤ (5956302590547/50000000000000 : ℝ)^3389 := by
    have hnat : (1951693917 : ℕ)^4413*50000000000000^3389 ≤ 5956302590547^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951693917 10000000000 5956302590547 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408138349/10000000000 : ℝ)^4413 ≤ (11228638939037/25000000000000 : ℝ)^3389 := by
    have hnat : (5408138349 : ℕ)^4413*25000000000000^3389 ≤ 11228638939037^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408138349 10000000000 11228638939037 25000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246346341/10000000000 : ℝ)^4413 ≤ (21586419522087/50000000000000 : ℝ)^3389 := by
    have hnat : (5246346341 : ℕ)^4413*50000000000000^3389 ≤ 21586419522087^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246346341 10000000000 21586419522087 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1951693917/10000000000 : ℝ), (5408138349/10000000000 : ℝ), (5246346341/10000000000 : ℝ)] ![(5956302590547/50000000000000 : ℝ), (11228638939037/25000000000000 : ℝ), (21586419522087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1951693917/10000000000 : ℝ)|^4413 ≤ (5956302590547/50000000000000 : ℝ)^3389
        have hw : |(-1951693917/10000000000 : ℝ)|=(1951693917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408138349/10000000000 : ℝ)|^4413 ≤ (11228638939037/25000000000000 : ℝ)^3389
        have hw : |(5408138349/10000000000 : ℝ)|=(5408138349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246346341/10000000000 : ℝ)|^4413 ≤ (21586419522087/50000000000000 : ℝ)^3389
        have hw : |(5246346341/10000000000 : ℝ)|=(5246346341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s4_1 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347110507/10000000000 : ℝ)*x 0 + (-1017034383/5000000000 : ℝ)*x 1 + (2623173223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347110507/10000000000 : ℝ)^4413 ≤ (44255705521179/100000000000000 : ℝ)^3389 := by
    have hnat : (5347110507 : ℕ)^4413*100000000000000^3389 ≤ 44255705521179^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347110507 10000000000 44255705521179 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1017034383/5000000000 : ℝ)^4413 ≤ (12571454295089/100000000000000 : ℝ)^3389 := by
    have hnat : (1017034383 : ℕ)^4413*100000000000000^3389 ≤ 12571454295089^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017034383 5000000000 12571454295089 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623173223/5000000000 : ℝ)^4413 ≤ (43172840169311/100000000000000 : ℝ)^3389 := by
    have hnat : (2623173223 : ℕ)^4413*100000000000000^3389 ≤ 43172840169311^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623173223 5000000000 43172840169311 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347110507/10000000000 : ℝ), (-1017034383/5000000000 : ℝ), (2623173223/5000000000 : ℝ)] ![(44255705521179/100000000000000 : ℝ), (12571454295089/100000000000000 : ℝ), (43172840169311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347110507/10000000000 : ℝ)|^4413 ≤ (44255705521179/100000000000000 : ℝ)^3389
        have hw : |(5347110507/10000000000 : ℝ)|=(5347110507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1017034383/5000000000 : ℝ)|^4413 ≤ (12571454295089/100000000000000 : ℝ)^3389
        have hw : |(-1017034383/5000000000 : ℝ)|=(1017034383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623173223/5000000000 : ℝ)|^4413 ≤ (43172840169311/100000000000000 : ℝ)^3389
        have hw : |(2623173223/5000000000 : ℝ)|=(2623173223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s4_2 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673555221/5000000000 : ℝ)*x 0 + (1311586631/2500000000 : ℝ)*x 1 + (-325451/1600000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673555221/5000000000 : ℝ)^4413 ≤ (44255704820651/100000000000000 : ℝ)^3389 := by
    have hnat : (2673555221 : ℕ)^4413*100000000000000^3389 ≤ 44255704820651^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673555221 5000000000 44255704820651 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311586631/2500000000 : ℝ)^4413 ≤ (43172841005127/100000000000000 : ℝ)^3389 := by
    have hnat : (1311586631 : ℕ)^4413*100000000000000^3389 ≤ 43172841005127^3389*2500000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311586631 2500000000 43172841005127 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325451/1600000 : ℝ)^4413 ≤ (12571454166323/100000000000000 : ℝ)^3389 := by
    have hnat : (325451 : ℕ)^4413*100000000000000^3389 ≤ 12571454166323^3389*1600000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325451 1600000 12571454166323 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673555221/5000000000 : ℝ), (1311586631/2500000000 : ℝ), (-325451/1600000 : ℝ)] ![(44255704820651/100000000000000 : ℝ), (43172841005127/100000000000000 : ℝ), (12571454166323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673555221/5000000000 : ℝ)|^4413 ≤ (44255704820651/100000000000000 : ℝ)^3389
        have hw : |(2673555221/5000000000 : ℝ)|=(2673555221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311586631/2500000000 : ℝ)|^4413 ≤ (43172841005127/100000000000000 : ℝ)^3389
        have hw : |(1311586631/2500000000 : ℝ)|=(1311586631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-325451/1600000 : ℝ)|^4413 ≤ (12571454166323/100000000000000 : ℝ)^3389
        have hw : |(-325451/1600000 : ℝ)|=(325451/1600000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s4_3 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4298329549/10000000000 : ℝ)*x 0 + (4125011983/10000000000 : ℝ)*x 1 + (279881379/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298329549/10000000000 : ℝ)^4413 ≤ (16652128131469/50000000000000 : ℝ)^3389 := by
    have hnat : (4298329549 : ℕ)^4413*50000000000000^3389 ≤ 16652128131469^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298329549 10000000000 16652128131469 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4125011983/10000000000 : ℝ)^4413 ≤ (31566351928427/100000000000000 : ℝ)^3389 := by
    have hnat : (4125011983 : ℕ)^4413*100000000000000^3389 ≤ 31566351928427^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4125011983 10000000000 31566351928427 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279881379/625000000 : ℝ)^4413 ≤ (8782347948699/25000000000000 : ℝ)^3389 := by
    have hnat : (279881379 : ℕ)^4413*25000000000000^3389 ≤ 8782347948699^3389*625000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279881379 625000000 8782347948699 25000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298329549/10000000000 : ℝ), (4125011983/10000000000 : ℝ), (279881379/625000000 : ℝ)] ![(16652128131469/50000000000000 : ℝ), (31566351928427/100000000000000 : ℝ), (8782347948699/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298329549/10000000000 : ℝ)|^4413 ≤ (16652128131469/50000000000000 : ℝ)^3389
        have hw : |(4298329549/10000000000 : ℝ)|=(4298329549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4125011983/10000000000 : ℝ)|^4413 ≤ (31566351928427/100000000000000 : ℝ)^3389
        have hw : |(4125011983/10000000000 : ℝ)|=(4125011983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(279881379/625000000 : ℝ)|^4413 ≤ (8782347948699/25000000000000 : ℝ)^3389
        have hw : |(279881379/625000000 : ℝ)|=(279881379/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s4_4 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-975852759/5000000000 : ℝ)*x 0 + (5246939261/10000000000 : ℝ)*x 1 + (54075423/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (975852759/5000000000 : ℝ)^4413 ≤ (11912697385827/100000000000000 : ℝ)^3389 := by
    have hnat : (975852759 : ℕ)^4413*100000000000000^3389 ≤ 11912697385827^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975852759 5000000000 11912697385827 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246939261/10000000000 : ℝ)^4413 ≤ (5397399079891/12500000000000 : ℝ)^3389 := by
    have hnat : (5246939261 : ℕ)^4413*12500000000000^3389 ≤ 5397399079891^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246939261 10000000000 5397399079891 12500000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54075423/100000000 : ℝ)^4413 ≤ (2245405498119/5000000000000 : ℝ)^3389 := by
    have hnat : (54075423 : ℕ)^4413*5000000000000^3389 ≤ 2245405498119^3389*100000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54075423 100000000 2245405498119 5000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-975852759/5000000000 : ℝ), (5246939261/10000000000 : ℝ), (54075423/100000000 : ℝ)] ![(11912697385827/100000000000000 : ℝ), (5397399079891/12500000000000 : ℝ), (2245405498119/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-975852759/5000000000 : ℝ)|^4413 ≤ (11912697385827/100000000000000 : ℝ)^3389
        have hw : |(-975852759/5000000000 : ℝ)|=(975852759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246939261/10000000000 : ℝ)|^4413 ≤ (5397399079891/12500000000000 : ℝ)^3389
        have hw : |(5246939261/10000000000 : ℝ)|=(5246939261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54075423/100000000 : ℝ)|^4413 ≤ (2245405498119/5000000000000 : ℝ)^3389
        have hw : |(54075423/100000000 : ℝ)|=(54075423/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s4_5 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (13262381/25000000 : ℝ)*x 0 + (-1872872959/10000000000 : ℝ)*x 1 + (5407542277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13262381/25000000 : ℝ)^4413 ≤ (8760378906991/20000000000000 : ℝ)^3389 := by
    have hnat : (13262381 : ℕ)^4413*20000000000000^3389 ≤ 8760378906991^3389*25000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13262381 25000000 8760378906991 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1872872959/10000000000 : ℝ)^4413 ≤ (11289995732361/100000000000000 : ℝ)^3389 := by
    have hnat : (1872872959 : ℕ)^4413*100000000000000^3389 ≤ 11289995732361^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872872959 10000000000 11289995732361 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407542277/10000000000 : ℝ)^4413 ≤ (22454054856829/50000000000000 : ℝ)^3389 := by
    have hnat : (5407542277 : ℕ)^4413*50000000000000^3389 ≤ 22454054856829^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407542277 10000000000 22454054856829 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13262381/25000000 : ℝ), (-1872872959/10000000000 : ℝ), (5407542277/10000000000 : ℝ)] ![(8760378906991/20000000000000 : ℝ), (11289995732361/100000000000000 : ℝ), (22454054856829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13262381/25000000 : ℝ)|^4413 ≤ (8760378906991/20000000000000 : ℝ)^3389
        have hw : |(13262381/25000000 : ℝ)|=(13262381/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1872872959/10000000000 : ℝ)|^4413 ≤ (11289995732361/100000000000000 : ℝ)^3389
        have hw : |(-1872872959/10000000000 : ℝ)|=(1872872959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407542277/10000000000 : ℝ)|^4413 ≤ (22454054856829/50000000000000 : ℝ)^3389
        have hw : |(5407542277/10000000000 : ℝ)|=(5407542277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s4_6 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33155953/62500000 : ℝ)*x 0 + (1081508447/2000000000 : ℝ)*x 1 + (-1872872907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33155953/62500000 : ℝ)^4413 ≤ (8760379079017/20000000000000 : ℝ)^3389 := by
    have hnat : (33155953 : ℕ)^4413*20000000000000^3389 ≤ 8760379079017^3389*62500000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33155953 62500000 8760379079017 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081508447/2000000000 : ℝ)^4413 ≤ (44908109259469/100000000000000 : ℝ)^3389 := by
    have hnat : (1081508447 : ℕ)^4413*100000000000000^3389 ≤ 44908109259469^3389*2000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081508447 2000000000 44908109259469 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1872872907/10000000000 : ℝ)^4413 ≤ (11289995324181/100000000000000 : ℝ)^3389 := by
    have hnat : (1872872907 : ℕ)^4413*100000000000000^3389 ≤ 11289995324181^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872872907 10000000000 11289995324181 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33155953/62500000 : ℝ), (1081508447/2000000000 : ℝ), (-1872872907/10000000000 : ℝ)] ![(8760379079017/20000000000000 : ℝ), (44908109259469/100000000000000 : ℝ), (11289995324181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33155953/62500000 : ℝ)|^4413 ≤ (8760379079017/20000000000000 : ℝ)^3389
        have hw : |(33155953/62500000 : ℝ)|=(33155953/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081508447/2000000000 : ℝ)|^4413 ≤ (44908109259469/100000000000000 : ℝ)^3389
        have hw : |(1081508447/2000000000 : ℝ)|=(1081508447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1872872907/10000000000 : ℝ)|^4413 ≤ (11289995324181/100000000000000 : ℝ)^3389
        have hw : |(-1872872907/10000000000 : ℝ)|=(1872872907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s4_7 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2149177443/5000000000 : ℝ)*x 0 + (4476808013/10000000000 : ℝ)*x 1 + (165052511/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149177443/5000000000 : ℝ)^4413 ≤ (8326127974139/25000000000000 : ℝ)^3389 := by
    have hnat : (2149177443 : ℕ)^4413*25000000000000^3389 ≤ 8326127974139^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149177443 5000000000 8326127974139 25000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4476808013/10000000000 : ℝ)^4413 ≤ (17558086810883/50000000000000 : ℝ)^3389 := by
    have hnat : (4476808013 : ℕ)^4413*50000000000000^3389 ≤ 17558086810883^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476808013 10000000000 17558086810883 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165052511/400000000 : ℝ)^4413 ≤ (3947414308457/12500000000000 : ℝ)^3389 := by
    have hnat : (165052511 : ℕ)^4413*12500000000000^3389 ≤ 3947414308457^3389*400000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165052511 400000000 3947414308457 12500000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149177443/5000000000 : ℝ), (4476808013/10000000000 : ℝ), (165052511/400000000 : ℝ)] ![(8326127974139/25000000000000 : ℝ), (17558086810883/50000000000000 : ℝ), (3947414308457/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149177443/5000000000 : ℝ)|^4413 ≤ (8326127974139/25000000000000 : ℝ)^3389
        have hw : |(2149177443/5000000000 : ℝ)|=(2149177443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4476808013/10000000000 : ℝ)|^4413 ≤ (17558086810883/50000000000000 : ℝ)^3389
        have hw : |(4476808013/10000000000 : ℝ)|=(4476808013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(165052511/400000000 : ℝ)|^4413 ≤ (3947414308457/12500000000000 : ℝ)^3389
        have hw : |(165052511/400000000 : ℝ)|=(165052511/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1453_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79559293/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2987/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2273/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14793/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2987/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11231/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2987/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11231/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2987/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11231/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2987/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11231/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2987/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11231/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2987/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11231/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11231/100000 : ℝ) ^ (1103/256 : ℝ) ≤ (162057362401227/2000000000000000000 : ℝ) := by
    have hpowers : (11231/100000 : ℝ)^1103 ≤ (162057362401227/2000000000000000000 : ℝ)^256 := by
      have hnat : (11231 : ℕ)^1103*2000000000000000000^256 ≤ 162057362401227^256*100000^1103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11231 100000 162057362401227 2000000000000000000 1103 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11231/100000 : ℝ)) (X := (162057362401227/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2987/20000 : ℝ) ^ (1103/256 : ℝ) ≤ (27668511898226473/100000000000000000000 : ℝ) := by
    have hpowers : (2987/20000 : ℝ)^1103 ≤ (27668511898226473/100000000000000000000 : ℝ)^256 := by
      have hnat : (2987 : ℕ)^1103*100000000000000000000^256 ≤ 27668511898226473^256*20000^1103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2987 20000 27668511898226473 100000000000000000000 1103 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2987/20000 : ℝ)) (X := (27668511898226473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000162057362401227/1000000000000000000 : ℝ) ≤ (2000075220496139/2000000000000000 : ℝ) ^ (1103/256 : ℝ) := by
    have hpowers : (1000162057362401227/1000000000000000000 : ℝ)^256 ≤ (2000075220496139/2000000000000000 : ℝ)^1103 := by
      have hnat : (1000162057362401227 : ℕ)^256*2000000000000000^1103 ≤ 2000075220496139^1103*1000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000162057362401227 1000000000000000000 2000075220496139 2000000000000000 256 1103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000075220496139/2000000000000000 : ℝ)) (X := (1000162057362401227/1000000000000000000 : ℝ)) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035771380018287823/100000000000000000000 : ℝ) ≤ (5000415059647073/5000000000000000 : ℝ) ^ (1103/256 : ℝ) := by
    have hpowers : (100035771380018287823/100000000000000000000 : ℝ)^256 ≤ (5000415059647073/5000000000000000 : ℝ)^1103 := by
      have hnat : (100035771380018287823 : ℕ)^256*5000000000000000^1103 ≤ 5000415059647073^1103*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035771380018287823 100000000000000000000 5000415059647073 5000000000000000 256 1103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000415059647073/5000000000000000 : ℝ)) (X := (100035771380018287823/100000000000000000000 : ℝ)) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027668511898226473/50000000000000000000 : ℝ) ≤ (10001284136107597/10000000000000000 : ℝ) ^ (1103/256 : ℝ) := by
    have hpowers : (50027668511898226473/50000000000000000000 : ℝ)^256 ≤ (10001284136107597/10000000000000000 : ℝ)^1103 := by
      have hnat : (50027668511898226473 : ℕ)^256*10000000000000000^1103 ≤ 10001284136107597^1103*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027668511898226473 50000000000000000000 10001284136107597 10000000000000000 256 1103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001284136107597/10000000000000000 : ℝ)) (X := (50027668511898226473/50000000000000000000 : ℝ)) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(162057362401227/2000000000000000000 : ℝ) ≤ ((18515597478962378959/18520000000000000000 : ℝ)+2*(454016813451/370400000000000 : ℝ)*(11231/100000 : ℝ))^(1103/256 : ℝ) := by
    rw [show (18515597478962378959/18520000000000000000 : ℝ)+2*(454016813451/370400000000000 : ℝ)*(11231/100000 : ℝ)=(2000075220496139/2000000000000000 : ℝ) by norm_num, show 1+2*(162057362401227/2000000000000000000 : ℝ)=(1000162057362401227/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27668511898226473/100000000000000000000 : ℝ)+(162057362401227/2000000000000000000 : ℝ) ≤ ((18515597478962378959/18520000000000000000 : ℝ)+(454016813451/370400000000000 : ℝ)*((2987/20000 : ℝ)+(11231/100000 : ℝ)))^(1103/256 : ℝ) := by
    rw [show (18515597478962378959/18520000000000000000 : ℝ)+(454016813451/370400000000000 : ℝ)*((2987/20000 : ℝ)+(11231/100000 : ℝ))=(5000415059647073/5000000000000000 : ℝ) by norm_num, show 1+(27668511898226473/100000000000000000000 : ℝ)+(162057362401227/2000000000000000000 : ℝ)=(100035771380018287823/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27668511898226473/100000000000000000000 : ℝ) ≤ ((18515597478962378959/18520000000000000000 : ℝ)+2*(454016813451/370400000000000 : ℝ)*(2987/20000 : ℝ))^(1103/256 : ℝ) := by
    rw [show (18515597478962378959/18520000000000000000 : ℝ)+2*(454016813451/370400000000000 : ℝ)*(2987/20000 : ℝ)=(10001284136107597/10000000000000000 : ℝ) by norm_num, show 1+2*(27668511898226473/100000000000000000000 : ℝ)=(50027668511898226473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18515597478962378959/18520000000000000000 : ℝ)*(X 1 0+X 2 0)+(454016813451/370400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1103/256 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (2987/20000 : ℝ)) (c := (18515597478962378959/18520000000000000000 : ℝ)) (alpha := (454016813451/370400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18515597478962378959/18520000000000000000 : ℝ)*(X 0 1+X 2 1)+(454016813451/370400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1103/256 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (2987/20000 : ℝ)) (c := (18515597478962378959/18520000000000000000 : ℝ)) (alpha := (454016813451/370400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18515597478962378959/18520000000000000000 : ℝ)*(X 0 2+X 1 2)+(454016813451/370400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1103/256 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (2987/20000 : ℝ)) (c := (18515597478962378959/18520000000000000000 : ℝ)) (alpha := (454016813451/370400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1951693917/10000000000 : ℝ)*X 0 0+(5408138349/10000000000 : ℝ)*X 0 1+(5246346341/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347110507/10000000000 : ℝ)*X 1 0+(-1017034383/5000000000 : ℝ)*X 1 1+(2623173223/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673555221/5000000000 : ℝ)*X 2 0+(1311586631/2500000000 : ℝ)*X 2 1+(-325451/1600000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4298329549/10000000000 : ℝ)*X 0 0+(4125011983/10000000000 : ℝ)*X 0 1+(279881379/625000000 : ℝ)*X 0 2+(4298329549/10000000000 : ℝ)*X 1 0+(4125011983/10000000000 : ℝ)*X 1 1+(279881379/625000000 : ℝ)*X 1 2+(4298329549/10000000000 : ℝ)*X 2 0+(4125011983/10000000000 : ℝ)*X 2 1+(279881379/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-975852759/5000000000 : ℝ)*X 0 0+(5246939261/10000000000 : ℝ)*X 0 1+(54075423/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((13262381/25000000 : ℝ)*X 1 0+(-1872872959/10000000000 : ℝ)*X 1 1+(5407542277/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((33155953/62500000 : ℝ)*X 2 0+(1081508447/2000000000 : ℝ)*X 2 1+(-1872872907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2149177443/5000000000 : ℝ)*X 0 0+(4476808013/10000000000 : ℝ)*X 0 1+(165052511/400000000 : ℝ)*X 0 2+(2149177443/5000000000 : ℝ)*X 1 0+(4476808013/10000000000 : ℝ)*X 1 1+(165052511/400000000 : ℝ)*X 1 2+(2149177443/5000000000 : ℝ)*X 2 0+(4476808013/10000000000 : ℝ)*X 2 1+(165052511/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5240969211767366167582368579/463000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14195459/781250000000 : ℝ)*(base19) + (1550211833/100000000000000 : ℝ)*(base23) + (102489033/100000000000000 : ℝ)*(lower2) + (34149023/12500000000000 : ℝ)*(upper3) + (35531773/25000000000000 : ℝ)*(upper5) + (2253258781544091/50000000000000 : ℝ)*(major0) + (2253258781544091/50000000000000 : ℝ)*(major1) + (2253258781544091/50000000000000 : ℝ)*(major2) + (6180818615508551/100000000000000 : ℝ)*(sp0) + (618085746046461/10000000000000 : ℝ)*(sp1) + (772607215908941/12500000000000 : ℝ)*(sp2) + (1416077833949059/50000000000000 : ℝ)*(sp3) + (4066197481/10000000000000 : ℝ)*(sp4) + (9901737639/50000000000000 : ℝ)*(sp7) + (708043867843349/25000000000000 : ℝ)*(f.failure) + (6180859277483361/100000000000000 : ℝ)*(f.sum) + (16704077742139/9260000000000000000000000000 : ℝ)*base66 + (9841490445569231269/926000000000000000000000000000000 : ℝ)*base67 + (14884182184193231269/926000000000000000000000000000000 : ℝ)*base69 + (6866006089751231269/926000000000000000000000000000000 : ℝ)*base71 + (16068546394439/9260000000000000000000000000 : ℝ)*base74 + (2679732601699231269/926000000000000000000000000000000 : ℝ)*base75 + (13991170403595231269/926000000000000000000000000000000 : ℝ)*base77 + (19338147373831231269/926000000000000000000000000000000 : ℝ)*base79 + (15832070570479/9260000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6192257/1250000000000000000000 : ℝ)*base89 + (6192257/1250000000000000000000 : ℝ)*base91 + (6192257/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26323136834970150022563/4630000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75629893/10000000000000 : ℝ)*(base19) + (504362661/50000000000000 : ℝ)*(base23) + (68150741/100000000000000 : ℝ)*(upper3) + (17888277/25000000000000 : ℝ)*(lower4) + (36273409/25000000000000 : ℝ)*(upper5) + (1134954891912621/25000000000000 : ℝ)*(major0) + (1134954891912621/25000000000000 : ℝ)*(major1) + (1134954891912621/25000000000000 : ℝ)*(major2) + (16430655457/100000000000000 : ℝ)*(sp1) + (19406573271/100000000000000 : ℝ)*(sp2) + (622653442684259/10000000000000 : ℝ)*(sp4) + (3113258619944101/50000000000000 : ℝ)*(sp5) + (6226514011543997/100000000000000 : ℝ)*(sp6) + (2853104518946947/100000000000000 : ℝ)*(sp7) + (2853104518946947/100000000000000 : ℝ)*(f.failure) + (622653442684259/10000000000000 : ℝ)*(f.sum) + (5814983718789/4630000000000000000000000000 : ℝ)*base66 + (1943619258392508461/463000000000000000000000000000000 : ℝ)*base68 + (2990667756695491539/463000000000000000000000000000000 : ℝ)*base69 + (5251635834487491539/463000000000000000000000000000000 : ℝ)*base71 + (24147834993459/4630000000000000000000000000 : ℝ)*base74 + (5544383715407491539/463000000000000000000000000000000 : ℝ)*base75 + (472565973821508461/463000000000000000000000000000000 : ℝ)*base78 + (5028332362459508461/463000000000000000000000000000000 : ℝ)*base80 + (14485918121591/4630000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (7828471/5000000000000000000000 : ℝ)*base89 + (7828471/5000000000000000000000 : ℝ)*base91 + (7828471/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1453_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79559293/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2987/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14793/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1453_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1453_s5_0 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-97590357/500000000 : ℝ)*x 0 + (1081425681/2000000000 : ℝ)*x 1 + (5247281561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (97590357/500000000 : ℝ)^4413 ≤ (11913505084431/100000000000000 : ℝ)^3389 := by
    have hnat : (97590357 : ℕ)^4413*100000000000000^3389 ≤ 11913505084431^3389*500000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97590357 500000000 11913505084431 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081425681/2000000000 : ℝ)^4413 ≤ (8980726828979/20000000000000 : ℝ)^3389 := by
    have hnat : (1081425681 : ℕ)^4413*20000000000000^3389 ≤ 8980726828979^3389*2000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081425681 2000000000 8980726828979 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247281561/10000000000 : ℝ)^4413 ≤ (10795715186581/25000000000000 : ℝ)^3389 := by
    have hnat : (5247281561 : ℕ)^4413*25000000000000^3389 ≤ 10795715186581^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247281561 10000000000 10795715186581 25000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-97590357/500000000 : ℝ), (1081425681/2000000000 : ℝ), (5247281561/10000000000 : ℝ)] ![(11913505084431/100000000000000 : ℝ), (8980726828979/20000000000000 : ℝ), (10795715186581/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-97590357/500000000 : ℝ)|^4413 ≤ (11913505084431/100000000000000 : ℝ)^3389
        have hw : |(-97590357/500000000 : ℝ)|=(97590357/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081425681/2000000000 : ℝ)|^4413 ≤ (8980726828979/20000000000000 : ℝ)^3389
        have hw : |(1081425681/2000000000 : ℝ)|=(1081425681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247281561/10000000000 : ℝ)|^4413 ≤ (10795715186581/25000000000000 : ℝ)^3389
        have hw : |(5247281561/10000000000 : ℝ)|=(5247281561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s5_1 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4277479/8000000 : ℝ)*x 0 + (-2033174117/10000000000 : ℝ)*x 1 + (2623640781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4277479/8000000 : ℝ)^4413 ≤ (44252884492117/100000000000000 : ℝ)^3389 := by
    have hnat : (4277479 : ℕ)^4413*100000000000000^3389 ≤ 44252884492117^3389*8000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4277479 8000000 44252884492117 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2033174117/10000000000 : ℝ)^4413 ≤ (12564254733239/100000000000000 : ℝ)^3389 := by
    have hnat : (2033174117 : ℕ)^4413*100000000000000^3389 ≤ 12564254733239^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033174117 10000000000 12564254733239 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623640781/5000000000 : ℝ)^4413 ≤ (43182860757041/100000000000000 : ℝ)^3389 := by
    have hnat : (2623640781 : ℕ)^4413*100000000000000^3389 ≤ 43182860757041^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623640781 5000000000 43182860757041 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4277479/8000000 : ℝ), (-2033174117/10000000000 : ℝ), (2623640781/5000000000 : ℝ)] ![(44252884492117/100000000000000 : ℝ), (12564254733239/100000000000000 : ℝ), (43182860757041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4277479/8000000 : ℝ)|^4413 ≤ (44252884492117/100000000000000 : ℝ)^3389
        have hw : |(4277479/8000000 : ℝ)|=(4277479/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2033174117/10000000000 : ℝ)|^4413 ≤ (12564254733239/100000000000000 : ℝ)^3389
        have hw : |(-2033174117/10000000000 : ℝ)|=(2033174117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623640781/5000000000 : ℝ)|^4413 ≤ (43182860757041/100000000000000 : ℝ)^3389
        have hw : |(2623640781/5000000000 : ℝ)|=(2623640781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s5_2 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334178047/625000000 : ℝ)*x 0 + (5247281559/10000000000 : ℝ)*x 1 + (-1016587059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334178047/625000000 : ℝ)^4413 ≤ (5531610564209/12500000000000 : ℝ)^3389 := by
    have hnat : (334178047 : ℕ)^4413*12500000000000^3389 ≤ 5531610564209^3389*625000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334178047 625000000 5531610564209 12500000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247281559/10000000000 : ℝ)^4413 ≤ (10795715181223/25000000000000 : ℝ)^3389 := by
    have hnat : (5247281559 : ℕ)^4413*25000000000000^3389 ≤ 10795715181223^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247281559 10000000000 10795715181223 25000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016587059/5000000000 : ℝ)^4413 ≤ (6282127370643/50000000000000 : ℝ)^3389 := by
    have hnat : (1016587059 : ℕ)^4413*50000000000000^3389 ≤ 6282127370643^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016587059 5000000000 6282127370643 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334178047/625000000 : ℝ), (5247281559/10000000000 : ℝ), (-1016587059/5000000000 : ℝ)] ![(5531610564209/12500000000000 : ℝ), (10795715181223/25000000000000 : ℝ), (6282127370643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334178047/625000000 : ℝ)|^4413 ≤ (5531610564209/12500000000000 : ℝ)^3389
        have hw : |(334178047/625000000 : ℝ)|=(334178047/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247281559/10000000000 : ℝ)|^4413 ≤ (10795715181223/25000000000000 : ℝ)^3389
        have hw : |(5247281559/10000000000 : ℝ)|=(5247281559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1016587059/5000000000 : ℝ)|^4413 ≤ (6282127370643/50000000000000 : ℝ)^3389
        have hw : |(-1016587059/5000000000 : ℝ)|=(1016587059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s5_3 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2686499/6250000 : ℝ)*x 0 + (2063563079/5000000000 : ℝ)*x 1 + (4475971391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686499/6250000 : ℝ)^4413 ≤ (33304950925177/100000000000000 : ℝ)^3389 := by
    have hnat : (2686499 : ℕ)^4413*100000000000000^3389 ≤ 33304950925177^3389*6250000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686499 6250000 33304950925177 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063563079/5000000000 : ℝ)^4413 ≤ (157937102743/500000000000 : ℝ)^3389 := by
    have hnat : (2063563079 : ℕ)^4413*500000000000^3389 ≤ 157937102743^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063563079 5000000000 157937102743 500000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4475971391/10000000000 : ℝ)^4413 ≤ (3510762850317/10000000000000 : ℝ)^3389 := by
    have hnat : (4475971391 : ℕ)^4413*10000000000000^3389 ≤ 3510762850317^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475971391 10000000000 3510762850317 10000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686499/6250000 : ℝ), (2063563079/5000000000 : ℝ), (4475971391/10000000000 : ℝ)] ![(33304950925177/100000000000000 : ℝ), (157937102743/500000000000 : ℝ), (3510762850317/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686499/6250000 : ℝ)|^4413 ≤ (33304950925177/100000000000000 : ℝ)^3389
        have hw : |(2686499/6250000 : ℝ)|=(2686499/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2063563079/5000000000 : ℝ)|^4413 ≤ (157937102743/500000000000 : ℝ)^3389
        have hw : |(2063563079/5000000000 : ℝ)|=(2063563079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4475971391/10000000000 : ℝ)|^4413 ≤ (3510762850317/10000000000000 : ℝ)^3389
        have hw : |(4475971391/10000000000 : ℝ)|=(4475971391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s5_4 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-975909157/5000000000 : ℝ)*x 0 + (104957207/200000000 : ℝ)*x 1 + (5406546609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (975909157/5000000000 : ℝ)^4413 ≤ (11913593896923/100000000000000 : ℝ)^3389 := by
    have hnat : (975909157 : ℕ)^4413*100000000000000^3389 ≤ 11913593896923^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975909157 5000000000 11913593896923 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104957207/200000000 : ℝ)^4413 ≤ (43189063248219/100000000000000 : ℝ)^3389 := by
    have hnat : (104957207 : ℕ)^4413*100000000000000^3389 ≤ 43189063248219^3389*200000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104957207 200000000 43189063248219 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406546609/10000000000 : ℝ)^4413 ≤ (8979468567697/20000000000000 : ℝ)^3389 := by
    have hnat : (5406546609 : ℕ)^4413*20000000000000^3389 ≤ 8979468567697^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406546609 10000000000 8979468567697 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-975909157/5000000000 : ℝ), (104957207/200000000 : ℝ), (5406546609/10000000000 : ℝ)] ![(11913593896923/100000000000000 : ℝ), (43189063248219/100000000000000 : ℝ), (8979468567697/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-975909157/5000000000 : ℝ)|^4413 ≤ (11913593896923/100000000000000 : ℝ)^3389
        have hw : |(-975909157/5000000000 : ℝ)|=(975909157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104957207/200000000 : ℝ)|^4413 ≤ (43189063248219/100000000000000 : ℝ)^3389
        have hw : |(104957207/200000000 : ℝ)|=(104957207/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406546609/10000000000 : ℝ)|^4413 ≤ (8979468567697/20000000000000 : ℝ)^3389
        have hw : |(5406546609/10000000000 : ℝ)|=(5406546609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s5_5 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305197273/10000000000 : ℝ)*x 0 + (-936954537/5000000000 : ℝ)*x 1 + (5406546637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305197273/10000000000 : ℝ)^4413 ≤ (8760905466777/20000000000000 : ℝ)^3389 := by
    have hnat : (5305197273 : ℕ)^4413*20000000000000^3389 ≤ 8760905466777^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305197273 10000000000 8760905466777 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (936954537/5000000000 : ℝ)^4413 ≤ (11298129505777/100000000000000 : ℝ)^3389 := by
    have hnat : (936954537 : ℕ)^4413*100000000000000^3389 ≤ 11298129505777^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936954537 5000000000 11298129505777 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406546637/10000000000 : ℝ)^4413 ≤ (44897343141261/100000000000000 : ℝ)^3389 := by
    have hnat : (5406546637 : ℕ)^4413*100000000000000^3389 ≤ 44897343141261^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406546637 10000000000 44897343141261 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305197273/10000000000 : ℝ), (-936954537/5000000000 : ℝ), (5406546637/10000000000 : ℝ)] ![(8760905466777/20000000000000 : ℝ), (11298129505777/100000000000000 : ℝ), (44897343141261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305197273/10000000000 : ℝ)|^4413 ≤ (8760905466777/20000000000000 : ℝ)^3389
        have hw : |(5305197273/10000000000 : ℝ)|=(5305197273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-936954537/5000000000 : ℝ)|^4413 ≤ (11298129505777/100000000000000 : ℝ)^3389
        have hw : |(-936954537/5000000000 : ℝ)|=(936954537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406546637/10000000000 : ℝ)|^4413 ≤ (44897343141261/100000000000000 : ℝ)^3389
        have hw : |(5406546637/10000000000 : ℝ)|=(5406546637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s5_6 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663149659/1250000000 : ℝ)*x 0 + (675818331/1250000000 : ℝ)*x 1 + (-1873909061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663149659/1250000000 : ℝ)^4413 ≤ (21902263661567/50000000000000 : ℝ)^3389 := by
    have hnat : (663149659 : ℕ)^4413*50000000000000^3389 ≤ 21902263661567^3389*1250000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663149659 1250000000 21902263661567 50000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675818331/1250000000 : ℝ)^4413 ≤ (2806083953763/6250000000000 : ℝ)^3389 := by
    have hnat : (675818331 : ℕ)^4413*6250000000000^3389 ≤ 2806083953763^3389*1250000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675818331 1250000000 2806083953763 6250000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1873909061/10000000000 : ℝ)^4413 ≤ (2259625880743/20000000000000 : ℝ)^3389 := by
    have hnat : (1873909061 : ℕ)^4413*20000000000000^3389 ≤ 2259625880743^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873909061 10000000000 2259625880743 20000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663149659/1250000000 : ℝ), (675818331/1250000000 : ℝ), (-1873909061/10000000000 : ℝ)] ![(21902263661567/50000000000000 : ℝ), (2806083953763/6250000000000 : ℝ), (2259625880743/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663149659/1250000000 : ℝ)|^4413 ≤ (21902263661567/50000000000000 : ℝ)^3389
        have hw : |(663149659/1250000000 : ℝ)|=(663149659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675818331/1250000000 : ℝ)|^4413 ≤ (2806083953763/6250000000000 : ℝ)^3389
        have hw : |(675818331/1250000000 : ℝ)|=(675818331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1873909061/10000000000 : ℝ)|^4413 ≤ (2259625880743/20000000000000 : ℝ)^3389
        have hw : |(-1873909061/10000000000 : ℝ)|=(1873909061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1453_s5_7 (p : ℝ) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2149211383/5000000000 : ℝ)*x 0 + (4474708279/10000000000 : ℝ)*x 1 + (4128395841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149211383/5000000000 : ℝ)^4413 ≤ (33305196763227/100000000000000 : ℝ)^3389 := by
    have hnat : (2149211383 : ℕ)^4413*100000000000000^3389 ≤ 33305196763227^3389*5000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149211383 5000000000 33305196763227 100000000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4474708279/10000000000 : ℝ)^4413 ≤ (2193420512541/6250000000000 : ℝ)^3389 := by
    have hnat : (4474708279 : ℕ)^4413*6250000000000^3389 ≤ 2193420512541^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474708279 10000000000 2193420512541 6250000000000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4128395841/10000000000 : ℝ)^4413 ≤ (30859448269/97656250000 : ℝ)^3389 := by
    have hnat : (4128395841 : ℕ)^4413*97656250000^3389 ≤ 30859448269^3389*10000000000^4413 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128395841 10000000000 30859448269 97656250000 4413 3389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4413/1024 : ℝ)) 4413 3389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149211383/5000000000 : ℝ), (4474708279/10000000000 : ℝ), (4128395841/10000000000 : ℝ)] ![(33305196763227/100000000000000 : ℝ), (2193420512541/6250000000000 : ℝ), (30859448269/97656250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149211383/5000000000 : ℝ)|^4413 ≤ (33305196763227/100000000000000 : ℝ)^3389
        have hw : |(2149211383/5000000000 : ℝ)|=(2149211383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4474708279/10000000000 : ℝ)|^4413 ≤ (2193420512541/6250000000000 : ℝ)^3389
        have hw : |(4474708279/10000000000 : ℝ)|=(4474708279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4128395841/10000000000 : ℝ)|^4413 ≤ (30859448269/97656250000 : ℝ)^3389
        have hw : |(4128395841/10000000000 : ℝ)|=(4128395841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1453_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79559293/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14793/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2277/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3693/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14793/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2273/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14793/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2273/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14793/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2273/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14793/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2273/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14793/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2273/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14793/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2273/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2273/20000 : ℝ) ^ (1103/256 : ℝ) ≤ (852770939449571/10000000000000000000 : ℝ) := by
    have hpowers : (2273/20000 : ℝ)^1103 ≤ (852770939449571/10000000000000000000 : ℝ)^256 := by
      have hnat : (2273 : ℕ)^1103*10000000000000000000^256 ≤ 852770939449571^256*20000^1103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2273 20000 852770939449571 10000000000000000000 1103 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2273/20000 : ℝ)) (X := (852770939449571/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14793/100000 : ℝ) ^ (1103/256 : ℝ) ≤ (1327637715916659/5000000000000000000 : ℝ) := by
    have hpowers : (14793/100000 : ℝ)^1103 ≤ (1327637715916659/5000000000000000000 : ℝ)^256 := by
      have hnat : (14793 : ℕ)^1103*5000000000000000000^256 ≤ 1327637715916659^256*100000^1103 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14793 100000 1327637715916659 5000000000000000000 1103 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14793/100000 : ℝ)) (X := (1327637715916659/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000852770939449571/5000000000000000000 : ℝ) ≤ (2500098955152311/2500000000000000 : ℝ) ^ (1103/256 : ℝ) := by
    have hpowers : (5000852770939449571/5000000000000000000 : ℝ)^256 ≤ (2500098955152311/2500000000000000 : ℝ)^1103 := by
      have hnat : (5000852770939449571 : ℕ)^256*2500000000000000^1103 ≤ 2500098955152311^1103*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000852770939449571 5000000000000000000 2500098955152311 2500000000000000 256 1103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500098955152311/2500000000000000 : ℝ)) (X := (5000852770939449571/5000000000000000000 : ℝ)) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003508046371282889/10000000000000000000 : ℝ) ≤ (1250101760985287/1250000000000000 : ℝ) ^ (1103/256 : ℝ) := by
    have hpowers : (10003508046371282889/10000000000000000000 : ℝ)^256 ≤ (1250101760985287/1250000000000000 : ℝ)^1103 := by
      have hnat : (10003508046371282889 : ℕ)^256*1250000000000000^1103 ≤ 1250101760985287^1103*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003508046371282889 10000000000000000000 1250101760985287 1250000000000000 256 1103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250101760985287/1250000000000000 : ℝ)) (X := (10003508046371282889/10000000000000000000 : ℝ)) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501327637715916659/2500000000000000000 : ℝ) ≤ (2500308088788837/2500000000000000 : ℝ) ^ (1103/256 : ℝ) := by
    have hpowers : (2501327637715916659/2500000000000000000 : ℝ)^256 ≤ (2500308088788837/2500000000000000 : ℝ)^1103 := by
      have hnat : (2501327637715916659 : ℕ)^256*2500000000000000^1103 ≤ 2500308088788837^1103*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501327637715916659 2500000000000000000 2500308088788837 2500000000000000 256 1103 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500308088788837/2500000000000000 : ℝ)) (X := (2501327637715916659/2500000000000000000 : ℝ)) (by norm_num) 1103 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(852770939449571/10000000000000000000 : ℝ) ≤ ((4283981207241502059/4285000000000000000 : ℝ)+2*(104566818263/85700000000000 : ℝ)*(2273/20000 : ℝ))^(1103/256 : ℝ) := by
    rw [show (4283981207241502059/4285000000000000000 : ℝ)+2*(104566818263/85700000000000 : ℝ)*(2273/20000 : ℝ)=(2500098955152311/2500000000000000 : ℝ) by norm_num, show 1+2*(852770939449571/10000000000000000000 : ℝ)=(5000852770939449571/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1327637715916659/5000000000000000000 : ℝ)+(852770939449571/10000000000000000000 : ℝ) ≤ ((4283981207241502059/4285000000000000000 : ℝ)+(104566818263/85700000000000 : ℝ)*((14793/100000 : ℝ)+(2273/20000 : ℝ)))^(1103/256 : ℝ) := by
    rw [show (4283981207241502059/4285000000000000000 : ℝ)+(104566818263/85700000000000 : ℝ)*((14793/100000 : ℝ)+(2273/20000 : ℝ))=(1250101760985287/1250000000000000 : ℝ) by norm_num, show 1+(1327637715916659/5000000000000000000 : ℝ)+(852770939449571/10000000000000000000 : ℝ)=(10003508046371282889/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1327637715916659/5000000000000000000 : ℝ) ≤ ((4283981207241502059/4285000000000000000 : ℝ)+2*(104566818263/85700000000000 : ℝ)*(14793/100000 : ℝ))^(1103/256 : ℝ) := by
    rw [show (4283981207241502059/4285000000000000000 : ℝ)+2*(104566818263/85700000000000 : ℝ)*(14793/100000 : ℝ)=(2500308088788837/2500000000000000 : ℝ) by norm_num, show 1+2*(1327637715916659/5000000000000000000 : ℝ)=(2501327637715916659/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4283981207241502059/4285000000000000000 : ℝ)*(X 1 0+X 2 0)+(104566818263/85700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1103/256 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (14793/100000 : ℝ)) (c := (4283981207241502059/4285000000000000000 : ℝ)) (alpha := (104566818263/85700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4283981207241502059/4285000000000000000 : ℝ)*(X 0 1+X 2 1)+(104566818263/85700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1103/256 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (14793/100000 : ℝ)) (c := (4283981207241502059/4285000000000000000 : ℝ)) (alpha := (104566818263/85700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4283981207241502059/4285000000000000000 : ℝ)*(X 0 2+X 1 2)+(104566818263/85700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1103/256 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (14793/100000 : ℝ)) (c := (4283981207241502059/4285000000000000000 : ℝ)) (alpha := (104566818263/85700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-97590357/500000000 : ℝ)*X 0 0+(1081425681/2000000000 : ℝ)*X 0 1+(5247281561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((4277479/8000000 : ℝ)*X 1 0+(-2033174117/10000000000 : ℝ)*X 1 1+(2623640781/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334178047/625000000 : ℝ)*X 2 0+(5247281559/10000000000 : ℝ)*X 2 1+(-1016587059/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2686499/6250000 : ℝ)*X 0 0+(2063563079/5000000000 : ℝ)*X 0 1+(4475971391/10000000000 : ℝ)*X 0 2+(2686499/6250000 : ℝ)*X 1 0+(2063563079/5000000000 : ℝ)*X 1 1+(4475971391/10000000000 : ℝ)*X 1 2+(2686499/6250000 : ℝ)*X 2 0+(2063563079/5000000000 : ℝ)*X 2 1+(4475971391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-975909157/5000000000 : ℝ)*X 0 0+(104957207/200000000 : ℝ)*X 0 1+(5406546609/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305197273/10000000000 : ℝ)*X 1 0+(-936954537/5000000000 : ℝ)*X 1 1+(5406546637/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663149659/1250000000 : ℝ)*X 2 0+(675818331/1250000000 : ℝ)*X 2 1+(-1873909061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2149211383/5000000000 : ℝ)*X 0 0+(4474708279/10000000000 : ℝ)*X 0 1+(4128395841/10000000000 : ℝ)*X 0 2+(2149211383/5000000000 : ℝ)*X 1 0+(4474708279/10000000000 : ℝ)*X 1 1+(4128395841/10000000000 : ℝ)*X 1 2+(2149211383/5000000000 : ℝ)*X 2 0+(4474708279/10000000000 : ℝ)*X 2 1+(4128395841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1453_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (552654766657055884933479033/53562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92983581/5000000000000 : ℝ)*(base19) + (1736526257/100000000000000 : ℝ)*(base23) + (2683807/4000000000000 : ℝ)*(lower2) + (16052011/6250000000000 : ℝ)*(upper3) + (32954291/20000000000000 : ℝ)*(upper5) + (2280676758501229/50000000000000 : ℝ)*(major0) + (2280676758501229/50000000000000 : ℝ)*(major1) + (2280676758501229/50000000000000 : ℝ)*(major2) + (3128014745741147/50000000000000 : ℝ)*(sp0) + (625606704051953/10000000000000 : ℝ)*(sp1) + (6256067163664893/100000000000000 : ℝ)*(sp2) + (358327279736999/12500000000000 : ℝ)*(sp3) + (4926088607/12500000000000 : ℝ)*(sp4) + (9775993183/50000000000000 : ℝ)*(sp7) + (1433318894941179/50000000000000 : ℝ)*(f.failure) + (125121378003823/2000000000000 : ℝ)*(f.sum) + (16502341861483/2142500000000000000000000000 : ℝ)*base66 + (3521869501341119489/214250000000000000000000000000000 : ℝ)*base68 + (1292730099934119489/214250000000000000000000000000000 : ℝ)*base70 + (1716921476729119489/214250000000000000000000000000000 : ℝ)*base72 + (14371035626973/2142500000000000000000000000 : ℝ)*base74 + (935073066947619489/214250000000000000000000000000000 : ℝ)*base76 + (4834725192442119489/214250000000000000000000000000000 : ℝ)*base78 + (686774473141630511/214250000000000000000000000000000 : ℝ)*base79 + (9704340861407/2142500000000000000000000000 : ℝ)*base81 + (27826447/2500000000000000000000 : ℝ)*base89 + (27826447/2500000000000000000000 : ℝ)*base91 + (27826447/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (756632992257605145552928911/107125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (138419173/12500000000000 : ℝ)*(base19) + (240223523/20000000000000 : ℝ)*(base23) + (18402807/12500000000000 : ℝ)*(upper3) + (5023971/12500000000000 : ℝ)*(lower4) + (139393013/100000000000000 : ℝ)*(upper5) + (2297326922749019/50000000000000 : ℝ)*(major0) + (2297326922749019/50000000000000 : ℝ)*(major1) + (2297326922749019/50000000000000 : ℝ)*(major2) + (23801830667/100000000000000 : ℝ)*(sp1) + (26246443041/100000000000000 : ℝ)*(sp2) + (787717708931049/12500000000000 : ℝ)*(sp4) + (6301716762264341/100000000000000 : ℝ)*(sp5) + (787714277985967/12500000000000 : ℝ)*(sp6) + (180472861506969/6250000000000 : ℝ)*(sp7) + (180472861506969/6250000000000 : ℝ)*(f.failure) + (787717708931049/12500000000000 : ℝ)*(f.sum) + (8032875897083/2142500000000000000000000000 : ℝ)*base66 + (1119686335400580121/214250000000000000000000000000000 : ℝ)*base67 + (4293616092642580121/214250000000000000000000000000000 : ℝ)*base69 + (536956418028830121/214250000000000000000000000000000 : ℝ)*base71 + (4905539426761/4285000000000000000000000000 : ℝ)*base74 + (7240039866654830121/214250000000000000000000000000000 : ℝ)*base75 + (2308282716124580121/214250000000000000000000000000000 : ℝ)*base77 + (2076476990780830121/214250000000000000000000000000000 : ℝ)*base79 + (433566331191/267812500000000000000000000 : ℝ)*base82 + (537083/312500000000000000000 : ℝ)*base90 + (537083/312500000000000000000 : ℝ)*base92 + (537083/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1453_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79559293/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14793/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1453_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1453_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79559293/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15729/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2623/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1453_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1453_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1453_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1103/256 : ℝ) ≤ p) (hpb : p ≤ (4413/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79559293/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15729/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2623/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1453_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
