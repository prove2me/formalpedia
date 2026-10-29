-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1388_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:25:01.030076+00:00
-- url     : https://prove2.me/submissions/80c29f97-07ea-4528-8682-5117c8e17c99

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
theorem support_rectangle_w1388_s3_0 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2003545631/10000000000 : ℝ)*x 0 + (2710824781/5000000000 : ℝ)*x 1 + (130887037/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2003545631/10000000000 : ℝ)^1087 ≤ (24419665399/200000000000 : ℝ)^831 := by
    have hnat : (2003545631 : ℕ)^1087*200000000000^831 ≤ 24419665399^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003545631 10000000000 24419665399 200000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2710824781/5000000000 : ℝ)^1087 ≤ (11224507617471/25000000000000 : ℝ)^831 := by
    have hnat : (2710824781 : ℕ)^1087*25000000000000^831 ≤ 11224507617471^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710824781 5000000000 11224507617471 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130887037/250000000 : ℝ)^1087 ≤ (42892136816809/100000000000000 : ℝ)^831 := by
    have hnat : (130887037 : ℕ)^1087*100000000000000^831 ≤ 42892136816809^831*250000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130887037 250000000 42892136816809 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2003545631/10000000000 : ℝ), (2710824781/5000000000 : ℝ), (130887037/250000000 : ℝ)] ![(24419665399/200000000000 : ℝ), (11224507617471/25000000000000 : ℝ), (42892136816809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2003545631/10000000000 : ℝ)|^1087 ≤ (24419665399/200000000000 : ℝ)^831
        have hw : |(-2003545631/10000000000 : ℝ)|=(2003545631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2710824781/5000000000 : ℝ)|^1087 ≤ (11224507617471/25000000000000 : ℝ)^831
        have hw : |(2710824781/5000000000 : ℝ)|=(2710824781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130887037/250000000 : ℝ)|^1087 ≤ (42892136816809/100000000000000 : ℝ)^831
        have hw : |(130887037/250000000 : ℝ)|=(130887037/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s3_1 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5351060517/10000000000 : ℝ)*x 0 + (-2098588423/10000000000 : ℝ)*x 1 + (5235481651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351060517/10000000000 : ℝ)^1087 ≤ (22067460184043/50000000000000 : ℝ)^831 := by
    have hnat : (5351060517 : ℕ)^1087*50000000000000^831 ≤ 22067460184043^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351060517 10000000000 22067460184043 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2098588423/10000000000 : ℝ)^1087 ≤ (3243235244181/25000000000000 : ℝ)^831 := by
    have hnat : (2098588423 : ℕ)^1087*25000000000000^831 ≤ 3243235244181^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098588423 10000000000 3243235244181 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5235481651/10000000000 : ℝ)^1087 ≤ (10723034662329/25000000000000 : ℝ)^831 := by
    have hnat : (5235481651 : ℕ)^1087*25000000000000^831 ≤ 10723034662329^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235481651 10000000000 10723034662329 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351060517/10000000000 : ℝ), (-2098588423/10000000000 : ℝ), (5235481651/10000000000 : ℝ)] ![(22067460184043/50000000000000 : ℝ), (3243235244181/25000000000000 : ℝ), (10723034662329/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351060517/10000000000 : ℝ)|^1087 ≤ (22067460184043/50000000000000 : ℝ)^831
        have hw : |(5351060517/10000000000 : ℝ)|=(5351060517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2098588423/10000000000 : ℝ)|^1087 ≤ (3243235244181/25000000000000 : ℝ)^831
        have hw : |(-2098588423/10000000000 : ℝ)|=(2098588423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5235481651/10000000000 : ℝ)|^1087 ≤ (10723034662329/25000000000000 : ℝ)^831
        have hw : |(5235481651/10000000000 : ℝ)|=(5235481651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s3_2 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5351060527/10000000000 : ℝ)*x 0 + (2617740831/5000000000 : ℝ)*x 1 + (-1049294197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351060527/10000000000 : ℝ)^1087 ≤ (44134920475973/100000000000000 : ℝ)^831 := by
    have hnat : (5351060527 : ℕ)^1087*100000000000000^831 ≤ 44134920475973^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351060527 10000000000 44134920475973 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617740831/5000000000 : ℝ)^1087 ≤ (42892138767197/100000000000000 : ℝ)^831 := by
    have hnat : (2617740831 : ℕ)^1087*100000000000000^831 ≤ 42892138767197^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617740831 5000000000 42892138767197 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049294197/5000000000 : ℝ)^1087 ≤ (12972940742227/100000000000000 : ℝ)^831 := by
    have hnat : (1049294197 : ℕ)^1087*100000000000000^831 ≤ 12972940742227^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049294197 5000000000 12972940742227 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351060527/10000000000 : ℝ), (2617740831/5000000000 : ℝ), (-1049294197/5000000000 : ℝ)] ![(44134920475973/100000000000000 : ℝ), (42892138767197/100000000000000 : ℝ), (12972940742227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351060527/10000000000 : ℝ)|^1087 ≤ (44134920475973/100000000000000 : ℝ)^831
        have hw : |(5351060527/10000000000 : ℝ)|=(5351060527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2617740831/5000000000 : ℝ)|^1087 ≤ (42892138767197/100000000000000 : ℝ)^831
        have hw : |(2617740831/5000000000 : ℝ)|=(2617740831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1049294197/5000000000 : ℝ)|^1087 ≤ (12972940742227/100000000000000 : ℝ)^831
        have hw : |(-1049294197/5000000000 : ℝ)|=(1049294197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s3_3 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2156957841/5000000000 : ℝ)*x 0 + (4119739349/10000000000 : ℝ)*x 1 + (903287937/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156957841/5000000000 : ℝ)^1087 ≤ (8323946532141/25000000000000 : ℝ)^831 := by
    have hnat : (2156957841 : ℕ)^1087*25000000000000^831 ≤ 8323946532141^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156957841 5000000000 8323946532141 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4119739349/10000000000 : ℝ)^1087 ≤ (15674565974191/50000000000000 : ℝ)^831 := by
    have hnat : (4119739349 : ℕ)^1087*50000000000000^831 ≤ 15674565974191^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4119739349 10000000000 15674565974191 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903287937/2000000000 : ℝ)^1087 ≤ (4419385238897/12500000000000 : ℝ)^831 := by
    have hnat : (903287937 : ℕ)^1087*12500000000000^831 ≤ 4419385238897^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903287937 2000000000 4419385238897 12500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2156957841/5000000000 : ℝ), (4119739349/10000000000 : ℝ), (903287937/2000000000 : ℝ)] ![(8323946532141/25000000000000 : ℝ), (15674565974191/50000000000000 : ℝ), (4419385238897/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2156957841/5000000000 : ℝ)|^1087 ≤ (8323946532141/25000000000000 : ℝ)^831
        have hw : |(2156957841/5000000000 : ℝ)|=(2156957841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4119739349/10000000000 : ℝ)|^1087 ≤ (15674565974191/50000000000000 : ℝ)^831
        have hw : |(4119739349/10000000000 : ℝ)|=(4119739349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(903287937/2000000000 : ℝ)|^1087 ≤ (4419385238897/12500000000000 : ℝ)^831
        have hw : |(903287937/2000000000 : ℝ)|=(903287937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s3_4 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-200356313/1000000000 : ℝ)*x 0 + (5236238687/10000000000 : ℝ)*x 1 + (5420887551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (200356313/1000000000 : ℝ)^1087 ≤ (12209972192627/100000000000000 : ℝ)^831 := by
    have hnat : (200356313 : ℕ)^1087*100000000000000^831 ≤ 12209972192627^831*1000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200356313 1000000000 12209972192627 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5236238687/10000000000 : ℝ)^1087 ≤ (42900251542993/100000000000000 : ℝ)^831 := by
    have hnat : (5236238687 : ℕ)^1087*100000000000000^831 ≤ 42900251542993^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236238687 10000000000 42900251542993 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420887551/10000000000 : ℝ)^1087 ≤ (44889776246727/100000000000000 : ℝ)^831 := by
    have hnat : (5420887551 : ℕ)^1087*100000000000000^831 ≤ 44889776246727^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420887551 10000000000 44889776246727 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-200356313/1000000000 : ℝ), (5236238687/10000000000 : ℝ), (5420887551/10000000000 : ℝ)] ![(12209972192627/100000000000000 : ℝ), (42900251542993/100000000000000 : ℝ), (44889776246727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-200356313/1000000000 : ℝ)|^1087 ≤ (12209972192627/100000000000000 : ℝ)^831
        have hw : |(-200356313/1000000000 : ℝ)|=(200356313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5236238687/10000000000 : ℝ)|^1087 ≤ (42900251542993/100000000000000 : ℝ)^831
        have hw : |(5236238687/10000000000 : ℝ)|=(5236238687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420887551/10000000000 : ℝ)|^1087 ≤ (44889776246727/100000000000000 : ℝ)^831
        have hw : |(5420887551/10000000000 : ℝ)|=(5420887551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s3_5 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1325715913/2500000000 : ℝ)*x 0 + (-239147759/1250000000 : ℝ)*x 1 + (5420888069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325715913/2500000000 : ℝ)^1087 ≤ (5451957437113/12500000000000 : ℝ)^831 := by
    have hnat : (1325715913 : ℕ)^1087*12500000000000^831 ≤ 5451957437113^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325715913 2500000000 5451957437113 12500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (239147759/1250000000 : ℝ)^1087 ≤ (718409913817/6250000000000 : ℝ)^831 := by
    have hnat : (239147759 : ℕ)^1087*6250000000000^831 ≤ 718409913817^831*1250000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239147759 1250000000 718409913817 6250000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420888069/10000000000 : ℝ)^1087 ≤ (44889781857663/100000000000000 : ℝ)^831 := by
    have hnat : (5420888069 : ℕ)^1087*100000000000000^831 ≤ 44889781857663^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420888069 10000000000 44889781857663 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325715913/2500000000 : ℝ), (-239147759/1250000000 : ℝ), (5420888069/10000000000 : ℝ)] ![(5451957437113/12500000000000 : ℝ), (718409913817/6250000000000 : ℝ), (44889781857663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325715913/2500000000 : ℝ)|^1087 ≤ (5451957437113/12500000000000 : ℝ)^831
        have hw : |(1325715913/2500000000 : ℝ)|=(1325715913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-239147759/1250000000 : ℝ)|^1087 ≤ (718409913817/6250000000000 : ℝ)^831
        have hw : |(-239147759/1250000000 : ℝ)|=(239147759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420888069/10000000000 : ℝ)|^1087 ≤ (44889781857663/100000000000000 : ℝ)^831
        have hw : |(5420888069/10000000000 : ℝ)|=(5420888069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s3_6 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2651432243/5000000000 : ℝ)*x 0 + (2710443769/5000000000 : ℝ)*x 1 + (-1913181663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651432243/5000000000 : ℝ)^1087 ≤ (21807834234837/50000000000000 : ℝ)^831 := by
    have hnat : (2651432243 : ℕ)^1087*50000000000000^831 ≤ 21807834234837^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651432243 5000000000 21807834234837 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2710443769/5000000000 : ℝ)^1087 ≤ (5611222013239/12500000000000 : ℝ)^831 := by
    have hnat : (2710443769 : ℕ)^1087*12500000000000^831 ≤ 5611222013239^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710443769 5000000000 5611222013239 12500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1913181663/10000000000 : ℝ)^1087 ≤ (5747277703381/50000000000000 : ℝ)^831 := by
    have hnat : (1913181663 : ℕ)^1087*50000000000000^831 ≤ 5747277703381^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913181663 10000000000 5747277703381 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651432243/5000000000 : ℝ), (2710443769/5000000000 : ℝ), (-1913181663/10000000000 : ℝ)] ![(21807834234837/50000000000000 : ℝ), (5611222013239/12500000000000 : ℝ), (5747277703381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651432243/5000000000 : ℝ)|^1087 ≤ (21807834234837/50000000000000 : ℝ)^831
        have hw : |(2651432243/5000000000 : ℝ)|=(2651432243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2710443769/5000000000 : ℝ)|^1087 ≤ (5611222013239/12500000000000 : ℝ)^831
        have hw : |(2710443769/5000000000 : ℝ)|=(2710443769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1913181663/10000000000 : ℝ)|^1087 ≤ (5747277703381/50000000000000 : ℝ)^831
        have hw : |(-1913181663/10000000000 : ℝ)|=(1913181663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s3_7 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4313952759/10000000000 : ℝ)*x 0 + (4514826663/10000000000 : ℝ)*x 1 + (412136091/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313952759/10000000000 : ℝ)^1087 ≤ (33296160455693/100000000000000 : ℝ)^831 := by
    have hnat : (4313952759 : ℕ)^1087*100000000000000^831 ≤ 33296160455693^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313952759 10000000000 33296160455693 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514826663/10000000000 : ℝ)^1087 ≤ (17669283037807/50000000000000 : ℝ)^831 := by
    have hnat : (4514826663 : ℕ)^1087*50000000000000^831 ≤ 17669283037807^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514826663 10000000000 17669283037807 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (412136091/1000000000 : ℝ)^1087 ≤ (31365273449417/100000000000000 : ℝ)^831 := by
    have hnat : (412136091 : ℕ)^1087*100000000000000^831 ≤ 31365273449417^831*1000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412136091 1000000000 31365273449417 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313952759/10000000000 : ℝ), (4514826663/10000000000 : ℝ), (412136091/1000000000 : ℝ)] ![(33296160455693/100000000000000 : ℝ), (17669283037807/50000000000000 : ℝ), (31365273449417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313952759/10000000000 : ℝ)|^1087 ≤ (33296160455693/100000000000000 : ℝ)^831
        have hw : |(4313952759/10000000000 : ℝ)|=(4313952759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514826663/10000000000 : ℝ)|^1087 ≤ (17669283037807/50000000000000 : ℝ)^831
        have hw : |(4514826663/10000000000 : ℝ)|=(4514826663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(412136091/1000000000 : ℝ)|^1087 ≤ (31365273449417/100000000000000 : ℝ)^831
        have hw : |(412136091/1000000000 : ℝ)|=(412136091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s3_8 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-82603731/10000000000 : ℝ)*x 0 + (285712471/500000000 : ℝ)*x 1 + (377538657/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82603731/10000000000 : ℝ)^1087 ≤ (188497335657/100000000000000 : ℝ)^831 := by
    have hnat : (82603731 : ℕ)^1087*100000000000000^831 ≤ 188497335657^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82603731 10000000000 188497335657 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285712471/500000000 : ℝ)^1087 ≤ (4809361428289/10000000000000 : ℝ)^831 := by
    have hnat : (285712471 : ℕ)^1087*10000000000000^831 ≤ 4809361428289^831*500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285712471 500000000 4809361428289 10000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (377538657/625000000 : ℝ)^1087 ≤ (25858944184961/50000000000000 : ℝ)^831 := by
    have hnat : (377538657 : ℕ)^1087*50000000000000^831 ≤ 25858944184961^831*625000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377538657 625000000 25858944184961 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-82603731/10000000000 : ℝ), (285712471/500000000 : ℝ), (377538657/625000000 : ℝ)] ![(188497335657/100000000000000 : ℝ), (4809361428289/10000000000000 : ℝ), (25858944184961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-82603731/10000000000 : ℝ)|^1087 ≤ (188497335657/100000000000000 : ℝ)^831
        have hw : |(-82603731/10000000000 : ℝ)|=(82603731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(285712471/500000000 : ℝ)|^1087 ≤ (4809361428289/10000000000000 : ℝ)^831
        have hw : |(285712471/500000000 : ℝ)|=(285712471/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(377538657/625000000 : ℝ)|^1087 ≤ (25858944184961/50000000000000 : ℝ)^831
        have hw : |(377538657/625000000 : ℝ)|=(377538657/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s3_9 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (64501329/625000000 : ℝ)*x 0 + (-2107483227/5000000000 : ℝ)*x 1 + (3493891499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64501329/625000000 : ℝ)^1087 ≤ (1281690126047/25000000000000 : ℝ)^831 := by
    have hnat : (64501329 : ℕ)^1087*25000000000000^831 ≤ 1281690126047^831*625000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64501329 625000000 1281690126047 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107483227/5000000000 : ℝ)^1087 ≤ (1009385950017/3125000000000 : ℝ)^831 := by
    have hnat : (2107483227 : ℕ)^1087*3125000000000^831 ≤ 1009385950017^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107483227 5000000000 1009385950017 3125000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3493891499/5000000000 : ℝ)^1087 ≤ (1564322226971/2500000000000 : ℝ)^831 := by
    have hnat : (3493891499 : ℕ)^1087*2500000000000^831 ≤ 1564322226971^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3493891499 5000000000 1564322226971 2500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(64501329/625000000 : ℝ), (-2107483227/5000000000 : ℝ), (3493891499/5000000000 : ℝ)] ![(1281690126047/25000000000000 : ℝ), (1009385950017/3125000000000 : ℝ), (1564322226971/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(64501329/625000000 : ℝ)|^1087 ≤ (1281690126047/25000000000000 : ℝ)^831
        have hw : |(64501329/625000000 : ℝ)|=(64501329/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2107483227/5000000000 : ℝ)|^1087 ≤ (1009385950017/3125000000000 : ℝ)^831
        have hw : |(-2107483227/5000000000 : ℝ)|=(2107483227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3493891499/5000000000 : ℝ)|^1087 ≤ (1564322226971/2500000000000 : ℝ)^831
        have hw : |(3493891499/5000000000 : ℝ)|=(3493891499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s3_10 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (516014961/5000000000 : ℝ)*x 0 + (6987802059/10000000000 : ℝ)*x 1 + (-526867321/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516014961/5000000000 : ℝ)^1087 ≤ (5126816764359/100000000000000 : ℝ)^831 := by
    have hnat : (516014961 : ℕ)^1087*100000000000000^831 ≤ 5126816764359^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516014961 5000000000 5126816764359 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6987802059/10000000000 : ℝ)^1087 ≤ (12514622468823/20000000000000 : ℝ)^831 := by
    have hnat : (6987802059 : ℕ)^1087*20000000000000^831 ≤ 12514622468823^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6987802059 10000000000 12514622468823 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526867321/1250000000 : ℝ)^1087 ≤ (8075017717799/25000000000000 : ℝ)^831 := by
    have hnat : (526867321 : ℕ)^1087*25000000000000^831 ≤ 8075017717799^831*1250000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526867321 1250000000 8075017717799 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(516014961/5000000000 : ℝ), (6987802059/10000000000 : ℝ), (-526867321/1250000000 : ℝ)] ![(5126816764359/100000000000000 : ℝ), (12514622468823/20000000000000 : ℝ), (8075017717799/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(516014961/5000000000 : ℝ)|^1087 ≤ (5126816764359/100000000000000 : ℝ)^831
        have hw : |(516014961/5000000000 : ℝ)|=(516014961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6987802059/10000000000 : ℝ)|^1087 ≤ (12514622468823/20000000000000 : ℝ)^831
        have hw : |(6987802059/10000000000 : ℝ)|=(6987802059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-526867321/1250000000 : ℝ)|^1087 ≤ (8075017717799/25000000000000 : ℝ)^831
        have hw : |(-526867321/1250000000 : ℝ)|=(526867321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s3_11 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (971270677/10000000000 : ℝ)*x 0 + (1165819859/2000000000 : ℝ)*x 1 + (2757065691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (971270677/10000000000 : ℝ)^1087 ≤ (947125896089/20000000000000 : ℝ)^831 := by
    have hnat : (971270677 : ℕ)^1087*20000000000000^831 ≤ 947125896089^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971270677 10000000000 947125896089 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1165819859/2000000000 : ℝ)^1087 ≤ (24680959406569/50000000000000 : ℝ)^831 := by
    have hnat : (1165819859 : ℕ)^1087*50000000000000^831 ≤ 24680959406569^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165819859 2000000000 24680959406569 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2757065691/5000000000 : ℝ)^1087 ≤ (918049033791/2000000000000 : ℝ)^831 := by
    have hnat : (2757065691 : ℕ)^1087*2000000000000^831 ≤ 918049033791^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757065691 5000000000 918049033791 2000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(971270677/10000000000 : ℝ), (1165819859/2000000000 : ℝ), (2757065691/5000000000 : ℝ)] ![(947125896089/20000000000000 : ℝ), (24680959406569/50000000000000 : ℝ), (918049033791/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(971270677/10000000000 : ℝ)|^1087 ≤ (947125896089/20000000000000 : ℝ)^831
        have hw : |(971270677/10000000000 : ℝ)|=(971270677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1165819859/2000000000 : ℝ)|^1087 ≤ (24680959406569/50000000000000 : ℝ)^831
        have hw : |(1165819859/2000000000 : ℝ)|=(1165819859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2757065691/5000000000 : ℝ)|^1087 ≤ (918049033791/2000000000000 : ℝ)^831
        have hw : |(2757065691/5000000000 : ℝ)|=(2757065691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1388_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15933/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1103/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14971/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15933/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10137/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15933/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10137/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15933/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10137/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15933/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10137/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15933/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10137/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15933/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10137/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10137/100000 : ℝ) ^ (4347/1024 : ℝ) ≤ (3012583615126217/50000000000000000000 : ℝ) := by
    have hpowers : (10137/100000 : ℝ)^4347 ≤ (3012583615126217/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10137 : ℕ)^4347*50000000000000000000^1024 ≤ 3012583615126217^1024*100000^4347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10137 100000 3012583615126217 50000000000000000000 4347 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10137/100000 : ℝ)) (X := (3012583615126217/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15933/100000 : ℝ) ^ (4347/1024 : ℝ) ≤ (10270690771179847/25000000000000000000 : ℝ) := by
    have hpowers : (15933/100000 : ℝ)^4347 ≤ (10270690771179847/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15933 : ℕ)^4347*25000000000000000000^1024 ≤ 10270690771179847^1024*100000^4347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15933 100000 10270690771179847 25000000000000000000 4347 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15933/100000 : ℝ)) (X := (10270690771179847/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003012583615126217/25000000000000000000 : ℝ) ≤ (5000141925168933/5000000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (25003012583615126217/25000000000000000000 : ℝ)^1024 ≤ (5000141925168933/5000000000000000 : ℝ)^4347 := by
      have hnat : (25003012583615126217 : ℕ)^1024*5000000000000000^4347 ≤ 5000141925168933^4347*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003012583615126217 25000000000000000000 5000141925168933 5000000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000141925168933/5000000000000000 : ℝ)) (X := (25003012583615126217/25000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023553965157485911/50000000000000000000 : ℝ) ≤ (2000221899413253/2000000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (50023553965157485911/50000000000000000000 : ℝ)^1024 ≤ (2000221899413253/2000000000000000 : ℝ)^4347 := by
      have hnat : (50023553965157485911 : ℕ)^1024*2000000000000000^4347 ≤ 2000221899413253^4347*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023553965157485911 50000000000000000000 2000221899413253 2000000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000221899413253/2000000000000000 : ℝ)) (X := (50023553965157485911/50000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12510270690771179847/12500000000000000000 : ℝ) ≤ (1250241892974333/1250000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (12510270690771179847/12500000000000000000 : ℝ)^1024 ≤ (1250241892974333/1250000000000000 : ℝ)^4347 := by
      have hnat : (12510270690771179847 : ℕ)^1024*1250000000000000^4347 ≤ 1250241892974333^4347*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12510270690771179847 12500000000000000000 1250241892974333 1250000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250241892974333/1250000000000000 : ℝ)) (X := (12510270690771179847/12500000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3012583615126217/50000000000000000000 : ℝ) ≤ ((643832289275407889/644000000000000000 : ℝ)+2*(275215576133/193200000000000 : ℝ)*(10137/100000 : ℝ))^(4347/1024 : ℝ) := by
    rw [show (643832289275407889/644000000000000000 : ℝ)+2*(275215576133/193200000000000 : ℝ)*(10137/100000 : ℝ)=(5000141925168933/5000000000000000 : ℝ) by norm_num, show 1+2*(3012583615126217/50000000000000000000 : ℝ)=(25003012583615126217/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10270690771179847/25000000000000000000 : ℝ)+(3012583615126217/50000000000000000000 : ℝ) ≤ ((643832289275407889/644000000000000000 : ℝ)+(275215576133/193200000000000 : ℝ)*((15933/100000 : ℝ)+(10137/100000 : ℝ)))^(4347/1024 : ℝ) := by
    rw [show (643832289275407889/644000000000000000 : ℝ)+(275215576133/193200000000000 : ℝ)*((15933/100000 : ℝ)+(10137/100000 : ℝ))=(2000221899413253/2000000000000000 : ℝ) by norm_num, show 1+(10270690771179847/25000000000000000000 : ℝ)+(3012583615126217/50000000000000000000 : ℝ)=(50023553965157485911/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10270690771179847/25000000000000000000 : ℝ) ≤ ((643832289275407889/644000000000000000 : ℝ)+2*(275215576133/193200000000000 : ℝ)*(15933/100000 : ℝ))^(4347/1024 : ℝ) := by
    rw [show (643832289275407889/644000000000000000 : ℝ)+2*(275215576133/193200000000000 : ℝ)*(15933/100000 : ℝ)=(1250241892974333/1250000000000000 : ℝ) by norm_num, show 1+2*(10270690771179847/25000000000000000000 : ℝ)=(12510270690771179847/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (643832289275407889/644000000000000000 : ℝ)*(X 1 0+X 2 0)+(275215576133/193200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (10137/100000 : ℝ)) (hi := (15933/100000 : ℝ)) (c := (643832289275407889/644000000000000000 : ℝ)) (alpha := (275215576133/193200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (643832289275407889/644000000000000000 : ℝ)*(X 0 1+X 2 1)+(275215576133/193200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (10137/100000 : ℝ)) (hi := (15933/100000 : ℝ)) (c := (643832289275407889/644000000000000000 : ℝ)) (alpha := (275215576133/193200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (643832289275407889/644000000000000000 : ℝ)*(X 0 2+X 1 2)+(275215576133/193200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (10137/100000 : ℝ)) (hi := (15933/100000 : ℝ)) (c := (643832289275407889/644000000000000000 : ℝ)) (alpha := (275215576133/193200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2003545631/10000000000 : ℝ)*X 0 0+(2710824781/5000000000 : ℝ)*X 0 1+(130887037/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351060517/10000000000 : ℝ)*X 1 0+(-2098588423/10000000000 : ℝ)*X 1 1+(5235481651/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351060527/10000000000 : ℝ)*X 2 0+(2617740831/5000000000 : ℝ)*X 2 1+(-1049294197/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2156957841/5000000000 : ℝ)*X 0 0+(4119739349/10000000000 : ℝ)*X 0 1+(903287937/2000000000 : ℝ)*X 0 2+(2156957841/5000000000 : ℝ)*X 1 0+(4119739349/10000000000 : ℝ)*X 1 1+(903287937/2000000000 : ℝ)*X 1 2+(2156957841/5000000000 : ℝ)*X 2 0+(4119739349/10000000000 : ℝ)*X 2 1+(903287937/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-200356313/1000000000 : ℝ)*X 0 0+(5236238687/10000000000 : ℝ)*X 0 1+(5420887551/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325715913/2500000000 : ℝ)*X 1 0+(-239147759/1250000000 : ℝ)*X 1 1+(5420888069/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651432243/5000000000 : ℝ)*X 2 0+(2710443769/5000000000 : ℝ)*X 2 1+(-1913181663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4313952759/10000000000 : ℝ)*X 0 0+(4514826663/10000000000 : ℝ)*X 0 1+(412136091/1000000000 : ℝ)*X 0 2+(4313952759/10000000000 : ℝ)*X 1 0+(4514826663/10000000000 : ℝ)*X 1 1+(412136091/1000000000 : ℝ)*X 1 2+(4313952759/10000000000 : ℝ)*X 2 0+(4514826663/10000000000 : ℝ)*X 2 1+(412136091/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-82603731/10000000000 : ℝ)*X 0 0+(285712471/500000000 : ℝ)*X 0 1+(377538657/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((64501329/625000000 : ℝ)*X 1 0+(-2107483227/5000000000 : ℝ)*X 1 1+(3493891499/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((516014961/5000000000 : ℝ)*X 2 0+(6987802059/10000000000 : ℝ)*X 2 1+(-526867321/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((971270677/10000000000 : ℝ)*X 0 0+(1165819859/2000000000 : ℝ)*X 0 1+(2757065691/5000000000 : ℝ)*X 0 2+(971270677/10000000000 : ℝ)*X 1 0+(1165819859/2000000000 : ℝ)*X 1 1+(2757065691/5000000000 : ℝ)*X 1 2+(971270677/10000000000 : ℝ)*X 2 0+(1165819859/2000000000 : ℝ)*X 2 1+(2757065691/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s3_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36047960384928668595878233/2300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (387708917/50000000000000 : ℝ)*(lower2) + (16116997/12500000000000 : ℝ)*(lower4) + (1973071355773369/50000000000000 : ℝ)*(major0) + (1973071355773369/50000000000000 : ℝ)*(major1) + (1973071355773369/50000000000000 : ℝ)*(major2) + (5371486286331027/100000000000000 : ℝ)*(sp0) + (5371491529564413/100000000000000 : ℝ)*(sp1) + (5371496734883861/100000000000000 : ℝ)*(sp2) + (630197026888857/25000000000000 : ℝ)*(sp3) + (679919687/10000000000000 : ℝ)*(sp4) + (3762928823/100000000000000 : ℝ)*(sp5) + (926893981/25000000000000 : ℝ)*(sp8) + (187576323/12500000000000 : ℝ)*(sp9) + (1455499/2500000000000 : ℝ)*(sp10) + (630197026888857/25000000000000 : ℝ)*(f.failure) + (5371496793103821/100000000000000 : ℝ)*(f.sum) + (64449009890627/4830000000000000000000000000 : ℝ)*base65 + (1377569579051294123/96600000000000000000000000000000 : ℝ)*base67 + (1488394867810094123/96600000000000000000000000000000 : ℝ)*base69 + (1238124303519494123/96600000000000000000000000000000 : ℝ)*base71 + (5036732005153/4830000000000000000000000000 : ℝ)*base74 + (1939893698227694123/96600000000000000000000000000000 : ℝ)*base75 + (1965501382471094123/96600000000000000000000000000000 : ℝ)*base77 + (1120582601556494123/96600000000000000000000000000000 : ℝ)*base79 + (15394658795297/4830000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (31570001/2500000000000000000000 : ℝ)*base90 + (31570001/2500000000000000000000 : ℝ)*base92 + (31570001/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3874612785046319085320623/2300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45482653/100000000000000 : ℝ)*(lower4) + (1989302600760083/50000000000000 : ℝ)*(major0) + (1989302600760083/50000000000000 : ℝ)*(major1) + (1989302600760083/50000000000000 : ℝ)*(major2) + (4870005587/50000000000000 : ℝ)*(sp1) + (5619210641/100000000000000 : ℝ)*(sp2) + (1645513369/50000000000000 : ℝ)*(sp3) + (338480228289259/6250000000000 : ℝ)*(sp4) + (2707837762678073/50000000000000 : ℝ)*(sp5) + (5415678528601397/100000000000000 : ℝ)*(sp6) + (158845053930081/6250000000000 : ℝ)*(sp7) + (201592397/12500000000000 : ℝ)*(sp8) + (558777641/50000000000000 : ℝ)*(sp10) + (927611163/100000000000000 : ℝ)*(sp11) + (635381270379799/25000000000000 : ℝ)*(f.failure) + (135392131634183/2500000000000 : ℝ)*(f.sum) + (5038000663373/690000000000000000000000000 : ℝ)*base66 + (88619937259989377/13800000000000000000000000000000 : ℝ)*base68 + (158141465052189377/13800000000000000000000000000000 : ℝ)*base70 + (96612401755610623/13800000000000000000000000000000 : ℝ)*base71 + (1740431203313/690000000000000000000000000 : ℝ)*base74 + (48525556238210623/13800000000000000000000000000000 : ℝ)*base75 + (159508430565789377/13800000000000000000000000000000 : ℝ)*base78 + (62900831968389377/13800000000000000000000000000000 : ℝ)*base80 + (3795643422773/690000000000000000000000000 : ℝ)*base82 + (2685407/2500000000000000000000 : ℝ)*base90 + (2685407/2500000000000000000000 : ℝ)*base92 + (2685407/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1388_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15933/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14971/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1388_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1388_s4_0 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-125292403/625000000 : ℝ)*x 0 + (2706088473/5000000000 : ℝ)*x 1 + (1048841813/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (125292403/625000000 : ℝ)^1087 ≤ (12218863714623/100000000000000 : ℝ)^831 := by
    have hnat : (125292403 : ℕ)^1087*100000000000000^831 ≤ 12218863714623^831*625000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125292403 625000000 12218863714623 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706088473/5000000000 : ℝ)^1087 ≤ (11198861751501/25000000000000 : ℝ)^831 := by
    have hnat : (2706088473 : ℕ)^1087*25000000000000^831 ≤ 11198861751501^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706088473 5000000000 11198861751501 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048841813/2000000000 : ℝ)^1087 ≤ (42985689256933/100000000000000 : ℝ)^831 := by
    have hnat : (1048841813 : ℕ)^1087*100000000000000^831 ≤ 42985689256933^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048841813 2000000000 42985689256933 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-125292403/625000000 : ℝ), (2706088473/5000000000 : ℝ), (1048841813/2000000000 : ℝ)] ![(12218863714623/100000000000000 : ℝ), (11198861751501/25000000000000 : ℝ), (42985689256933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-125292403/625000000 : ℝ)|^1087 ≤ (12218863714623/100000000000000 : ℝ)^831
        have hw : |(-125292403/625000000 : ℝ)|=(125292403/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706088473/5000000000 : ℝ)|^1087 ≤ (11198861751501/25000000000000 : ℝ)^831
        have hw : |(2706088473/5000000000 : ℝ)|=(2706088473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048841813/2000000000 : ℝ)|^1087 ≤ (42985689256933/100000000000000 : ℝ)^831
        have hw : |(1048841813/2000000000 : ℝ)|=(1048841813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s4_1 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348629907/10000000000 : ℝ)*x 0 + (-2090258801/10000000000 : ℝ)*x 1 + (1311051889/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348629907/10000000000 : ℝ)^1087 ≤ (22054349483443/50000000000000 : ℝ)^831 := by
    have hnat : (5348629907 : ℕ)^1087*50000000000000^831 ≤ 22054349483443^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348629907 10000000000 22054349483443 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2090258801/10000000000 : ℝ)^1087 ≤ (3226406986607/25000000000000 : ℝ)^831 := by
    have hnat : (2090258801 : ℕ)^1087*25000000000000^831 ≤ 3226406986607^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090258801 10000000000 3226406986607 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311051889/2500000000 : ℝ)^1087 ≤ (42985673077561/100000000000000 : ℝ)^831 := by
    have hnat : (1311051889 : ℕ)^1087*100000000000000^831 ≤ 42985673077561^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311051889 2500000000 42985673077561 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348629907/10000000000 : ℝ), (-2090258801/10000000000 : ℝ), (1311051889/2500000000 : ℝ)] ![(22054349483443/50000000000000 : ℝ), (3226406986607/25000000000000 : ℝ), (42985673077561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348629907/10000000000 : ℝ)|^1087 ≤ (22054349483443/50000000000000 : ℝ)^831
        have hw : |(5348629907/10000000000 : ℝ)|=(5348629907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2090258801/10000000000 : ℝ)|^1087 ≤ (3226406986607/25000000000000 : ℝ)^831
        have hw : |(-2090258801/10000000000 : ℝ)|=(2090258801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311051889/2500000000 : ℝ)|^1087 ≤ (42985673077561/100000000000000 : ℝ)^831
        have hw : |(1311051889/2500000000 : ℝ)|=(1311051889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s4_2 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348629437/10000000000 : ℝ)*x 0 + (1048841691/2000000000 : ℝ)*x 1 + (-418051647/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348629437/10000000000 : ℝ)^1087 ≤ (8821738779377/20000000000000 : ℝ)^831 := by
    have hnat : (5348629437 : ℕ)^1087*20000000000000^831 ≤ 8821738779377^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348629437 10000000000 8821738779377 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048841691/2000000000 : ℝ)^1087 ≤ (10746420679141/25000000000000 : ℝ)^831 := by
    have hnat : (1048841691 : ℕ)^1087*25000000000000^831 ≤ 10746420679141^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048841691 2000000000 10746420679141 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (418051647/2000000000 : ℝ)^1087 ≤ (12905623375293/100000000000000 : ℝ)^831 := by
    have hnat : (418051647 : ℕ)^1087*100000000000000^831 ≤ 12905623375293^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418051647 2000000000 12905623375293 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348629437/10000000000 : ℝ), (1048841691/2000000000 : ℝ), (-418051647/2000000000 : ℝ)] ![(8821738779377/20000000000000 : ℝ), (10746420679141/25000000000000 : ℝ), (12905623375293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348629437/10000000000 : ℝ)|^1087 ≤ (8821738779377/20000000000000 : ℝ)^831
        have hw : |(5348629437/10000000000 : ℝ)|=(5348629437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048841691/2000000000 : ℝ)|^1087 ≤ (10746420679141/25000000000000 : ℝ)^831
        have hw : |(1048841691/2000000000 : ℝ)|=(1048841691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-418051647/2000000000 : ℝ)|^1087 ≤ (12905623375293/100000000000000 : ℝ)^831
        have hw : |(-418051647/2000000000 : ℝ)|=(418051647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s4_3 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4314606521/10000000000 : ℝ)*x 0 + (4139044791/10000000000 : ℝ)*x 1 + (4496965693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314606521/10000000000 : ℝ)^1087 ≤ (16651380479871/50000000000000 : ℝ)^831 := by
    have hnat : (4314606521 : ℕ)^1087*50000000000000^831 ≤ 16651380479871^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314606521 10000000000 16651380479871 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4139044791/10000000000 : ℝ)^1087 ≤ (31541430969747/100000000000000 : ℝ)^831 := by
    have hnat : (4139044791 : ℕ)^1087*100000000000000^831 ≤ 31541430969747^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4139044791 10000000000 31541430969747 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4496965693/10000000000 : ℝ)^1087 ≤ (35155808057547/100000000000000 : ℝ)^831 := by
    have hnat : (4496965693 : ℕ)^1087*100000000000000^831 ≤ 35155808057547^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496965693 10000000000 35155808057547 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314606521/10000000000 : ℝ), (4139044791/10000000000 : ℝ), (4496965693/10000000000 : ℝ)] ![(16651380479871/50000000000000 : ℝ), (31541430969747/100000000000000 : ℝ), (35155808057547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314606521/10000000000 : ℝ)|^1087 ≤ (16651380479871/50000000000000 : ℝ)^831
        have hw : |(4314606521/10000000000 : ℝ)|=(4314606521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4139044791/10000000000 : ℝ)|^1087 ≤ (31541430969747/100000000000000 : ℝ)^831
        have hw : |(4139044791/10000000000 : ℝ)|=(4139044791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4496965693/10000000000 : ℝ)|^1087 ≤ (35155808057547/100000000000000 : ℝ)^831
        have hw : |(4496965693/10000000000 : ℝ)|=(4496965693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s4_4 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2004691229/10000000000 : ℝ)*x 0 + (5244824953/10000000000 : ℝ)*x 1 + (2705778789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2004691229/10000000000 : ℝ)^1087 ≤ (305474140399/2500000000000 : ℝ)^831 := by
    have hnat : (2004691229 : ℕ)^1087*2500000000000^831 ≤ 305474140399^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004691229 10000000000 305474140399 2500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244824953/10000000000 : ℝ)^1087 ≤ (42992292876057/100000000000000 : ℝ)^831 := by
    have hnat : (5244824953 : ℕ)^1087*100000000000000^831 ≤ 42992292876057^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244824953 10000000000 42992292876057 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705778789/5000000000 : ℝ)^1087 ≤ (5598592687577/12500000000000 : ℝ)^831 := by
    have hnat : (2705778789 : ℕ)^1087*12500000000000^831 ≤ 5598592687577^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705778789 5000000000 5598592687577 12500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2004691229/10000000000 : ℝ), (5244824953/10000000000 : ℝ), (2705778789/5000000000 : ℝ)] ![(305474140399/2500000000000 : ℝ), (42992292876057/100000000000000 : ℝ), (5598592687577/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2004691229/10000000000 : ℝ)|^1087 ≤ (305474140399/2500000000000 : ℝ)^831
        have hw : |(-2004691229/10000000000 : ℝ)|=(2004691229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244824953/10000000000 : ℝ)|^1087 ≤ (42992292876057/100000000000000 : ℝ)^831
        have hw : |(5244824953/10000000000 : ℝ)|=(5244824953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705778789/5000000000 : ℝ)|^1087 ≤ (5598592687577/12500000000000 : ℝ)^831
        have hw : |(2705778789/5000000000 : ℝ)|=(2705778789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s4_5 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305144213/10000000000 : ℝ)*x 0 + (-961454423/5000000000 : ℝ)*x 1 + (5411557653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305144213/10000000000 : ℝ)^1087 ≤ (43640197033577/100000000000000 : ℝ)^831 := by
    have hnat : (5305144213 : ℕ)^1087*100000000000000^831 ≤ 43640197033577^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305144213 10000000000 43640197033577 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (961454423/5000000000 : ℝ)^1087 ≤ (5785530321277/50000000000000 : ℝ)^831 := by
    have hnat : (961454423 : ℕ)^1087*50000000000000^831 ≤ 5785530321277^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961454423 5000000000 5785530321277 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411557653/10000000000 : ℝ)^1087 ≤ (44788742312579/100000000000000 : ℝ)^831 := by
    have hnat : (5411557653 : ℕ)^1087*100000000000000^831 ≤ 44788742312579^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411557653 10000000000 44788742312579 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305144213/10000000000 : ℝ), (-961454423/5000000000 : ℝ), (5411557653/10000000000 : ℝ)] ![(43640197033577/100000000000000 : ℝ), (5785530321277/50000000000000 : ℝ), (44788742312579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305144213/10000000000 : ℝ)|^1087 ≤ (43640197033577/100000000000000 : ℝ)^831
        have hw : |(5305144213/10000000000 : ℝ)|=(5305144213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-961454423/5000000000 : ℝ)|^1087 ≤ (5785530321277/50000000000000 : ℝ)^831
        have hw : |(-961454423/5000000000 : ℝ)|=(961454423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411557653/10000000000 : ℝ)|^1087 ≤ (44788742312579/100000000000000 : ℝ)^831
        have hw : |(5411557653/10000000000 : ℝ)|=(5411557653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s4_6 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1326286041/2500000000 : ℝ)*x 0 + (43292461/80000000 : ℝ)*x 1 + (-38458179/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326286041/2500000000 : ℝ)^1087 ≤ (4364019650633/10000000000000 : ℝ)^831 := by
    have hnat : (1326286041 : ℕ)^1087*10000000000000^831 ≤ 4364019650633^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326286041 2500000000 4364019650633 10000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43292461/80000000 : ℝ)^1087 ≤ (22394371004723/50000000000000 : ℝ)^831 := by
    have hnat : (43292461 : ℕ)^1087*50000000000000^831 ≤ 22394371004723^831*80000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43292461 80000000 22394371004723 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38458179/200000000 : ℝ)^1087 ≤ (11571061461163/100000000000000 : ℝ)^831 := by
    have hnat : (38458179 : ℕ)^1087*100000000000000^831 ≤ 11571061461163^831*200000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38458179 200000000 11571061461163 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326286041/2500000000 : ℝ), (43292461/80000000 : ℝ), (-38458179/200000000 : ℝ)] ![(4364019650633/10000000000000 : ℝ), (22394371004723/50000000000000 : ℝ), (11571061461163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326286041/2500000000 : ℝ)|^1087 ≤ (4364019650633/10000000000000 : ℝ)^831
        have hw : |(1326286041/2500000000 : ℝ)|=(1326286041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43292461/80000000 : ℝ)|^1087 ≤ (22394371004723/50000000000000 : ℝ)^831
        have hw : |(43292461/80000000 : ℝ)|=(43292461/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38458179/200000000 : ℝ)|^1087 ≤ (11571061461163/100000000000000 : ℝ)^831
        have hw : |(-38458179/200000000 : ℝ)|=(38458179/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s4_7 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (539329163/1250000000 : ℝ)*x 0 + (224782609/500000000 : ℝ)*x 1 + (1035091261/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539329163/1250000000 : ℝ)^1087 ≤ (6660606274503/20000000000000 : ℝ)^831 := by
    have hnat : (539329163 : ℕ)^1087*20000000000000^831 ≤ 6660606274503^831*1250000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539329163 1250000000 6660606274503 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224782609/500000000 : ℝ)^1087 ≤ (1405695066819/4000000000000 : ℝ)^831 := by
    have hnat : (224782609 : ℕ)^1087*4000000000000^831 ≤ 1405695066819^831*500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224782609 500000000 1405695066819 4000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035091261/2500000000 : ℝ)^1087 ≤ (631091839029/2000000000000 : ℝ)^831 := by
    have hnat : (1035091261 : ℕ)^1087*2000000000000^831 ≤ 631091839029^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035091261 2500000000 631091839029 2000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539329163/1250000000 : ℝ), (224782609/500000000 : ℝ), (1035091261/2500000000 : ℝ)] ![(6660606274503/20000000000000 : ℝ), (1405695066819/4000000000000 : ℝ), (631091839029/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539329163/1250000000 : ℝ)|^1087 ≤ (6660606274503/20000000000000 : ℝ)^831
        have hw : |(539329163/1250000000 : ℝ)|=(539329163/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224782609/500000000 : ℝ)|^1087 ≤ (1405695066819/4000000000000 : ℝ)^831
        have hw : |(224782609/500000000 : ℝ)|=(224782609/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035091261/2500000000 : ℝ)|^1087 ≤ (631091839029/2000000000000 : ℝ)^831
        have hw : |(1035091261/2500000000 : ℝ)|=(1035091261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1388_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14971/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11217/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14773/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14971/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1103/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14971/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1103/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14971/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1103/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14971/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1103/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14971/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1103/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14971/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1103/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1103/10000 : ℝ) ^ (4347/1024 : ℝ) ≤ (1724450957593481/20000000000000000000 : ℝ) := by
    have hpowers : (1103/10000 : ℝ)^4347 ≤ (1724450957593481/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1103 : ℕ)^4347*20000000000000000000^1024 ≤ 1724450957593481^1024*10000^4347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1103 10000 1724450957593481 20000000000000000000 4347 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1103/10000 : ℝ)) (X := (1724450957593481/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14971/100000 : ℝ) ^ (4347/1024 : ℝ) ≤ (985582676585601/3125000000000000000 : ℝ) := by
    have hpowers : (14971/100000 : ℝ)^4347 ≤ (985582676585601/3125000000000000000 : ℝ)^1024 := by
      have hnat : (14971 : ℕ)^4347*3125000000000000000^1024 ≤ 985582676585601^1024*100000^4347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14971 100000 985582676585601 3125000000000000000 4347 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14971/100000 : ℝ)) (X := (985582676585601/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001724450957593481/10000000000000000000 : ℝ) ≤ (10000406193099441/10000000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (10001724450957593481/10000000000000000000 : ℝ)^1024 ≤ (10000406193099441/10000000000000000 : ℝ)^4347 := by
      have hnat : (10001724450957593481 : ℕ)^1024*10000000000000000^4347 ≤ 10000406193099441^4347*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001724450957593481 10000000000000000000 10000406193099441 10000000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000406193099441/10000000000000000 : ℝ)) (X := (10001724450957593481/10000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040160900438706637/100000000000000000000 : ℝ) ≤ (2000189180818059/2000000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (100040160900438706637/100000000000000000000 : ℝ)^1024 ≤ (2000189180818059/2000000000000000 : ℝ)^4347 := by
      have hnat : (100040160900438706637 : ℕ)^1024*2000000000000000^4347 ≤ 2000189180818059^4347*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040160900438706637 100000000000000000000 2000189180818059 2000000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000189180818059/2000000000000000 : ℝ)) (X := (100040160900438706637/100000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563485582676585601/1562500000000000000 : ℝ) ≤ (10001485615081149/10000000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (1563485582676585601/1562500000000000000 : ℝ)^1024 ≤ (10001485615081149/10000000000000000 : ℝ)^4347 := by
      have hnat : (1563485582676585601 : ℕ)^1024*10000000000000000^4347 ≤ 10001485615081149^4347*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563485582676585601 1562500000000000000 10001485615081149 10000000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001485615081149/10000000000000000 : ℝ)) (X := (1563485582676585601/1562500000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1724450957593481/20000000000000000000 : ℝ) ≤ ((5628527826078093963/5630000000000000000 : ℝ)+2*(38550785061/28150000000000 : ℝ)*(1103/10000 : ℝ))^(4347/1024 : ℝ) := by
    rw [show (5628527826078093963/5630000000000000000 : ℝ)+2*(38550785061/28150000000000 : ℝ)*(1103/10000 : ℝ)=(10000406193099441/10000000000000000 : ℝ) by norm_num, show 1+2*(1724450957593481/20000000000000000000 : ℝ)=(10001724450957593481/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(985582676585601/3125000000000000000 : ℝ)+(1724450957593481/20000000000000000000 : ℝ) ≤ ((5628527826078093963/5630000000000000000 : ℝ)+(38550785061/28150000000000 : ℝ)*((14971/100000 : ℝ)+(1103/10000 : ℝ)))^(4347/1024 : ℝ) := by
    rw [show (5628527826078093963/5630000000000000000 : ℝ)+(38550785061/28150000000000 : ℝ)*((14971/100000 : ℝ)+(1103/10000 : ℝ))=(2000189180818059/2000000000000000 : ℝ) by norm_num, show 1+(985582676585601/3125000000000000000 : ℝ)+(1724450957593481/20000000000000000000 : ℝ)=(100040160900438706637/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(985582676585601/3125000000000000000 : ℝ) ≤ ((5628527826078093963/5630000000000000000 : ℝ)+2*(38550785061/28150000000000 : ℝ)*(14971/100000 : ℝ))^(4347/1024 : ℝ) := by
    rw [show (5628527826078093963/5630000000000000000 : ℝ)+2*(38550785061/28150000000000 : ℝ)*(14971/100000 : ℝ)=(10001485615081149/10000000000000000 : ℝ) by norm_num, show 1+2*(985582676585601/3125000000000000000 : ℝ)=(1563485582676585601/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5628527826078093963/5630000000000000000 : ℝ)*(X 1 0+X 2 0)+(38550785061/28150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (1103/10000 : ℝ)) (hi := (14971/100000 : ℝ)) (c := (5628527826078093963/5630000000000000000 : ℝ)) (alpha := (38550785061/28150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5628527826078093963/5630000000000000000 : ℝ)*(X 0 1+X 2 1)+(38550785061/28150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (1103/10000 : ℝ)) (hi := (14971/100000 : ℝ)) (c := (5628527826078093963/5630000000000000000 : ℝ)) (alpha := (38550785061/28150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5628527826078093963/5630000000000000000 : ℝ)*(X 0 2+X 1 2)+(38550785061/28150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (1103/10000 : ℝ)) (hi := (14971/100000 : ℝ)) (c := (5628527826078093963/5630000000000000000 : ℝ)) (alpha := (38550785061/28150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-125292403/625000000 : ℝ)*X 0 0+(2706088473/5000000000 : ℝ)*X 0 1+(1048841813/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348629907/10000000000 : ℝ)*X 1 0+(-2090258801/10000000000 : ℝ)*X 1 1+(1311051889/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348629437/10000000000 : ℝ)*X 2 0+(1048841691/2000000000 : ℝ)*X 2 1+(-418051647/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4314606521/10000000000 : ℝ)*X 0 0+(4139044791/10000000000 : ℝ)*X 0 1+(4496965693/10000000000 : ℝ)*X 0 2+(4314606521/10000000000 : ℝ)*X 1 0+(4139044791/10000000000 : ℝ)*X 1 1+(4496965693/10000000000 : ℝ)*X 1 2+(4314606521/10000000000 : ℝ)*X 2 0+(4139044791/10000000000 : ℝ)*X 2 1+(4496965693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2004691229/10000000000 : ℝ)*X 0 0+(5244824953/10000000000 : ℝ)*X 0 1+(2705778789/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305144213/10000000000 : ℝ)*X 1 0+(-961454423/5000000000 : ℝ)*X 1 1+(5411557653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326286041/2500000000 : ℝ)*X 2 0+(43292461/80000000 : ℝ)*X 2 1+(-38458179/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((539329163/1250000000 : ℝ)*X 0 0+(224782609/500000000 : ℝ)*X 0 1+(1035091261/2500000000 : ℝ)*X 0 2+(539329163/1250000000 : ℝ)*X 1 0+(224782609/500000000 : ℝ)*X 1 1+(1035091261/2500000000 : ℝ)*X 1 2+(539329163/1250000000 : ℝ)*X 2 0+(224782609/500000000 : ℝ)*X 2 1+(1035091261/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (99141647373043459664377353/17593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (765017841/100000000000000 : ℝ)*(base19) + (18371537/20000000000000 : ℝ)*(base23) + (65954101/50000000000000 : ℝ)*(lower2) + (33120637/100000000000000 : ℝ)*(upper5) + (546715182065927/12500000000000 : ℝ)*(major0) + (546715182065927/12500000000000 : ℝ)*(major1) + (546715182065927/12500000000000 : ℝ)*(major2) + (5953518166659511/100000000000000 : ℝ)*(sp0) + (93023210297933/1562500000000 : ℝ)*(sp1) + (11627925811083/195312500000 : ℝ)*(sp2) + (698479863404807/25000000000000 : ℝ)*(sp3) + (15971286979/50000000000000 : ℝ)*(sp5) + (2005952733/10000000000000 : ℝ)*(sp6) + (638117639/12500000000000 : ℝ)*(sp7) + (2793924558560339/100000000000000 : ℝ)*(f.failure) + (5953518166659511/100000000000000 : ℝ)*(f.sum) + (3651859747817/703750000000000000000000000 : ℝ)*base66 + (182104595996651299/70375000000000000000000000000000 : ℝ)*base68 + (797836740644026299/70375000000000000000000000000000 : ℝ)*base70 + (644197314981651299/70375000000000000000000000000000 : ℝ)*base72 + (292328176087/43984375000000000000000000 : ℝ)*base74 + (1119082093775651299/70375000000000000000000000000000 : ℝ)*base76 + (780687729749401299/70375000000000000000000000000000 : ℝ)*base78 + (74016664251848701/70375000000000000000000000000000 : ℝ)*base79 + (386998894683/175937500000000000000000000 : ℝ)*base82 + (18338373/10000000000000000000000 : ℝ)*base89 + (18338373/10000000000000000000000 : ℝ)*base91 + (18338373/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32868913630389477097428723/14075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11907347/3125000000000 : ℝ)*(base19) + (161039153/50000000000000 : ℝ)*(base23) + (16615989/100000000000000 : ℝ)*(upper2) + (55603187/100000000000000 : ℝ)*(upper3) + (81927637/100000000000000 : ℝ)*(upper5) + (220306262200493/5000000000000 : ℝ)*(major0) + (220306262200493/5000000000000 : ℝ)*(major1) + (220306262200493/5000000000000 : ℝ)*(major2) + (2453162187/25000000000000 : ℝ)*(sp1) + (2778634001/50000000000000 : ℝ)*(sp2) + (1499406594171917/25000000000000 : ℝ)*(sp4) + (5997616183003817/100000000000000 : ℝ)*(sp5) + (74970256216767/1250000000000 : ℝ)*(sp6) + (140731201674487/5000000000000 : ℝ)*(sp7) + (140731201674487/5000000000000 : ℝ)*(f.failure) + (1499406594171917/25000000000000 : ℝ)*(f.sum) + (66338722817/28150000000000000000000000 : ℝ)*base65 + (226825238180923759/28150000000000000000000000000000 : ℝ)*base67 + (257292437521923759/28150000000000000000000000000000 : ℝ)*base69 + (50082247325026241/28150000000000000000000000000000 : ℝ)*base72 + (1785249211387/281500000000000000000000000 : ℝ)*base73 + (236305112549173759/28150000000000000000000000000000 : ℝ)*base75 + (26487774689576241/28150000000000000000000000000000 : ℝ)*base78 + (139237996517023759/28150000000000000000000000000000 : ℝ)*base79 + (167175044957/281500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4649409/500000000000000000000 : ℝ)*base89 + (4649409/500000000000000000000 : ℝ)*base91 + (4649409/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1388_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14971/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11217/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1388_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1388_s5_0 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2004858549/10000000000 : ℝ)*x 0 + (2705294903/5000000000 : ℝ)*x 1 + (2622838817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2004858549/10000000000 : ℝ)^1087 ≤ (2444059931229/20000000000000 : ℝ)^831 := by
    have hnat : (2004858549 : ℕ)^1087*20000000000000^831 ≤ 2444059931229^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004858549 10000000000 2444059931229 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705294903/5000000000 : ℝ)^1087 ≤ (22389132259459/50000000000000 : ℝ)^831 := by
    have hnat : (2705294903 : ℕ)^1087*50000000000000^831 ≤ 22389132259459^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705294903 5000000000 22389132259459 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622838817/5000000000 : ℝ)^1087 ≤ (43001435810181/100000000000000 : ℝ)^831 := by
    have hnat : (2622838817 : ℕ)^1087*100000000000000^831 ≤ 43001435810181^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622838817 5000000000 43001435810181 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2004858549/10000000000 : ℝ), (2705294903/5000000000 : ℝ), (2622838817/5000000000 : ℝ)] ![(2444059931229/20000000000000 : ℝ), (22389132259459/50000000000000 : ℝ), (43001435810181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2004858549/10000000000 : ℝ)|^1087 ≤ (2444059931229/20000000000000 : ℝ)^831
        have hw : |(-2004858549/10000000000 : ℝ)|=(2004858549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705294903/5000000000 : ℝ)|^1087 ≤ (22389132259459/50000000000000 : ℝ)^831
        have hw : |(2705294903/5000000000 : ℝ)|=(2705294903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622838817/5000000000 : ℝ)|^1087 ≤ (43001435810181/100000000000000 : ℝ)^831
        have hw : |(2622838817/5000000000 : ℝ)|=(2622838817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s5_1 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1337055429/2500000000 : ℝ)*x 0 + (-261106493/1250000000 : ℝ)*x 1 + (5245677761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337055429/2500000000 : ℝ)^1087 ≤ (8820859153119/20000000000000 : ℝ)^831 := by
    have hnat : (1337055429 : ℕ)^1087*20000000000000^831 ≤ 8820859153119^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337055429 2500000000 8820859153119 20000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261106493/1250000000 : ℝ)^1087 ≤ (12894267052031/100000000000000 : ℝ)^831 := by
    have hnat : (261106493 : ℕ)^1087*100000000000000^831 ≤ 12894267052031^831*1250000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261106493 1250000000 12894267052031 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245677761/10000000000 : ℝ)^1087 ≤ (21500718585991/50000000000000 : ℝ)^831 := by
    have hnat : (5245677761 : ℕ)^1087*50000000000000^831 ≤ 21500718585991^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245677761 10000000000 21500718585991 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337055429/2500000000 : ℝ), (-261106493/1250000000 : ℝ), (5245677761/10000000000 : ℝ)] ![(8820859153119/20000000000000 : ℝ), (12894267052031/100000000000000 : ℝ), (21500718585991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337055429/2500000000 : ℝ)|^1087 ≤ (8820859153119/20000000000000 : ℝ)^831
        have hw : |(1337055429/2500000000 : ℝ)|=(1337055429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-261106493/1250000000 : ℝ)|^1087 ≤ (12894267052031/100000000000000 : ℝ)^831
        have hw : |(-261106493/1250000000 : ℝ)|=(261106493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245677761/10000000000 : ℝ)|^1087 ≤ (21500718585991/50000000000000 : ℝ)^831
        have hw : |(5245677761/10000000000 : ℝ)|=(5245677761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s5_2 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (534822177/1000000000 : ℝ)*x 0 + (1311419417/2500000000 : ℝ)*x 1 + (-417770399/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534822177/1000000000 : ℝ)^1087 ≤ (11026074087023/25000000000000 : ℝ)^831 := by
    have hnat : (534822177 : ℕ)^1087*25000000000000^831 ≤ 11026074087023^831*1000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534822177 1000000000 11026074087023 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311419417/2500000000 : ℝ)^1087 ≤ (43001436174757/100000000000000 : ℝ)^831 := by
    have hnat : (1311419417 : ℕ)^1087*100000000000000^831 ≤ 43001436174757^831*2500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311419417 2500000000 43001436174757 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (417770399/2000000000 : ℝ)^1087 ≤ (12894267463833/100000000000000 : ℝ)^831 := by
    have hnat : (417770399 : ℕ)^1087*100000000000000^831 ≤ 12894267463833^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417770399 2000000000 12894267463833 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534822177/1000000000 : ℝ), (1311419417/2500000000 : ℝ), (-417770399/2000000000 : ℝ)] ![(11026074087023/25000000000000 : ℝ), (43001436174757/100000000000000 : ℝ), (12894267463833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534822177/1000000000 : ℝ)|^1087 ≤ (11026074087023/25000000000000 : ℝ)^831
        have hw : |(534822177/1000000000 : ℝ)|=(534822177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311419417/2500000000 : ℝ)|^1087 ≤ (43001436174757/100000000000000 : ℝ)^831
        have hw : |(1311419417/2500000000 : ℝ)|=(1311419417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-417770399/2000000000 : ℝ)|^1087 ≤ (12894267463833/100000000000000 : ℝ)^831
        have hw : |(-417770399/2000000000 : ℝ)|=(417770399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s5_3 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4314715849/10000000000 : ℝ)*x 0 + (828457587/2000000000 : ℝ)*x 1 + (4493695671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314715849/10000000000 : ℝ)^1087 ≤ (16651932392927/50000000000000 : ℝ)^831 := by
    have hnat : (4314715849 : ℕ)^1087*50000000000000^831 ≤ 16651932392927^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314715849 10000000000 16651932392927 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (828457587/2000000000 : ℝ)^1087 ≤ (31573762660917/100000000000000 : ℝ)^831 := by
    have hnat : (828457587 : ℕ)^1087*100000000000000^831 ≤ 31573762660917^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828457587 2000000000 31573762660917 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493695671/10000000000 : ℝ)^1087 ≤ (35122372539943/100000000000000 : ℝ)^831 := by
    have hnat : (4493695671 : ℕ)^1087*100000000000000^831 ≤ 35122372539943^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493695671 10000000000 35122372539943 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314715849/10000000000 : ℝ), (828457587/2000000000 : ℝ), (4493695671/10000000000 : ℝ)] ![(16651932392927/50000000000000 : ℝ), (31573762660917/100000000000000 : ℝ), (35122372539943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314715849/10000000000 : ℝ)|^1087 ≤ (16651932392927/50000000000000 : ℝ)^831
        have hw : |(4314715849/10000000000 : ℝ)|=(4314715849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(828457587/2000000000 : ℝ)|^1087 ≤ (31573762660917/100000000000000 : ℝ)^831
        have hw : |(828457587/2000000000 : ℝ)|=(828457587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493695671/10000000000 : ℝ)|^1087 ≤ (35122372539943/100000000000000 : ℝ)^831
        have hw : |(4493695671/10000000000 : ℝ)|=(4493695671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s5_4 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-200487037/1000000000 : ℝ)*x 0 + (5246272093/10000000000 : ℝ)*x 1 + (2704996131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (200487037/1000000000 : ℝ)^1087 ≤ (12220393906121/100000000000000 : ℝ)^831 := by
    have hnat : (200487037 : ℕ)^1087*100000000000000^831 ≤ 12220393906121^831*1000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200487037 1000000000 12220393906121 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246272093/10000000000 : ℝ)^1087 ≤ (43007810210969/100000000000000 : ℝ)^831 := by
    have hnat : (5246272093 : ℕ)^1087*100000000000000^831 ≤ 43007810210969^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246272093 10000000000 43007810210969 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704996131/5000000000 : ℝ)^1087 ≤ (22385897934337/50000000000000 : ℝ)^831 := by
    have hnat : (2704996131 : ℕ)^1087*50000000000000^831 ≤ 22385897934337^831*5000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704996131 5000000000 22385897934337 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-200487037/1000000000 : ℝ), (5246272093/10000000000 : ℝ), (2704996131/5000000000 : ℝ)] ![(12220393906121/100000000000000 : ℝ), (43007810210969/100000000000000 : ℝ), (22385897934337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-200487037/1000000000 : ℝ)|^1087 ≤ (12220393906121/100000000000000 : ℝ)^831
        have hw : |(-200487037/1000000000 : ℝ)|=(200487037/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246272093/10000000000 : ℝ)|^1087 ≤ (43007810210969/100000000000000 : ℝ)^831
        have hw : |(5246272093/10000000000 : ℝ)|=(5246272093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704996131/5000000000 : ℝ)|^1087 ≤ (22385897934337/50000000000000 : ℝ)^831
        have hw : |(2704996131/5000000000 : ℝ)|=(2704996131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s5_5 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (530552771/1000000000 : ℝ)*x 0 + (-192453739/1000000000 : ℝ)*x 1 + (169062257/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530552771/1000000000 : ℝ)^1087 ≤ (43644323561949/100000000000000 : ℝ)^831 := by
    have hnat : (530552771 : ℕ)^1087*100000000000000^831 ≤ 43644323561949^831*1000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530552771 1000000000 43644323561949 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192453739/1000000000 : ℝ)^1087 ≤ (11583880970339/100000000000000 : ℝ)^831 := by
    have hnat : (192453739 : ℕ)^1087*100000000000000^831 ≤ 11583880970339^831*1000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192453739 1000000000 11583880970339 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169062257/312500000 : ℝ)^1087 ≤ (11192948864329/25000000000000 : ℝ)^831 := by
    have hnat : (169062257 : ℕ)^1087*25000000000000^831 ≤ 11192948864329^831*312500000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169062257 312500000 11192948864329 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530552771/1000000000 : ℝ), (-192453739/1000000000 : ℝ), (169062257/312500000 : ℝ)] ![(43644323561949/100000000000000 : ℝ), (11583880970339/100000000000000 : ℝ), (11192948864329/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530552771/1000000000 : ℝ)|^1087 ≤ (43644323561949/100000000000000 : ℝ)^831
        have hw : |(530552771/1000000000 : ℝ)|=(530552771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-192453739/1000000000 : ℝ)|^1087 ≤ (11583880970339/100000000000000 : ℝ)^831
        have hw : |(-192453739/1000000000 : ℝ)|=(192453739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169062257/312500000 : ℝ)|^1087 ≤ (11192948864329/25000000000000 : ℝ)^831
        have hw : |(169062257/312500000 : ℝ)|=(169062257/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s5_6 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1061105543/2000000000 : ℝ)*x 0 + (5409992197/10000000000 : ℝ)*x 1 + (-96226871/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061105543/2000000000 : ℝ)^1087 ≤ (43644323615751/100000000000000 : ℝ)^831 := by
    have hnat : (1061105543 : ℕ)^1087*100000000000000^831 ≤ 43644323615751^831*2000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061105543 2000000000 43644323615751 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409992197/10000000000 : ℝ)^1087 ≤ (11192948791259/25000000000000 : ℝ)^831 := by
    have hnat : (5409992197 : ℕ)^1087*25000000000000^831 ≤ 11192948791259^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409992197 10000000000 11192948791259 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96226871/500000000 : ℝ)^1087 ≤ (11583881206537/100000000000000 : ℝ)^831 := by
    have hnat : (96226871 : ℕ)^1087*100000000000000^831 ≤ 11583881206537^831*500000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96226871 500000000 11583881206537 100000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061105543/2000000000 : ℝ), (5409992197/10000000000 : ℝ), (-96226871/500000000 : ℝ)] ![(43644323615751/100000000000000 : ℝ), (11192948791259/25000000000000 : ℝ), (11583881206537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061105543/2000000000 : ℝ)|^1087 ≤ (43644323615751/100000000000000 : ℝ)^831
        have hw : |(1061105543/2000000000 : ℝ)|=(1061105543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409992197/10000000000 : ℝ)|^1087 ≤ (11192948791259/25000000000000 : ℝ)^831
        have hw : |(5409992197/10000000000 : ℝ)|=(5409992197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-96226871/500000000 : ℝ)|^1087 ≤ (11583881206537/100000000000000 : ℝ)^831
        have hw : |(-96226871/500000000 : ℝ)|=(96226871/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1388_s5_7 (p : ℝ) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4314741041/10000000000 : ℝ)*x 0 + (4492429043/10000000000 : ℝ)*x 1 + (4143561111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314741041/10000000000 : ℝ)^1087 ≤ (8326029784293/25000000000000 : ℝ)^831 := by
    have hnat : (4314741041 : ℕ)^1087*25000000000000^831 ≤ 8326029784293^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314741041 10000000000 8326029784293 25000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492429043/10000000000 : ℝ)^1087 ≤ (4388677932413/12500000000000 : ℝ)^831 := by
    have hnat : (4492429043 : ℕ)^1087*12500000000000^831 ≤ 4388677932413^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492429043 10000000000 4388677932413 12500000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4143561111/10000000000 : ℝ)^1087 ≤ (15793228697071/50000000000000 : ℝ)^831 := by
    have hnat : (4143561111 : ℕ)^1087*50000000000000^831 ≤ 15793228697071^831*10000000000^1087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143561111 10000000000 15793228697071 50000000000000 1087 831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1087/256 : ℝ)) 1087 831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314741041/10000000000 : ℝ), (4492429043/10000000000 : ℝ), (4143561111/10000000000 : ℝ)] ![(8326029784293/25000000000000 : ℝ), (4388677932413/12500000000000 : ℝ), (15793228697071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314741041/10000000000 : ℝ)|^1087 ≤ (8326029784293/25000000000000 : ℝ)^831
        have hw : |(4314741041/10000000000 : ℝ)|=(4314741041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492429043/10000000000 : ℝ)|^1087 ≤ (4388677932413/12500000000000 : ℝ)^831
        have hw : |(4492429043/10000000000 : ℝ)|=(4492429043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4143561111/10000000000 : ℝ)|^1087 ≤ (15793228697071/50000000000000 : ℝ)^831
        have hw : |(4143561111/10000000000 : ℝ)|=(4143561111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1388_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11217/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (703/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (737/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11217/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11217/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11217/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11217/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11217/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11217/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11217/100000 : ℝ) ^ (4347/1024 : ℝ) ≤ (4630046339314857/50000000000000000000 : ℝ) := by
    have hpowers : (11217/100000 : ℝ)^4347 ≤ (4630046339314857/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11217 : ℕ)^4347*50000000000000000000^1024 ≤ 4630046339314857^1024*100000^4347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11217 100000 4630046339314857 50000000000000000000 4347 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11217/100000 : ℝ)) (X := (4630046339314857/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14773/100000 : ℝ) ^ (4347/1024 : ℝ) ≤ (5961112115710839/20000000000000000000 : ℝ) := by
    have hpowers : (14773/100000 : ℝ)^4347 ≤ (5961112115710839/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14773 : ℕ)^4347*20000000000000000000^1024 ≤ 5961112115710839^1024*100000^4347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14773 100000 5961112115710839 20000000000000000000 4347 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14773/100000 : ℝ)) (X := (5961112115710839/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004630046339314857/25000000000000000000 : ℝ) ≤ (10000436239417809/10000000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (25004630046339314857/25000000000000000000 : ℝ)^1024 ≤ (10000436239417809/10000000000000000 : ℝ)^4347 := by
      have hnat : (25004630046339314857 : ℕ)^1024*10000000000000000^4347 ≤ 10000436239417809^4347*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004630046339314857 25000000000000000000 10000436239417809 10000000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000436239417809/10000000000000000 : ℝ)) (X := (25004630046339314857/25000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039065653257183909/100000000000000000000 : ℝ) ≤ (5000460055868333/5000000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (100039065653257183909/100000000000000000000 : ℝ)^1024 ≤ (5000460055868333/5000000000000000 : ℝ)^4347 := by
      have hnat : (100039065653257183909 : ℕ)^1024*5000000000000000^4347 ≤ 5000460055868333^4347*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039065653257183909 100000000000000000000 5000460055868333 5000000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000460055868333/5000000000000000 : ℝ)) (X := (100039065653257183909/100000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005961112115710839/10000000000000000000 : ℝ) ≤ (10001403984055523/10000000000000000 : ℝ) ^ (4347/1024 : ℝ) := by
    have hpowers : (10005961112115710839/10000000000000000000 : ℝ)^1024 ≤ (10001403984055523/10000000000000000 : ℝ)^4347 := by
      have hnat : (10005961112115710839 : ℕ)^1024*10000000000000000^4347 ≤ 10001403984055523^4347*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005961112115710839 10000000000000000000 10001403984055523 10000000000000000 1024 4347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001403984055523/10000000000000000 : ℝ)) (X := (10005961112115710839/10000000000000000000 : ℝ)) (by norm_num) 4347 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4630046339314857/50000000000000000000 : ℝ) ≤ ((17775348037884245433/17780000000000000000 : ℝ)+2*(483872318857/355600000000000 : ℝ)*(11217/100000 : ℝ))^(4347/1024 : ℝ) := by
    rw [show (17775348037884245433/17780000000000000000 : ℝ)+2*(483872318857/355600000000000 : ℝ)*(11217/100000 : ℝ)=(10000436239417809/10000000000000000 : ℝ) by norm_num, show 1+2*(4630046339314857/50000000000000000000 : ℝ)=(25004630046339314857/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5961112115710839/20000000000000000000 : ℝ)+(4630046339314857/50000000000000000000 : ℝ) ≤ ((17775348037884245433/17780000000000000000 : ℝ)+(483872318857/355600000000000 : ℝ)*((14773/100000 : ℝ)+(11217/100000 : ℝ)))^(4347/1024 : ℝ) := by
    rw [show (17775348037884245433/17780000000000000000 : ℝ)+(483872318857/355600000000000 : ℝ)*((14773/100000 : ℝ)+(11217/100000 : ℝ))=(5000460055868333/5000000000000000 : ℝ) by norm_num, show 1+(5961112115710839/20000000000000000000 : ℝ)+(4630046339314857/50000000000000000000 : ℝ)=(100039065653257183909/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5961112115710839/20000000000000000000 : ℝ) ≤ ((17775348037884245433/17780000000000000000 : ℝ)+2*(483872318857/355600000000000 : ℝ)*(14773/100000 : ℝ))^(4347/1024 : ℝ) := by
    rw [show (17775348037884245433/17780000000000000000 : ℝ)+2*(483872318857/355600000000000 : ℝ)*(14773/100000 : ℝ)=(10001403984055523/10000000000000000 : ℝ) by norm_num, show 1+2*(5961112115710839/20000000000000000000 : ℝ)=(10005961112115710839/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17775348037884245433/17780000000000000000 : ℝ)*(X 1 0+X 2 0)+(483872318857/355600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (11217/100000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (17775348037884245433/17780000000000000000 : ℝ)) (alpha := (483872318857/355600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17775348037884245433/17780000000000000000 : ℝ)*(X 0 1+X 2 1)+(483872318857/355600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (11217/100000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (17775348037884245433/17780000000000000000 : ℝ)) (alpha := (483872318857/355600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17775348037884245433/17780000000000000000 : ℝ)*(X 0 2+X 1 2)+(483872318857/355600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4347/1024 : ℝ)) (lo := (11217/100000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (17775348037884245433/17780000000000000000 : ℝ)) (alpha := (483872318857/355600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2004858549/10000000000 : ℝ)*X 0 0+(2705294903/5000000000 : ℝ)*X 0 1+(2622838817/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337055429/2500000000 : ℝ)*X 1 0+(-261106493/1250000000 : ℝ)*X 1 1+(5245677761/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534822177/1000000000 : ℝ)*X 2 0+(1311419417/2500000000 : ℝ)*X 2 1+(-417770399/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4314715849/10000000000 : ℝ)*X 0 0+(828457587/2000000000 : ℝ)*X 0 1+(4493695671/10000000000 : ℝ)*X 0 2+(4314715849/10000000000 : ℝ)*X 1 0+(828457587/2000000000 : ℝ)*X 1 1+(4493695671/10000000000 : ℝ)*X 1 2+(4314715849/10000000000 : ℝ)*X 2 0+(828457587/2000000000 : ℝ)*X 2 1+(4493695671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-200487037/1000000000 : ℝ)*X 0 0+(5246272093/10000000000 : ℝ)*X 0 1+(2704996131/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530552771/1000000000 : ℝ)*X 1 0+(-192453739/1000000000 : ℝ)*X 1 1+(169062257/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061105543/2000000000 : ℝ)*X 2 0+(5409992197/10000000000 : ℝ)*X 2 1+(-96226871/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4314741041/10000000000 : ℝ)*X 0 0+(4492429043/10000000000 : ℝ)*X 0 1+(4143561111/10000000000 : ℝ)*X 0 2+(4314741041/10000000000 : ℝ)*X 1 0+(4492429043/10000000000 : ℝ)*X 1 1+(4143561111/10000000000 : ℝ)*X 1 2+(4314741041/10000000000 : ℝ)*X 2 0+(4492429043/10000000000 : ℝ)*X 2 1+(4143561111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1388_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3529262967636122137159772181/444500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (717724169/50000000000000 : ℝ)*(base19) + (274603839/20000000000000 : ℝ)*(base23) + (13226709/20000000000000 : ℝ)*(lower2) + (23924583/10000000000000 : ℝ)*(upper3) + (95367367/100000000000000 : ℝ)*(upper5) + (4454813235592519/100000000000000 : ℝ)*(major0) + (4454813235592519/100000000000000 : ℝ)*(major1) + (4454813235592519/100000000000000 : ℝ)*(major2) + (3031934360351663/50000000000000 : ℝ)*(sp0) + (37899368409361/625000000000 : ℝ)*(sp1) + (757987375990863/12500000000000 : ℝ)*(sp2) + (1422855009641433/50000000000000 : ℝ)*(sp3) + (7915060693/25000000000000 : ℝ)*(sp4) + (1975786803/12500000000000 : ℝ)*(sp7) + (2845725825577289/100000000000000 : ℝ)*(f.failure) + (6063900380946099/100000000000000 : ℝ)*(f.sum) + (91527964460337/17780000000000000000000000000 : ℝ)*base66 + (17419605897818134273/1778000000000000000000000000000000 : ℝ)*base68 + (10874120443730134273/1778000000000000000000000000000000 : ℝ)*base70 + (13286503162770134273/1778000000000000000000000000000000 : ℝ)*base72 + (124485568054777/17780000000000000000000000000 : ℝ)*base74 + (4775347651733865727/1778000000000000000000000000000000 : ℝ)*base75 + (13428999052530134273/1778000000000000000000000000000000 : ℝ)*base78 + (28327143960778134273/1778000000000000000000000000000000 : ℝ)*base80 + (156306650401817/17780000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (8257023/10000000000000000000000 : ℝ)*base89 + (8257023/10000000000000000000000 : ℝ)*base91 + (8257023/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (503976447560724648614509137/127000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6662791/800000000000 : ℝ)*(base19) + (227706397/25000000000000 : ℝ)*(base23) + (18502103/25000000000000 : ℝ)*(upper3) + (2531663/6250000000000 : ℝ)*(lower4) + (53604289/50000000000000 : ℝ)*(upper5) + (4487198411471447/100000000000000 : ℝ)*(major0) + (4487198411471447/100000000000000 : ℝ)*(major1) + (4487198411471447/100000000000000 : ℝ)*(major2) + (17348414021/100000000000000 : ℝ)*(sp1) + (4208870027/25000000000000 : ℝ)*(sp2) + (3053991639607093/50000000000000 : ℝ)*(sp4) + (6107965097951291/100000000000000 : ℝ)*(sp5) + (6107965532908491/100000000000000 : ℝ)*(sp6) + (1433206705725709/50000000000000 : ℝ)*(sp7) + (1433206705725709/50000000000000 : ℝ)*(f.failure) + (3053991639607093/50000000000000 : ℝ)*(f.sum) + (990017494577/2540000000000000000000000000 : ℝ)*base65 + (1882670105141771207/254000000000000000000000000000000 : ℝ)*base68 + (959326729073771207/254000000000000000000000000000000 : ℝ)*base70 + (252867805189771207/254000000000000000000000000000000 : ℝ)*base72 + (1577828505897/2540000000000000000000000000 : ℝ)*base73 + (837513265055771207/254000000000000000000000000000000 : ℝ)*base76 + (675784302255771207/254000000000000000000000000000000 : ℝ)*base78 + (3060559944683771207/254000000000000000000000000000000 : ℝ)*base80 + (837714181423/2540000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (20224037/5000000000000000000000 : ℝ)*base90 + (20224037/5000000000000000000000 : ℝ)*base92 + (20224037/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1388_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11217/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (703/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (737/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1388_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1388_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15933/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (703/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (737/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1388_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1388_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1388_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4347/1024 : ℝ) ≤ p) (hpb : p ≤ (1087/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156544007/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15933/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (703/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (737/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1388_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
