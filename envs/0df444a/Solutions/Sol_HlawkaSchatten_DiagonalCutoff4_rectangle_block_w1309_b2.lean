-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1309_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:38:45.939404+00:00
-- url     : https://prove2.me/submissions/e2b281c8-e131-4208-acce-15f9b3a7c8bc

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
theorem support_rectangle_w1309_s6_0 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-20728207/100000000 : ℝ)*x 0 + (1353608261/2500000000 : ℝ)*x 1 + (5243516697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20728207/100000000 : ℝ)^4269 ≤ (12615205107389/100000000000000 : ℝ)^3245 := by
    have hnat : (20728207 : ℕ)^4269*100000000000000^3245 ≤ 12615205107389^3245*100000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20728207 100000000 12615205107389 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353608261/2500000000 : ℝ)^4269 ≤ (22307059830891/50000000000000 : ℝ)^3245 := by
    have hnat : (1353608261 : ℕ)^4269*50000000000000^3245 ≤ 22307059830891^3245*2500000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353608261 2500000000 22307059830891 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243516697/10000000000 : ℝ)^4269 ≤ (42770675211747/100000000000000 : ℝ)^3245 := by
    have hnat : (5243516697 : ℕ)^4269*100000000000000^3245 ≤ 42770675211747^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243516697 10000000000 42770675211747 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-20728207/100000000 : ℝ), (1353608261/2500000000 : ℝ), (5243516697/10000000000 : ℝ)] ![(12615205107389/100000000000000 : ℝ), (22307059830891/50000000000000 : ℝ), (42770675211747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-20728207/100000000 : ℝ)|^4269 ≤ (12615205107389/100000000000000 : ℝ)^3245
        have hw : |(-20728207/100000000 : ℝ)|=(20728207/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353608261/2500000000 : ℝ)|^4269 ≤ (22307059830891/50000000000000 : ℝ)^3245
        have hw : |(1353608261/2500000000 : ℝ)|=(1353608261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243516697/10000000000 : ℝ)|^4269 ≤ (42770675211747/100000000000000 : ℝ)^3245
        have hw : |(5243516697/10000000000 : ℝ)|=(5243516697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s6_1 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349547123/10000000000 : ℝ)*x 0 + (-2159931609/10000000000 : ℝ)*x 1 + (2621758139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349547123/10000000000 : ℝ)^4269 ≤ (43912087430441/100000000000000 : ℝ)^3245 := by
    have hnat : (5349547123 : ℕ)^4269*100000000000000^3245 ≤ 43912087430441^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349547123 10000000000 43912087430441 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2159931609/10000000000 : ℝ)^4269 ≤ (3329310461053/25000000000000 : ℝ)^3245 := by
    have hnat : (2159931609 : ℕ)^4269*25000000000000^3245 ≤ 3329310461053^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159931609 10000000000 3329310461053 25000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621758139/5000000000 : ℝ)^4269 ≤ (42770670715513/100000000000000 : ℝ)^3245 := by
    have hnat : (2621758139 : ℕ)^4269*100000000000000^3245 ≤ 42770670715513^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621758139 5000000000 42770670715513 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349547123/10000000000 : ℝ), (-2159931609/10000000000 : ℝ), (2621758139/5000000000 : ℝ)] ![(43912087430441/100000000000000 : ℝ), (3329310461053/25000000000000 : ℝ), (42770670715513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349547123/10000000000 : ℝ)|^4269 ≤ (43912087430441/100000000000000 : ℝ)^3245
        have hw : |(5349547123/10000000000 : ℝ)|=(5349547123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2159931609/10000000000 : ℝ)|^4269 ≤ (3329310461053/25000000000000 : ℝ)^3245
        have hw : |(-2159931609/10000000000 : ℝ)|=(2159931609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621758139/5000000000 : ℝ)|^4269 ≤ (42770670715513/100000000000000 : ℝ)^3245
        have hw : |(2621758139/5000000000 : ℝ)|=(2621758139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s6_2 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337386621/2500000000 : ℝ)*x 0 + (2621758281/5000000000 : ℝ)*x 1 + (-2159932083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337386621/2500000000 : ℝ)^4269 ≤ (1097802013249/2500000000000 : ℝ)^3245 := by
    have hnat : (1337386621 : ℕ)^4269*2500000000000^3245 ≤ 1097802013249^3245*2500000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337386621 2500000000 1097802013249 2500000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621758281/5000000000 : ℝ)^4269 ≤ (1069266844077/2500000000000 : ℝ)^3245 := by
    have hnat : (2621758281 : ℕ)^4269*2500000000000^3245 ≤ 1069266844077^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621758281 5000000000 1069266844077 2500000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2159932083/10000000000 : ℝ)^4269 ≤ (13317245688927/100000000000000 : ℝ)^3245 := by
    have hnat : (2159932083 : ℕ)^4269*100000000000000^3245 ≤ 13317245688927^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159932083 10000000000 13317245688927 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337386621/2500000000 : ℝ), (2621758281/5000000000 : ℝ), (-2159932083/10000000000 : ℝ)] ![(1097802013249/2500000000000 : ℝ), (1069266844077/2500000000000 : ℝ), (13317245688927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337386621/2500000000 : ℝ)|^4269 ≤ (1097802013249/2500000000000 : ℝ)^3245
        have hw : |(1337386621/2500000000 : ℝ)|=(1337386621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621758281/5000000000 : ℝ)|^4269 ≤ (1069266844077/2500000000000 : ℝ)^3245
        have hw : |(2621758281/5000000000 : ℝ)|=(2621758281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2159932083/10000000000 : ℝ)|^4269 ≤ (13317245688927/100000000000000 : ℝ)^3245
        have hw : |(-2159932083/10000000000 : ℝ)|=(2159932083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s6_3 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (135478729/312500000 : ℝ)*x 0 + (4161959739/10000000000 : ℝ)*x 1 + (4515517397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135478729/312500000 : ℝ)^4269 ≤ (16651317413861/50000000000000 : ℝ)^3245 := by
    have hnat : (135478729 : ℕ)^4269*50000000000000^3245 ≤ 16651317413861^3245*312500000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135478729 312500000 16651317413861 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4161959739/10000000000 : ℝ)^4269 ≤ (15780930286581/50000000000000 : ℝ)^3245 := by
    have hnat : (4161959739 : ℕ)^4269*50000000000000^3245 ≤ 15780930286581^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161959739 10000000000 15780930286581 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4515517397/10000000000 : ℝ)^4269 ≤ (35135504579941/100000000000000 : ℝ)^3245 := by
    have hnat : (4515517397 : ℕ)^4269*100000000000000^3245 ≤ 35135504579941^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515517397 10000000000 35135504579941 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135478729/312500000 : ℝ), (4161959739/10000000000 : ℝ), (4515517397/10000000000 : ℝ)] ![(16651317413861/50000000000000 : ℝ), (15780930286581/50000000000000 : ℝ), (35135504579941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135478729/312500000 : ℝ)|^4269 ≤ (16651317413861/50000000000000 : ℝ)^3245
        have hw : |(135478729/312500000 : ℝ)|=(135478729/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4161959739/10000000000 : ℝ)|^4269 ≤ (15780930286581/50000000000000 : ℝ)^3245
        have hw : |(4161959739/10000000000 : ℝ)|=(4161959739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4515517397/10000000000 : ℝ)|^4269 ≤ (35135504579941/100000000000000 : ℝ)^3245
        have hw : |(4515517397/10000000000 : ℝ)|=(4515517397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s6_4 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2072833589/10000000000 : ℝ)*x 0 + (5244127003/10000000000 : ℝ)*x 1 + (5413819343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2072833589/10000000000 : ℝ)^4269 ≤ (12615308303583/100000000000000 : ℝ)^3245 := by
    have hnat : (2072833589 : ℕ)^4269*100000000000000^3245 ≤ 12615308303583^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072833589 10000000000 12615308303583 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244127003/10000000000 : ℝ)^4269 ≤ (5347153055741/12500000000000 : ℝ)^3245 := by
    have hnat : (5244127003 : ℕ)^4269*12500000000000^3245 ≤ 5347153055741^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244127003 10000000000 5347153055741 12500000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413819343/10000000000 : ℝ)^4269 ≤ (44607467238761/100000000000000 : ℝ)^3245 := by
    have hnat : (5413819343 : ℕ)^4269*100000000000000^3245 ≤ 44607467238761^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413819343 10000000000 44607467238761 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2072833589/10000000000 : ℝ), (5244127003/10000000000 : ℝ), (5413819343/10000000000 : ℝ)] ![(12615308303583/100000000000000 : ℝ), (5347153055741/12500000000000 : ℝ), (44607467238761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2072833589/10000000000 : ℝ)|^4269 ≤ (12615308303583/100000000000000 : ℝ)^3245
        have hw : |(-2072833589/10000000000 : ℝ)|=(2072833589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244127003/10000000000 : ℝ)|^4269 ≤ (5347153055741/12500000000000 : ℝ)^3245
        have hw : |(5244127003/10000000000 : ℝ)|=(5244127003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413819343/10000000000 : ℝ)|^4269 ≤ (44607467238761/100000000000000 : ℝ)^3245
        have hw : |(5413819343/10000000000 : ℝ)|=(5413819343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s6_5 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652847537/5000000000 : ℝ)*x 0 + (-1989629391/10000000000 : ℝ)*x 1 + (1353454731/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652847537/5000000000 : ℝ)^4269 ≤ (5429893533227/12500000000000 : ℝ)^3245 := by
    have hnat : (2652847537 : ℕ)^4269*12500000000000^3245 ≤ 5429893533227^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652847537 5000000000 5429893533227 12500000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989629391/10000000000 : ℝ)^4269 ≤ (2390677804213/20000000000000 : ℝ)^3245 := by
    have hnat : (1989629391 : ℕ)^4269*20000000000000^3245 ≤ 2390677804213^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989629391 10000000000 2390677804213 20000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353454731/2500000000 : ℝ)^4269 ≤ (44607462696947/100000000000000 : ℝ)^3245 := by
    have hnat : (1353454731 : ℕ)^4269*100000000000000^3245 ≤ 44607462696947^3245*2500000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353454731 2500000000 44607462696947 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652847537/5000000000 : ℝ), (-1989629391/10000000000 : ℝ), (1353454731/2500000000 : ℝ)] ![(5429893533227/12500000000000 : ℝ), (2390677804213/20000000000000 : ℝ), (44607462696947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652847537/5000000000 : ℝ)|^4269 ≤ (5429893533227/12500000000000 : ℝ)^3245
        have hw : |(2652847537/5000000000 : ℝ)|=(2652847537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1989629391/10000000000 : ℝ)|^4269 ≤ (2390677804213/20000000000000 : ℝ)^3245
        have hw : |(-1989629391/10000000000 : ℝ)|=(1989629391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353454731/2500000000 : ℝ)|^4269 ≤ (44607462696947/100000000000000 : ℝ)^3245
        have hw : |(1353454731/2500000000 : ℝ)|=(1353454731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s6_6 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305694379/10000000000 : ℝ)*x 0 + (5413819727/10000000000 : ℝ)*x 1 + (-1989629237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305694379/10000000000 : ℝ)^4269 ≤ (43439140780067/100000000000000 : ℝ)^3245 := by
    have hnat : (5305694379 : ℕ)^4269*100000000000000^3245 ≤ 43439140780067^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305694379 10000000000 43439140780067 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413819727/10000000000 : ℝ)^4269 ≤ (22303735700593/50000000000000 : ℝ)^3245 := by
    have hnat : (5413819727 : ℕ)^4269*50000000000000^3245 ≤ 22303735700593^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413819727 10000000000 22303735700593 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1989629237/10000000000 : ℝ)^4269 ≤ (1494173475487/12500000000000 : ℝ)^3245 := by
    have hnat : (1989629237 : ℕ)^4269*12500000000000^3245 ≤ 1494173475487^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989629237 10000000000 1494173475487 12500000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305694379/10000000000 : ℝ), (5413819727/10000000000 : ℝ), (-1989629237/10000000000 : ℝ)] ![(43439140780067/100000000000000 : ℝ), (22303735700593/50000000000000 : ℝ), (1494173475487/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305694379/10000000000 : ℝ)|^4269 ≤ (43439140780067/100000000000000 : ℝ)^3245
        have hw : |(5305694379/10000000000 : ℝ)|=(5305694379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413819727/10000000000 : ℝ)|^4269 ≤ (22303735700593/50000000000000 : ℝ)^3245
        have hw : |(5413819727/10000000000 : ℝ)|=(5413819727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1989629237/10000000000 : ℝ)|^4269 ≤ (1494173475487/12500000000000 : ℝ)^3245
        have hw : |(-1989629237/10000000000 : ℝ)|=(1989629237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s6_7 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4335345119/10000000000 : ℝ)*x 0 + (2257127377/5000000000 : ℝ)*x 1 + (4163229047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4335345119/10000000000 : ℝ)^4269 ≤ (33302895465609/100000000000000 : ℝ)^3245 := by
    have hnat : (4335345119 : ℕ)^4269*100000000000000^3245 ≤ 33302895465609^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335345119 10000000000 33302895465609 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257127377/5000000000 : ℝ)^4269 ≤ (4390322518211/12500000000000 : ℝ)^3245 := by
    have hnat : (2257127377 : ℕ)^4269*12500000000000^3245 ≤ 4390322518211^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257127377 5000000000 4390322518211 12500000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4163229047/10000000000 : ℝ)^4269 ≤ (31574524374513/100000000000000 : ℝ)^3245 := by
    have hnat : (4163229047 : ℕ)^4269*100000000000000^3245 ≤ 31574524374513^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163229047 10000000000 31574524374513 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4335345119/10000000000 : ℝ), (2257127377/5000000000 : ℝ), (4163229047/10000000000 : ℝ)] ![(33302895465609/100000000000000 : ℝ), (4390322518211/12500000000000 : ℝ), (31574524374513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4335345119/10000000000 : ℝ)|^4269 ≤ (33302895465609/100000000000000 : ℝ)^3245
        have hw : |(4335345119/10000000000 : ℝ)|=(4335345119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2257127377/5000000000 : ℝ)|^4269 ≤ (4390322518211/12500000000000 : ℝ)^3245
        have hw : |(2257127377/5000000000 : ℝ)|=(2257127377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4163229047/10000000000 : ℝ)|^4269 ≤ (31574524374513/100000000000000 : ℝ)^3245
        have hw : |(4163229047/10000000000 : ℝ)|=(4163229047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1309_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30685957/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11059/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11069/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7343/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1837/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11059/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1837/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11059/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1837/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11059/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1837/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11059/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1837/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11059/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1837/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11059/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11059/100000 : ℝ) ^ (1067/256 : ℝ) ≤ (516663265609317/5000000000000000000 : ℝ) := by
    have hpowers : (11059/100000 : ℝ)^1067 ≤ (516663265609317/5000000000000000000 : ℝ)^256 := by
      have hnat : (11059 : ℕ)^1067*5000000000000000000^256 ≤ 516663265609317^256*100000^1067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11059 100000 516663265609317 5000000000000000000 1067 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11059/100000 : ℝ)) (X := (516663265609317/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1837/12500 : ℝ) ^ (1067/256 : ℝ) ≤ (16899819208522773/50000000000000000000 : ℝ) := by
    have hpowers : (1837/12500 : ℝ)^1067 ≤ (16899819208522773/50000000000000000000 : ℝ)^256 := by
      have hnat : (1837 : ℕ)^1067*50000000000000000000^256 ≤ 16899819208522773^256*12500^1067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1837 12500 16899819208522773 50000000000000000000 1067 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1837/12500 : ℝ)) (X := (16899819208522773/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500516663265609317/2500000000000000000 : ℝ) ≤ (625030987677841/625000000000000 : ℝ) ^ (1067/256 : ℝ) := by
    have hpowers : (2500516663265609317/2500000000000000000 : ℝ)^256 ≤ (625030987677841/625000000000000 : ℝ)^1067 := by
      have hnat : (2500516663265609317 : ℕ)^256*625000000000000^1067 ≤ 625030987677841^1067*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500516663265609317 2500000000000000000 625030987677841 625000000000000 256 1067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625030987677841/625000000000000 : ℝ)) (X := (2500516663265609317/2500000000000000000 : ℝ)) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022066451864615943/50000000000000000000 : ℝ) ≤ (2500264670312157/2500000000000000 : ℝ) ^ (1067/256 : ℝ) := by
    have hpowers : (50022066451864615943/50000000000000000000 : ℝ)^256 ≤ (2500264670312157/2500000000000000 : ℝ)^1067 := by
      have hnat : (50022066451864615943 : ℕ)^256*2500000000000000^1067 ≤ 2500264670312157^1067*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022066451864615943 50000000000000000000 2500264670312157 2500000000000000 256 1067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500264670312157/2500000000000000 : ℝ)) (X := (50022066451864615943/50000000000000000000 : ℝ)) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016899819208522773/25000000000000000000 : ℝ) ≤ (50008107798259/50000000000000 : ℝ) ^ (1067/256 : ℝ) := by
    have hpowers : (25016899819208522773/25000000000000000000 : ℝ)^256 ≤ (50008107798259/50000000000000 : ℝ)^1067 := by
      have hnat : (25016899819208522773 : ℕ)^256*50000000000000^1067 ≤ 50008107798259^1067*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016899819208522773 25000000000000000000 50008107798259 50000000000000 256 1067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50008107798259/50000000000000 : ℝ)) (X := (25016899819208522773/25000000000000000000 : ℝ)) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(516663265609317/5000000000000000000 : ℝ) ≤ ((4544919186303445647/4546250000000000000 : ℝ)+2*(140719600793/90925000000000 : ℝ)*(11059/100000 : ℝ))^(1067/256 : ℝ) := by
    rw [show (4544919186303445647/4546250000000000000 : ℝ)+2*(140719600793/90925000000000 : ℝ)*(11059/100000 : ℝ)=(625030987677841/625000000000000 : ℝ) by norm_num, show 1+2*(516663265609317/5000000000000000000 : ℝ)=(2500516663265609317/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16899819208522773/50000000000000000000 : ℝ)+(516663265609317/5000000000000000000 : ℝ) ≤ ((4544919186303445647/4546250000000000000 : ℝ)+(140719600793/90925000000000 : ℝ)*((1837/12500 : ℝ)+(11059/100000 : ℝ)))^(1067/256 : ℝ) := by
    rw [show (4544919186303445647/4546250000000000000 : ℝ)+(140719600793/90925000000000 : ℝ)*((1837/12500 : ℝ)+(11059/100000 : ℝ))=(2500264670312157/2500000000000000 : ℝ) by norm_num, show 1+(16899819208522773/50000000000000000000 : ℝ)+(516663265609317/5000000000000000000 : ℝ)=(50022066451864615943/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16899819208522773/50000000000000000000 : ℝ) ≤ ((4544919186303445647/4546250000000000000 : ℝ)+2*(140719600793/90925000000000 : ℝ)*(1837/12500 : ℝ))^(1067/256 : ℝ) := by
    rw [show (4544919186303445647/4546250000000000000 : ℝ)+2*(140719600793/90925000000000 : ℝ)*(1837/12500 : ℝ)=(50008107798259/50000000000000 : ℝ) by norm_num, show 1+2*(16899819208522773/50000000000000000000 : ℝ)=(25016899819208522773/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4544919186303445647/4546250000000000000 : ℝ)*(X 1 0+X 2 0)+(140719600793/90925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1067/256 : ℝ)) (lo := (11059/100000 : ℝ)) (hi := (1837/12500 : ℝ)) (c := (4544919186303445647/4546250000000000000 : ℝ)) (alpha := (140719600793/90925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4544919186303445647/4546250000000000000 : ℝ)*(X 0 1+X 2 1)+(140719600793/90925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1067/256 : ℝ)) (lo := (11059/100000 : ℝ)) (hi := (1837/12500 : ℝ)) (c := (4544919186303445647/4546250000000000000 : ℝ)) (alpha := (140719600793/90925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4544919186303445647/4546250000000000000 : ℝ)*(X 0 2+X 1 2)+(140719600793/90925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1067/256 : ℝ)) (lo := (11059/100000 : ℝ)) (hi := (1837/12500 : ℝ)) (c := (4544919186303445647/4546250000000000000 : ℝ)) (alpha := (140719600793/90925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-20728207/100000000 : ℝ)*X 0 0+(1353608261/2500000000 : ℝ)*X 0 1+(5243516697/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349547123/10000000000 : ℝ)*X 1 0+(-2159931609/10000000000 : ℝ)*X 1 1+(2621758139/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337386621/2500000000 : ℝ)*X 2 0+(2621758281/5000000000 : ℝ)*X 2 1+(-2159932083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((135478729/312500000 : ℝ)*X 0 0+(4161959739/10000000000 : ℝ)*X 0 1+(4515517397/10000000000 : ℝ)*X 0 2+(135478729/312500000 : ℝ)*X 1 0+(4161959739/10000000000 : ℝ)*X 1 1+(4515517397/10000000000 : ℝ)*X 1 2+(135478729/312500000 : ℝ)*X 2 0+(4161959739/10000000000 : ℝ)*X 2 1+(4515517397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2072833589/10000000000 : ℝ)*X 0 0+(5244127003/10000000000 : ℝ)*X 0 1+(5413819343/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652847537/5000000000 : ℝ)*X 1 0+(-1989629391/10000000000 : ℝ)*X 1 1+(1353454731/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305694379/10000000000 : ℝ)*X 2 0+(5413819727/10000000000 : ℝ)*X 2 1+(-1989629237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4335345119/10000000000 : ℝ)*X 0 0+(2257127377/5000000000 : ℝ)*X 0 1+(4163229047/10000000000 : ℝ)*X 0 2+(4335345119/10000000000 : ℝ)*X 1 0+(2257127377/5000000000 : ℝ)*X 1 1+(4163229047/10000000000 : ℝ)*X 1 2+(4335345119/10000000000 : ℝ)*X 2 0+(2257127377/5000000000 : ℝ)*X 2 1+(4163229047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (579524936474078076884618487/227312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (309149753/50000000000000 : ℝ)*(base19) + (17167103/25000000000000 : ℝ)*(base23) + (125172677/100000000000000 : ℝ)*(lower4) + (86043433/50000000000000 : ℝ)*(lower5) + (4339622841760469/100000000000000 : ℝ)*(major0) + (4339622841760469/100000000000000 : ℝ)*(major1) + (4339622841760469/100000000000000 : ℝ)*(major2) + (2925416538351571/50000000000000 : ℝ)*(sp0) + (5850835332294831/100000000000000 : ℝ)*(sp1) + (2925412772225031/50000000000000 : ℝ)*(sp2) + (2828401966950909/100000000000000 : ℝ)*(sp3) + (574778239/20000000000000 : ℝ)*(sp4) + (5168737931/50000000000000 : ℝ)*(sp6) + (7680993569/100000000000000 : ℝ)*(sp7) + (1414204823972239/50000000000000 : ℝ)*(f.failure) + (5850835950594337/100000000000000 : ℝ)*(f.sum) + (7411255012797/4546250000000000000000000000 : ℝ)*base65 + (2861155499590671557/454625000000000000000000000000000 : ℝ)*base68 + (1643177329341296557/454625000000000000000000000000000 : ℝ)*base70 + (2614402082570921557/454625000000000000000000000000000 : ℝ)*base72 + (2679511827269/9092500000000000000000000000 : ℝ)*base73 + (500255607126671557/454625000000000000000000000000000 : ℝ)*base76 + (1152073716701046557/454625000000000000000000000000000 : ℝ)*base78 + (2112839878633796557/454625000000000000000000000000000 : ℝ)*base80 + (3938258399277/4546250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (5147723/1000000000000000000000 : ℝ)*base89 + (5147723/1000000000000000000000 : ℝ)*base91 + (5147723/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (154304011554262974866344947/22731250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (90521479/10000000000000 : ℝ)*(base19) + (390249683/100000000000000 : ℝ)*(base23) + (11618817/12500000000000 : ℝ)*(upper2) + (146928713/100000000000000 : ℝ)*(upper3) + (437090030978967/10000000000000 : ℝ)*(major0) + (437090030978967/10000000000000 : ℝ)*(major1) + (437090030978967/10000000000000 : ℝ)*(major2) + (25016947/2000000000000 : ℝ)*(sp1) + (2786282279/25000000000000 : ℝ)*(sp2) + (477360539/50000000000000 : ℝ)*(sp3) + (5893005219807529/100000000000000 : ℝ)*(sp4) + (5893003063745389/100000000000000 : ℝ)*(sp5) + (589299368442873/10000000000000 : ℝ)*(sp6) + (2848794218777777/100000000000000 : ℝ)*(sp7) + (569759034699771/20000000000000 : ℝ)*(f.failure) + (5893005219807529/100000000000000 : ℝ)*(f.sum) + (1765007641903/1818500000000000000000000000 : ℝ)*base65 + (295623328003980851/45462500000000000000000000000000 : ℝ)*base68 + (59656124832293351/45462500000000000000000000000000 : ℝ)*base70 + (450810380804630851/45462500000000000000000000000000 : ℝ)*base72 + (3064411761/3637000000000000000000000000 : ℝ)*base73 + (471858760808455851/45462500000000000000000000000000 : ℝ)*base76 + (99342743783044149/45462500000000000000000000000000 : ℝ)*base77 + (9776911550331649/45462500000000000000000000000000 : ℝ)*base79 + (4909346148109/3637000000000000000000000000 : ℝ)*base81 + (815847/400000000000000000000 : ℝ)*base89 + (815847/400000000000000000000 : ℝ)*base91 + (815847/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1309_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30685957/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11059/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11069/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1309_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1309_s7_0 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-129551877/625000000 : ℝ)*x 0 + (5414347673/10000000000 : ℝ)*x 1 + (2621797987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129551877/625000000 : ℝ)^4269 ≤ (1576909978041/12500000000000 : ℝ)^3245 := by
    have hnat : (129551877 : ℕ)^4269*12500000000000^3245 ≤ 1576909978041^3245*625000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129551877 625000000 1576909978041 12500000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414347673/10000000000 : ℝ)^4269 ≤ (44613194239223/100000000000000 : ℝ)^3245 := by
    have hnat : (5414347673 : ℕ)^4269*100000000000000^3245 ≤ 44613194239223^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414347673 10000000000 44613194239223 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621797987/5000000000 : ℝ)^4269 ≤ (42771525924901/100000000000000 : ℝ)^3245 := by
    have hnat : (2621797987 : ℕ)^4269*100000000000000^3245 ≤ 42771525924901^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621797987 5000000000 42771525924901 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-129551877/625000000 : ℝ), (5414347673/10000000000 : ℝ), (2621797987/5000000000 : ℝ)] ![(1576909978041/12500000000000 : ℝ), (44613194239223/100000000000000 : ℝ), (42771525924901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-129551877/625000000 : ℝ)|^4269 ≤ (1576909978041/12500000000000 : ℝ)^3245
        have hw : |(-129551877/625000000 : ℝ)|=(129551877/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414347673/10000000000 : ℝ)|^4269 ≤ (44613194239223/100000000000000 : ℝ)^3245
        have hw : |(5414347673/10000000000 : ℝ)|=(5414347673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621797987/5000000000 : ℝ)|^4269 ≤ (42771525924901/100000000000000 : ℝ)^3245
        have hw : |(2621797987/5000000000 : ℝ)|=(2621797987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s7_1 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674761967/5000000000 : ℝ)*x 0 + (-2159852467/10000000000 : ℝ)*x 1 + (2621799717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674761967/5000000000 : ℝ)^4269 ≤ (43911837015497/100000000000000 : ℝ)^3245 := by
    have hnat : (2674761967 : ℕ)^4269*100000000000000^3245 ≤ 43911837015497^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674761967 5000000000 43911837015497 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2159852467/10000000000 : ℝ)^4269 ≤ (6658299955201/50000000000000 : ℝ)^3245 := by
    have hnat : (2159852467 : ℕ)^4269*50000000000000^3245 ≤ 6658299955201^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159852467 10000000000 6658299955201 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621799717/5000000000 : ℝ)^4269 ≤ (4277156305389/10000000000000 : ℝ)^3245 := by
    have hnat : (2621799717 : ℕ)^4269*10000000000000^3245 ≤ 4277156305389^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621799717 5000000000 4277156305389 10000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674761967/5000000000 : ℝ), (-2159852467/10000000000 : ℝ), (2621799717/5000000000 : ℝ)] ![(43911837015497/100000000000000 : ℝ), (6658299955201/50000000000000 : ℝ), (4277156305389/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674761967/5000000000 : ℝ)|^4269 ≤ (43911837015497/100000000000000 : ℝ)^3245
        have hw : |(2674761967/5000000000 : ℝ)|=(2674761967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2159852467/10000000000 : ℝ)|^4269 ≤ (6658299955201/50000000000000 : ℝ)^3245
        have hw : |(-2159852467/10000000000 : ℝ)|=(2159852467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621799717/5000000000 : ℝ)|^4269 ≤ (4277156305389/10000000000000 : ℝ)^3245
        have hw : |(2621799717/5000000000 : ℝ)|=(2621799717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s7_2 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534952577/1000000000 : ℝ)*x 0 + (1048719243/2000000000 : ℝ)*x 1 + (-1079927141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534952577/1000000000 : ℝ)^4269 ≤ (21955928421103/50000000000000 : ℝ)^3245 := by
    have hnat : (534952577 : ℕ)^4269*50000000000000^3245 ≤ 21955928421103^3245*1000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534952577 1000000000 21955928421103 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048719243/2000000000 : ℝ)^4269 ≤ (42771528511053/100000000000000 : ℝ)^3245 := by
    have hnat : (1048719243 : ℕ)^4269*100000000000000^3245 ≤ 42771528511053^3245*2000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048719243 2000000000 42771528511053 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079927141/5000000000 : ℝ)^4269 ≤ (13316614632083/100000000000000 : ℝ)^3245 := by
    have hnat : (1079927141 : ℕ)^4269*100000000000000^3245 ≤ 13316614632083^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079927141 5000000000 13316614632083 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534952577/1000000000 : ℝ), (1048719243/2000000000 : ℝ), (-1079927141/5000000000 : ℝ)] ![(21955928421103/50000000000000 : ℝ), (42771528511053/100000000000000 : ℝ), (13316614632083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534952577/1000000000 : ℝ)|^4269 ≤ (21955928421103/50000000000000 : ℝ)^3245
        have hw : |(534952577/1000000000 : ℝ)|=(534952577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048719243/2000000000 : ℝ)|^4269 ≤ (42771528511053/100000000000000 : ℝ)^3245
        have hw : |(1048719243/2000000000 : ℝ)|=(1048719243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1079927141/5000000000 : ℝ)|^4269 ≤ (13316614632083/100000000000000 : ℝ)^3245
        have hw : |(-1079927141/5000000000 : ℝ)|=(1079927141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s7_3 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4335323743/10000000000 : ℝ)*x 0 + (1040534061/2500000000 : ℝ)*x 1 + (903068203/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4335323743/10000000000 : ℝ)^4269 ≤ (33302679444657/100000000000000 : ℝ)^3245 := by
    have hnat : (4335323743 : ℕ)^4269*100000000000000^3245 ≤ 33302679444657^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335323743 10000000000 33302679444657 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040534061/2500000000 : ℝ)^4269 ≤ (15781810739421/50000000000000 : ℝ)^3245 := by
    have hnat : (1040534061 : ℕ)^4269*50000000000000^3245 ≤ 15781810739421^3245*2500000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040534061 2500000000 15781810739421 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903068203/2000000000 : ℝ)^4269 ≤ (8783424765597/25000000000000 : ℝ)^3245 := by
    have hnat : (903068203 : ℕ)^4269*25000000000000^3245 ≤ 8783424765597^3245*2000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903068203 2000000000 8783424765597 25000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4335323743/10000000000 : ℝ), (1040534061/2500000000 : ℝ), (903068203/2000000000 : ℝ)] ![(33302679444657/100000000000000 : ℝ), (15781810739421/50000000000000 : ℝ), (8783424765597/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4335323743/10000000000 : ℝ)|^4269 ≤ (33302679444657/100000000000000 : ℝ)^3245
        have hw : |(4335323743/10000000000 : ℝ)|=(4335323743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1040534061/2500000000 : ℝ)|^4269 ≤ (15781810739421/50000000000000 : ℝ)^3245
        have hw : |(1040534061/2500000000 : ℝ)|=(1040534061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(903068203/2000000000 : ℝ)|^4269 ≤ (8783424765597/25000000000000 : ℝ)^3245
        have hw : |(903068203/2000000000 : ℝ)|=(903068203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s7_4 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1036421009/5000000000 : ℝ)*x 0 + (5244207369/10000000000 : ℝ)*x 1 + (2706866777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036421009/5000000000 : ℝ)^4269 ≤ (12615375790753/100000000000000 : ℝ)^3245 := by
    have hnat : (1036421009 : ℕ)^4269*100000000000000^3245 ≤ 12615375790753^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036421009 5000000000 12615375790753 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244207369/10000000000 : ℝ)^4269 ≤ (5347260859591/12500000000000 : ℝ)^3245 := by
    have hnat : (5244207369 : ℕ)^4269*12500000000000^3245 ≤ 5347260859591^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244207369 10000000000 5347260859591 12500000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706866777/5000000000 : ℝ)^4269 ≤ (2787908582397/6250000000000 : ℝ)^3245 := by
    have hnat : (2706866777 : ℕ)^4269*6250000000000^3245 ≤ 2787908582397^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706866777 5000000000 2787908582397 6250000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1036421009/5000000000 : ℝ), (5244207369/10000000000 : ℝ), (2706866777/5000000000 : ℝ)] ![(12615375790753/100000000000000 : ℝ), (5347260859591/12500000000000 : ℝ), (2787908582397/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1036421009/5000000000 : ℝ)|^4269 ≤ (12615375790753/100000000000000 : ℝ)^3245
        have hw : |(-1036421009/5000000000 : ℝ)|=(1036421009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244207369/10000000000 : ℝ)|^4269 ≤ (5347260859591/12500000000000 : ℝ)^3245
        have hw : |(5244207369/10000000000 : ℝ)|=(5244207369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706866777/5000000000 : ℝ)|^4269 ≤ (2787908582397/6250000000000 : ℝ)^3245
        have hw : |(2706866777/5000000000 : ℝ)|=(2706866777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s7_5 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663214549/1250000000 : ℝ)*x 0 + (-198971753/1000000000 : ℝ)*x 1 + (216549339/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663214549/1250000000 : ℝ)^4269 ≤ (21719688939601/50000000000000 : ℝ)^3245 := by
    have hnat : (663214549 : ℕ)^4269*50000000000000^3245 ≤ 21719688939601^3245*1250000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663214549 1250000000 21719688939601 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (198971753/1000000000 : ℝ)^4269 ≤ (1494260706243/12500000000000 : ℝ)^3245 := by
    have hnat : (198971753 : ℕ)^4269*12500000000000^3245 ≤ 1494260706243^3245*1000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198971753 1000000000 1494260706243 12500000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216549339/400000000 : ℝ)^4269 ≤ (5575817057753/12500000000000 : ℝ)^3245 := by
    have hnat : (216549339 : ℕ)^4269*12500000000000^3245 ≤ 5575817057753^3245*400000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216549339 400000000 5575817057753 12500000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663214549/1250000000 : ℝ), (-198971753/1000000000 : ℝ), (216549339/400000000 : ℝ)] ![(21719688939601/50000000000000 : ℝ), (1494260706243/12500000000000 : ℝ), (5575817057753/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663214549/1250000000 : ℝ)|^4269 ≤ (21719688939601/50000000000000 : ℝ)^3245
        have hw : |(663214549/1250000000 : ℝ)|=(663214549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-198971753/1000000000 : ℝ)|^4269 ≤ (1494260706243/12500000000000 : ℝ)^3245
        have hw : |(-198971753/1000000000 : ℝ)|=(198971753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216549339/400000000 : ℝ)|^4269 ≤ (5575817057753/12500000000000 : ℝ)^3245
        have hw : |(216549339/400000000 : ℝ)|=(216549339/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s7_6 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42445731/80000000 : ℝ)*x 0 + (5413733573/10000000000 : ℝ)*x 1 + (-1989717419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42445731/80000000 : ℝ)^4269 ≤ (43439377696097/100000000000000 : ℝ)^3245 := by
    have hnat : (42445731 : ℕ)^4269*100000000000000^3245 ≤ 43439377696097^3245*80000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42445731 80000000 43439377696097 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413733573/10000000000 : ℝ)^4269 ≤ (8921307504861/20000000000000 : ℝ)^3245 := by
    have hnat : (5413733573 : ℕ)^4269*20000000000000^3245 ≤ 8921307504861^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413733573 10000000000 8921307504861 20000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1989717419/10000000000 : ℝ)^4269 ≤ (11954084772621/100000000000000 : ℝ)^3245 := by
    have hnat : (1989717419 : ℕ)^4269*100000000000000^3245 ≤ 11954084772621^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989717419 10000000000 11954084772621 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42445731/80000000 : ℝ), (5413733573/10000000000 : ℝ), (-1989717419/10000000000 : ℝ)] ![(43439377696097/100000000000000 : ℝ), (8921307504861/20000000000000 : ℝ), (11954084772621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42445731/80000000 : ℝ)|^4269 ≤ (43439377696097/100000000000000 : ℝ)^3245
        have hw : |(42445731/80000000 : ℝ)|=(42445731/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413733573/10000000000 : ℝ)|^4269 ≤ (8921307504861/20000000000000 : ℝ)^3245
        have hw : |(5413733573/10000000000 : ℝ)|=(5413733573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1989717419/10000000000 : ℝ)|^4269 ≤ (11954084772621/100000000000000 : ℝ)^3245
        have hw : |(-1989717419/10000000000 : ℝ)|=(1989717419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s7_7 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083837921/2500000000 : ℝ)*x 0 + (4514081461/10000000000 : ℝ)*x 1 + (1040850043/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083837921/2500000000 : ℝ)^4269 ≤ (1665148090503/5000000000000 : ℝ)^3245 := by
    have hnat : (1083837921 : ℕ)^4269*5000000000000^3245 ≤ 1665148090503^3245*2500000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083837921 2500000000 1665148090503 5000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514081461/10000000000 : ℝ)^4269 ≤ (17560403202371/50000000000000 : ℝ)^3245 := by
    have hnat : (4514081461 : ℕ)^4269*50000000000000^3245 ≤ 17560403202371^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514081461 10000000000 17560403202371 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040850043/2500000000 : ℝ)^4269 ≤ (631524635409/2000000000000 : ℝ)^3245 := by
    have hnat : (1040850043 : ℕ)^4269*2000000000000^3245 ≤ 631524635409^3245*2500000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040850043 2500000000 631524635409 2000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083837921/2500000000 : ℝ), (4514081461/10000000000 : ℝ), (1040850043/2500000000 : ℝ)] ![(1665148090503/5000000000000 : ℝ), (17560403202371/50000000000000 : ℝ), (631524635409/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083837921/2500000000 : ℝ)|^4269 ≤ (1665148090503/5000000000000 : ℝ)^3245
        have hw : |(1083837921/2500000000 : ℝ)|=(1083837921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514081461/10000000000 : ℝ)|^4269 ≤ (17560403202371/50000000000000 : ℝ)^3245
        have hw : |(4514081461/10000000000 : ℝ)|=(4514081461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1040850043/2500000000 : ℝ)|^4269 ≤ (631524635409/2000000000000 : ℝ)^3245
        have hw : |(1040850043/2500000000 : ℝ)|=(1040850043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1309_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30685957/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11069/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1107/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3671/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7343/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11069/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7343/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11069/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7343/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11069/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7343/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11069/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7343/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11069/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7343/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11069/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11069/100000 : ℝ) ^ (1067/256 : ℝ) ≤ (10372265632932379/100000000000000000000 : ℝ) := by
    have hpowers : (11069/100000 : ℝ)^1067 ≤ (10372265632932379/100000000000000000000 : ℝ)^256 := by
      have hnat : (11069 : ℕ)^1067*100000000000000000000^256 ≤ 10372265632932379^256*100000^1067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11069 100000 10372265632932379 100000000000000000000 1067 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11069/100000 : ℝ)) (X := (10372265632932379/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7343/50000 : ℝ) ^ (1067/256 : ℝ) ≤ (33703881700515199/100000000000000000000 : ℝ) := by
    have hpowers : (7343/50000 : ℝ)^1067 ≤ (33703881700515199/100000000000000000000 : ℝ)^256 := by
      have hnat : (7343 : ℕ)^1067*100000000000000000000^256 ≤ 33703881700515199^256*50000^1067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7343 50000 33703881700515199 100000000000000000000 1067 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7343/50000 : ℝ)) (X := (33703881700515199/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010372265632932379/50000000000000000000 : ℝ) ≤ (5000248836990781/5000000000000000 : ℝ) ^ (1067/256 : ℝ) := by
    have hpowers : (50010372265632932379/50000000000000000000 : ℝ)^256 ≤ (5000248836990781/5000000000000000 : ℝ)^1067 := by
      have hnat : (50010372265632932379 : ℕ)^256*5000000000000000^1067 ≤ 5000248836990781^1067*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010372265632932379 50000000000000000000 5000248836990781 5000000000000000 256 1067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000248836990781/5000000000000000 : ℝ)) (X := (50010372265632932379/50000000000000000000 : ℝ)) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022038073666723789/50000000000000000000 : ℝ) ≤ (10001057319976981/10000000000000000 : ℝ) ^ (1067/256 : ℝ) := by
    have hpowers : (50022038073666723789/50000000000000000000 : ℝ)^256 ≤ (10001057319976981/10000000000000000 : ℝ)^1067 := by
      have hnat : (50022038073666723789 : ℕ)^256*10000000000000000^1067 ≤ 10001057319976981^1067*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022038073666723789 50000000000000000000 10001057319976981 10000000000000000 256 1067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001057319976981/10000000000000000 : ℝ)) (X := (50022038073666723789/50000000000000000000 : ℝ)) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033703881700515199/50000000000000000000 : ℝ) ≤ (25004042414931/25000000000000 : ℝ) ^ (1067/256 : ℝ) := by
    have hpowers : (50033703881700515199/50000000000000000000 : ℝ)^256 ≤ (25004042414931/25000000000000 : ℝ)^1067 := by
      have hnat : (50033703881700515199 : ℕ)^256*25000000000000^1067 ≤ 25004042414931^1067*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033703881700515199 50000000000000000000 25004042414931 25000000000000 256 1067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25004042414931/25000000000000 : ℝ)) (X := (50033703881700515199/50000000000000000000 : ℝ)) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10372265632932379/100000000000000000000 : ℝ) ≤ ((9039852660936180983/9042500000000000000 : ℝ)+2*(559645995419/361700000000000 : ℝ)*(11069/100000 : ℝ))^(1067/256 : ℝ) := by
    rw [show (9039852660936180983/9042500000000000000 : ℝ)+2*(559645995419/361700000000000 : ℝ)*(11069/100000 : ℝ)=(5000248836990781/5000000000000000 : ℝ) by norm_num, show 1+2*(10372265632932379/100000000000000000000 : ℝ)=(50010372265632932379/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33703881700515199/100000000000000000000 : ℝ)+(10372265632932379/100000000000000000000 : ℝ) ≤ ((9039852660936180983/9042500000000000000 : ℝ)+(559645995419/361700000000000 : ℝ)*((7343/50000 : ℝ)+(11069/100000 : ℝ)))^(1067/256 : ℝ) := by
    rw [show (9039852660936180983/9042500000000000000 : ℝ)+(559645995419/361700000000000 : ℝ)*((7343/50000 : ℝ)+(11069/100000 : ℝ))=(10001057319976981/10000000000000000 : ℝ) by norm_num, show 1+(33703881700515199/100000000000000000000 : ℝ)+(10372265632932379/100000000000000000000 : ℝ)=(50022038073666723789/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33703881700515199/100000000000000000000 : ℝ) ≤ ((9039852660936180983/9042500000000000000 : ℝ)+2*(559645995419/361700000000000 : ℝ)*(7343/50000 : ℝ))^(1067/256 : ℝ) := by
    rw [show (9039852660936180983/9042500000000000000 : ℝ)+2*(559645995419/361700000000000 : ℝ)*(7343/50000 : ℝ)=(25004042414931/25000000000000 : ℝ) by norm_num, show 1+2*(33703881700515199/100000000000000000000 : ℝ)=(50033703881700515199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9039852660936180983/9042500000000000000 : ℝ)*(X 1 0+X 2 0)+(559645995419/361700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1067/256 : ℝ)) (lo := (11069/100000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (9039852660936180983/9042500000000000000 : ℝ)) (alpha := (559645995419/361700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9039852660936180983/9042500000000000000 : ℝ)*(X 0 1+X 2 1)+(559645995419/361700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1067/256 : ℝ)) (lo := (11069/100000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (9039852660936180983/9042500000000000000 : ℝ)) (alpha := (559645995419/361700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9039852660936180983/9042500000000000000 : ℝ)*(X 0 2+X 1 2)+(559645995419/361700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1067/256 : ℝ)) (lo := (11069/100000 : ℝ)) (hi := (7343/50000 : ℝ)) (c := (9039852660936180983/9042500000000000000 : ℝ)) (alpha := (559645995419/361700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-129551877/625000000 : ℝ)*X 0 0+(5414347673/10000000000 : ℝ)*X 0 1+(2621797987/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674761967/5000000000 : ℝ)*X 1 0+(-2159852467/10000000000 : ℝ)*X 1 1+(2621799717/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534952577/1000000000 : ℝ)*X 2 0+(1048719243/2000000000 : ℝ)*X 2 1+(-1079927141/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4335323743/10000000000 : ℝ)*X 0 0+(1040534061/2500000000 : ℝ)*X 0 1+(903068203/2000000000 : ℝ)*X 0 2+(4335323743/10000000000 : ℝ)*X 1 0+(1040534061/2500000000 : ℝ)*X 1 1+(903068203/2000000000 : ℝ)*X 1 2+(4335323743/10000000000 : ℝ)*X 2 0+(1040534061/2500000000 : ℝ)*X 2 1+(903068203/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1036421009/5000000000 : ℝ)*X 0 0+(5244207369/10000000000 : ℝ)*X 0 1+(2706866777/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663214549/1250000000 : ℝ)*X 1 0+(-198971753/1000000000 : ℝ)*X 1 1+(216549339/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((42445731/80000000 : ℝ)*X 2 0+(5413733573/10000000000 : ℝ)*X 2 1+(-1989717419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1083837921/2500000000 : ℝ)*X 0 0+(4514081461/10000000000 : ℝ)*X 0 1+(1040850043/2500000000 : ℝ)*X 0 2+(1083837921/2500000000 : ℝ)*X 1 0+(4514081461/10000000000 : ℝ)*X 1 1+(1040850043/2500000000 : ℝ)*X 1 2+(1083837921/2500000000 : ℝ)*X 2 0+(4514081461/10000000000 : ℝ)*X 2 1+(1040850043/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (490794257941356131792127393/45212500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (252245463/10000000000000 : ℝ)*(base23) + (577171037/100000000000000 : ℝ)*(upper2) + (49973903/25000000000000 : ℝ)*(upper3) + (40551459/25000000000000 : ℝ)*(upper4) + (434395365950581/10000000000000 : ℝ)*(major0) + (434395365950581/10000000000000 : ℝ)*(major1) + (434395365950581/10000000000000 : ℝ)*(major2) + (732070910414217/12500000000000 : ℝ)*(sp0) + (5856674638420851/100000000000000 : ℝ)*(sp1) + (2928319981858719/50000000000000 : ℝ)*(sp2) + (2831222302496269/100000000000000 : ℝ)*(sp3) + (21471021423/20000000000000 : ℝ)*(sp4) + (32152248783/100000000000000 : ℝ)*(sp6) + (5008125943/50000000000000 : ℝ)*(sp7) + (707808079687039/25000000000000 : ℝ)*(f.failure) + (5856674638420851/100000000000000 : ℝ)*(f.sum) + (11547072876581/723400000000000000000000000 : ℝ)*base65 + (543086917326851123/90425000000000000000000000000000 : ℝ)*base67 + (1468911675245551123/90425000000000000000000000000000 : ℝ)*base69 + (2991161777652851123/90425000000000000000000000000000 : ℝ)*base71 + (3684031501427/3617000000000000000000000000 : ℝ)*base74 + (1129884590172551123/90425000000000000000000000000000 : ℝ)*base75 + (77021643866176123/90425000000000000000000000000000 : ℝ)*base77 + (1565439014508801123/90425000000000000000000000000000 : ℝ)*base79 + (91675052683/36170000000000000000000000 : ℝ)*base81 + (2211323/500000000000000000000 : ℝ)*base89 + (2211323/500000000000000000000 : ℝ)*base91 + (2211323/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (797931286520431836098859/226062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (60495009/10000000000000 : ℝ)*(base19) + (849951729/100000000000000 : ℝ)*(base23) + (5179641/4000000000000 : ℝ)*(lower1) + (101354841/100000000000000 : ℝ)*(upper3) + (6349689/6250000000000 : ℝ)*(lower4) + (35854547/50000000000000 : ℝ)*(upper5) + (4375185757693/100000000000 : ℝ)*(major0) + (4375185757693/100000000000 : ℝ)*(major1) + (4375185757693/100000000000 : ℝ)*(major2) + (4385340121/50000000000000 : ℝ)*(sp2) + (1474695780963407/25000000000000 : ℝ)*(sp4) + (2949391259451769/50000000000000 : ℝ)*(sp5) + (2949386751610829/50000000000000 : ℝ)*(sp6) + (2851588273875897/100000000000000 : ℝ)*(sp7) + (2851588273875897/100000000000000 : ℝ)*(f.failure) + (1474695780963407/25000000000000 : ℝ)*(f.sum) + (3440333366963/904250000000000000000000000 : ℝ)*base65 + (45171442910931031/904250000000000000000000000000 : ℝ)*base68 + (423502440494219/904250000000000000000000000000 : ℝ)*base69 + (60423450443509781/904250000000000000000000000000 : ℝ)*base72 + (8877488098209/3617000000000000000000000000 : ℝ)*base74 + (162936849088582719/904250000000000000000000000000 : ℝ)*base75 + (3162784544315719/904250000000000000000000000000 : ℝ)*base77 + (1969982091107969/904250000000000000000000000000 : ℝ)*base79 + (2764928399073/1808500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1321571/2000000000000000000000 : ℝ)*base90 + (1321571/2000000000000000000000 : ℝ)*base92 + (1321571/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1309_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30685957/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7343/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11069/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1107/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3671/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1309_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1309_s8_0 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1036416829/5000000000 : ℝ)*x 0 + (5414331339/10000000000 : ℝ)*x 1 + (655451221/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036416829/5000000000 : ℝ)^4269 ≤ (2523061771207/20000000000000 : ℝ)^3245 := by
    have hnat : (1036416829 : ℕ)^4269*20000000000000^3245 ≤ 2523061771207^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036416829 5000000000 2523061771207 20000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414331339/10000000000 : ℝ)^4269 ≤ (11153254294753/25000000000000 : ℝ)^3245 := by
    have hnat : (5414331339 : ℕ)^4269*25000000000000^3245 ≤ 11153254294753^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414331339 10000000000 11153254294753 25000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655451221/1250000000 : ℝ)^4269 ≤ (534645924341/1250000000000 : ℝ)^3245 := by
    have hnat : (655451221 : ℕ)^4269*1250000000000^3245 ≤ 534645924341^3245*1250000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655451221 1250000000 534645924341 1250000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1036416829/5000000000 : ℝ), (5414331339/10000000000 : ℝ), (655451221/1250000000 : ℝ)] ![(2523061771207/20000000000000 : ℝ), (11153254294753/25000000000000 : ℝ), (534645924341/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1036416829/5000000000 : ℝ)|^4269 ≤ (2523061771207/20000000000000 : ℝ)^3245
        have hw : |(-1036416829/5000000000 : ℝ)|=(1036416829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414331339/10000000000 : ℝ)|^4269 ≤ (11153254294753/25000000000000 : ℝ)^3245
        have hw : |(5414331339/10000000000 : ℝ)|=(5414331339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655451221/1250000000 : ℝ)|^4269 ≤ (534645924341/1250000000000 : ℝ)^3245
        have hw : |(655451221/1250000000 : ℝ)|=(655451221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s8_1 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674760351/5000000000 : ℝ)*x 0 + (-539960867/2500000000 : ℝ)*x 1 + (327725593/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674760351/5000000000 : ℝ)^4269 ≤ (2744487632099/6250000000000 : ℝ)^3245 := by
    have hnat : (2674760351 : ℕ)^4269*6250000000000^3245 ≤ 2744487632099^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674760351 5000000000 2744487632099 6250000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539960867/2500000000 : ℝ)^4269 ≤ (13316526918499/100000000000000 : ℝ)^3245 := by
    have hnat : (539960867 : ℕ)^4269*100000000000000^3245 ≤ 13316526918499^3245*2500000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539960867 2500000000 13316526918499 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327725593/625000000 : ℝ)^4269 ≤ (42771670942619/100000000000000 : ℝ)^3245 := by
    have hnat : (327725593 : ℕ)^4269*100000000000000^3245 ≤ 42771670942619^3245*625000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327725593 625000000 42771670942619 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674760351/5000000000 : ℝ), (-539960867/2500000000 : ℝ), (327725593/625000000 : ℝ)] ![(2744487632099/6250000000000 : ℝ), (13316526918499/100000000000000 : ℝ), (42771670942619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674760351/5000000000 : ℝ)|^4269 ≤ (2744487632099/6250000000000 : ℝ)^3245
        have hw : |(2674760351/5000000000 : ℝ)|=(2674760351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-539960867/2500000000 : ℝ)|^4269 ≤ (13316526918499/100000000000000 : ℝ)^3245
        have hw : |(-539960867/2500000000 : ℝ)|=(539960867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327725593/625000000 : ℝ)|^4269 ≤ (42771670942619/100000000000000 : ℝ)^3245
        have hw : |(327725593/625000000 : ℝ)|=(327725593/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s8_2 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349520633/10000000000 : ℝ)*x 0 + (1310902393/2500000000 : ℝ)*x 1 + (-2159843451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349520633/10000000000 : ℝ)^4269 ≤ (21955900684231/50000000000000 : ℝ)^3245 := by
    have hnat : (5349520633 : ℕ)^4269*50000000000000^3245 ≤ 21955900684231^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349520633 10000000000 21955900684231 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310902393/2500000000 : ℝ)^4269 ≤ (42771671844017/100000000000000 : ℝ)^3245 := by
    have hnat : (1310902393 : ℕ)^4269*100000000000000^3245 ≤ 42771671844017^3245*2500000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310902393 2500000000 42771671844017 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2159843451/10000000000 : ℝ)^4269 ≤ (1331652678061/10000000000000 : ℝ)^3245 := by
    have hnat : (2159843451 : ℕ)^4269*10000000000000^3245 ≤ 1331652678061^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159843451 10000000000 1331652678061 10000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349520633/10000000000 : ℝ), (1310902393/2500000000 : ℝ), (-2159843451/10000000000 : ℝ)] ![(21955900684231/50000000000000 : ℝ), (42771671844017/100000000000000 : ℝ), (1331652678061/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349520633/10000000000 : ℝ)|^4269 ≤ (21955900684231/50000000000000 : ℝ)^3245
        have hw : |(5349520633/10000000000 : ℝ)|=(5349520633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310902393/2500000000 : ℝ)|^4269 ≤ (42771671844017/100000000000000 : ℝ)^3245
        have hw : |(1310902393/2500000000 : ℝ)|=(1310902393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2159843451/10000000000 : ℝ)|^4269 ≤ (1331652678061/10000000000000 : ℝ)^3245
        have hw : |(-2159843451/10000000000 : ℝ)|=(2159843451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s8_3 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (541915817/1250000000 : ℝ)*x 0 + (4162160179/10000000000 : ℝ)*x 1 + (451531493/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541915817/1250000000 : ℝ)^4269 ≤ (6660541534011/20000000000000 : ℝ)^3245 := by
    have hnat : (541915817 : ℕ)^4269*20000000000000^3245 ≤ 6660541534011^3245*1250000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541915817 1250000000 6660541534011 20000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4162160179/10000000000 : ℝ)^4269 ≤ (6312772053733/20000000000000 : ℝ)^3245 := by
    have hnat : (4162160179 : ℕ)^4269*20000000000000^3245 ≤ 6312772053733^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162160179 10000000000 6312772053733 20000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451531493/1000000000 : ℝ)^4269 ≤ (17566716023829/50000000000000 : ℝ)^3245 := by
    have hnat : (451531493 : ℕ)^4269*50000000000000^3245 ≤ 17566716023829^3245*1000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451531493 1000000000 17566716023829 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541915817/1250000000 : ℝ), (4162160179/10000000000 : ℝ), (451531493/1000000000 : ℝ)] ![(6660541534011/20000000000000 : ℝ), (6312772053733/20000000000000 : ℝ), (17566716023829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541915817/1250000000 : ℝ)|^4269 ≤ (6660541534011/20000000000000 : ℝ)^3245
        have hw : |(541915817/1250000000 : ℝ)|=(541915817/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4162160179/10000000000 : ℝ)|^4269 ≤ (6312772053733/20000000000000 : ℝ)^3245
        have hw : |(4162160179/10000000000 : ℝ)|=(4162160179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(451531493/1000000000 : ℝ)|^4269 ≤ (17566716023829/50000000000000 : ℝ)^3245
        have hw : |(451531493/1000000000 : ℝ)|=(451531493/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s8_4 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-414569279/2000000000 : ℝ)*x 0 + (1048843749/2000000000 : ℝ)*x 1 + (2706859529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414569279/2000000000 : ℝ)^4269 ≤ (3153852708859/25000000000000 : ℝ)^3245 := by
    have hnat : (414569279 : ℕ)^4269*25000000000000^3245 ≤ 3153852708859^3245*2000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414569279 2000000000 3153852708859 25000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048843749/2000000000 : ℝ)^4269 ≤ (42778208956213/100000000000000 : ℝ)^3245 := by
    have hnat : (1048843749 : ℕ)^4269*100000000000000^3245 ≤ 42778208956213^3245*2000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048843749 2000000000 42778208956213 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706859529/5000000000 : ℝ)^4269 ≤ (22303190093819/50000000000000 : ℝ)^3245 := by
    have hnat : (2706859529 : ℕ)^4269*50000000000000^3245 ≤ 22303190093819^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706859529 5000000000 22303190093819 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-414569279/2000000000 : ℝ), (1048843749/2000000000 : ℝ), (2706859529/5000000000 : ℝ)] ![(3153852708859/25000000000000 : ℝ), (42778208956213/100000000000000 : ℝ), (22303190093819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-414569279/2000000000 : ℝ)|^4269 ≤ (3153852708859/25000000000000 : ℝ)^3245
        have hw : |(-414569279/2000000000 : ℝ)|=(414569279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048843749/2000000000 : ℝ)|^4269 ≤ (42778208956213/100000000000000 : ℝ)^3245
        have hw : |(1048843749/2000000000 : ℝ)|=(1048843749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706859529/5000000000 : ℝ)|^4269 ≤ (22303190093819/50000000000000 : ℝ)^3245
        have hw : |(2706859529/5000000000 : ℝ)|=(2706859529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s8_5 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4335352931/10000000000 : ℝ)*x 0 + (4514054553/10000000000 : ℝ)*x 1 + (4163426513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4335352931/10000000000 : ℝ)^4269 ≤ (33302974411973/100000000000000 : ℝ)^3245 := by
    have hnat : (4335352931 : ℕ)^4269*100000000000000^3245 ≤ 33302974411973^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335352931 10000000000 33302974411973 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514054553/10000000000 : ℝ)^4269 ≤ (35120530989767/100000000000000 : ℝ)^3245 := by
    have hnat : (4514054553 : ℕ)^4269*100000000000000^3245 ≤ 35120530989767^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514054553 10000000000 35120530989767 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4163426513/10000000000 : ℝ)^4269 ≤ (31576494589167/100000000000000 : ℝ)^3245 := by
    have hnat : (4163426513 : ℕ)^4269*100000000000000^3245 ≤ 31576494589167^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163426513 10000000000 31576494589167 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4335352931/10000000000 : ℝ), (4514054553/10000000000 : ℝ), (4163426513/10000000000 : ℝ)] ![(33302974411973/100000000000000 : ℝ), (35120530989767/100000000000000 : ℝ), (31576494589167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4335352931/10000000000 : ℝ)|^4269 ≤ (33302974411973/100000000000000 : ℝ)^3245
        have hw : |(4335352931/10000000000 : ℝ)|=(4335352931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514054553/10000000000 : ℝ)|^4269 ≤ (35120530989767/100000000000000 : ℝ)^3245
        have hw : |(4514054553/10000000000 : ℝ)|=(4514054553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4163426513/10000000000 : ℝ)|^4269 ≤ (31576494589167/100000000000000 : ℝ)^3245
        have hw : |(4163426513/10000000000 : ℝ)|=(4163426513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1309_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30685957/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3671/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1107/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11071/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3671/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3671/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1107/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3671/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1107/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3671/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1107/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3671/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1107/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3671/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1107/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3671/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1107/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1107/10000 : ℝ) ^ (1067/256 : ℝ) ≤ (10376171809268597/100000000000000000000 : ℝ) := by
    have hpowers : (1107/10000 : ℝ)^1067 ≤ (10376171809268597/100000000000000000000 : ℝ)^256 := by
      have hnat : (1107 : ℕ)^1067*100000000000000000000^256 ≤ 10376171809268597^256*10000^1067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1107 10000 10376171809268597 100000000000000000000 1067 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1107/10000 : ℝ)) (X := (10376171809268597/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3671/25000 : ℝ) ^ (1067/256 : ℝ) ≤ (16842377563730661/50000000000000000000 : ℝ) := by
    have hpowers : (3671/25000 : ℝ)^1067 ≤ (16842377563730661/50000000000000000000 : ℝ)^256 := by
      have hnat : (3671 : ℕ)^1067*50000000000000000000^256 ≤ 16842377563730661^256*25000^1067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3671 25000 16842377563730661 50000000000000000000 1067 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3671/25000 : ℝ)) (X := (16842377563730661/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010376171809268597/50000000000000000000 : ℝ) ≤ (10000497861389897/10000000000000000 : ℝ) ^ (1067/256 : ℝ) := by
    have hpowers : (50010376171809268597/50000000000000000000 : ℝ)^256 ≤ (10000497861389897/10000000000000000 : ℝ)^1067 := by
      have hnat : (50010376171809268597 : ℕ)^256*10000000000000000^1067 ≤ 10000497861389897^1067*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010376171809268597 50000000000000000000 10000497861389897 10000000000000000 256 1067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000497861389897/10000000000000000 : ℝ)) (X := (50010376171809268597/50000000000000000000 : ℝ)) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044060926936729919/100000000000000000000 : ℝ) ≤ (10001056954923847/10000000000000000 : ℝ) ^ (1067/256 : ℝ) := by
    have hpowers : (100044060926936729919/100000000000000000000 : ℝ)^256 ≤ (10001056954923847/10000000000000000 : ℝ)^1067 := by
      have hnat : (100044060926936729919 : ℕ)^256*10000000000000000^1067 ≤ 10001056954923847^1067*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044060926936729919 100000000000000000000 10001056954923847 10000000000000000 256 1067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001056954923847/10000000000000000 : ℝ)) (X := (100044060926936729919/100000000000000000000 : ℝ)) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016842377563730661/25000000000000000000 : ℝ) ≤ (10001616048457797/10000000000000000 : ℝ) ^ (1067/256 : ℝ) := by
    have hpowers : (25016842377563730661/25000000000000000000 : ℝ)^256 ≤ (10001616048457797/10000000000000000 : ℝ)^1067 := by
      have hnat : (25016842377563730661 : ℕ)^256*10000000000000000^1067 ≤ 10001616048457797^1067*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016842377563730661 25000000000000000000 10001616048457797 10000000000000000 256 1067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001616048457797/10000000000000000 : ℝ)) (X := (25016842377563730661/25000000000000000000 : ℝ)) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10376171809268597/100000000000000000000 : ℝ) ≤ ((18064710470110717379/18070000000000000000 : ℝ)+2*(11181870679/7228000000000 : ℝ)*(1107/10000 : ℝ))^(1067/256 : ℝ) := by
    rw [show (18064710470110717379/18070000000000000000 : ℝ)+2*(11181870679/7228000000000 : ℝ)*(1107/10000 : ℝ)=(10000497861389897/10000000000000000 : ℝ) by norm_num, show 1+2*(10376171809268597/100000000000000000000 : ℝ)=(50010376171809268597/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16842377563730661/50000000000000000000 : ℝ)+(10376171809268597/100000000000000000000 : ℝ) ≤ ((18064710470110717379/18070000000000000000 : ℝ)+(11181870679/7228000000000 : ℝ)*((3671/25000 : ℝ)+(1107/10000 : ℝ)))^(1067/256 : ℝ) := by
    rw [show (18064710470110717379/18070000000000000000 : ℝ)+(11181870679/7228000000000 : ℝ)*((3671/25000 : ℝ)+(1107/10000 : ℝ))=(10001056954923847/10000000000000000 : ℝ) by norm_num, show 1+(16842377563730661/50000000000000000000 : ℝ)+(10376171809268597/100000000000000000000 : ℝ)=(100044060926936729919/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16842377563730661/50000000000000000000 : ℝ) ≤ ((18064710470110717379/18070000000000000000 : ℝ)+2*(11181870679/7228000000000 : ℝ)*(3671/25000 : ℝ))^(1067/256 : ℝ) := by
    rw [show (18064710470110717379/18070000000000000000 : ℝ)+2*(11181870679/7228000000000 : ℝ)*(3671/25000 : ℝ)=(10001616048457797/10000000000000000 : ℝ) by norm_num, show 1+2*(16842377563730661/50000000000000000000 : ℝ)=(25016842377563730661/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18064710470110717379/18070000000000000000 : ℝ)*(X 1 0+X 2 0)+(11181870679/7228000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1067/256 : ℝ)) (lo := (1107/10000 : ℝ)) (hi := (3671/25000 : ℝ)) (c := (18064710470110717379/18070000000000000000 : ℝ)) (alpha := (11181870679/7228000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18064710470110717379/18070000000000000000 : ℝ)*(X 0 1+X 2 1)+(11181870679/7228000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1067/256 : ℝ)) (lo := (1107/10000 : ℝ)) (hi := (3671/25000 : ℝ)) (c := (18064710470110717379/18070000000000000000 : ℝ)) (alpha := (11181870679/7228000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18064710470110717379/18070000000000000000 : ℝ)*(X 0 2+X 1 2)+(11181870679/7228000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1067/256 : ℝ)) (lo := (1107/10000 : ℝ)) (hi := (3671/25000 : ℝ)) (c := (18064710470110717379/18070000000000000000 : ℝ)) (alpha := (11181870679/7228000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1036416829/5000000000 : ℝ)*X 0 0+(5414331339/10000000000 : ℝ)*X 0 1+(655451221/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674760351/5000000000 : ℝ)*X 1 0+(-539960867/2500000000 : ℝ)*X 1 1+(327725593/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349520633/10000000000 : ℝ)*X 2 0+(1310902393/2500000000 : ℝ)*X 2 1+(-2159843451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((541915817/1250000000 : ℝ)*X 0 0+(4162160179/10000000000 : ℝ)*X 0 1+(451531493/1000000000 : ℝ)*X 0 2+(541915817/1250000000 : ℝ)*X 1 0+(4162160179/10000000000 : ℝ)*X 1 1+(451531493/1000000000 : ℝ)*X 1 2+(541915817/1250000000 : ℝ)*X 2 0+(4162160179/10000000000 : ℝ)*X 2 1+(451531493/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-414569279/2000000000 : ℝ)*X 0 0+(1048843749/2000000000 : ℝ)*X 0 1+(2706859529/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4335352931/10000000000 : ℝ)*X 0 0+(4514054553/10000000000 : ℝ)*X 0 1+(4163426513/10000000000 : ℝ)*X 0 2+(4335352931/10000000000 : ℝ)*X 1 0+(4514054553/10000000000 : ℝ)*X 1 1+(4163426513/10000000000 : ℝ)*X 1 2+(4335352931/10000000000 : ℝ)*X 2 0+(4514054553/10000000000 : ℝ)*X 2 1+(4163426513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63137488131557776167735789/45175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (171968741/25000000000000 : ℝ)*(base19) + (583858309/100000000000000 : ℝ)*(base23) + (44892557/100000000000000 : ℝ)*(upper3) + (7613571/50000000000000 : ℝ)*(upper4) + (4066783/12500000000000 : ℝ)*(upper5) + (434456944644403/10000000000000 : ℝ)*(major0) + (434456944644403/10000000000000 : ℝ)*(major1) + (434456944644403/10000000000000 : ℝ)*(major2) + (1430053278029/24414062500 : ℝ)*(sp0) + (2928752245980649/50000000000000 : ℝ)*(sp1) + (183047018624311/3125000000000 : ℝ)*(sp2) + (2831626731222007/100000000000000 : ℝ)*(sp3) + (3476514739/50000000000000 : ℝ)*(sp4) + (433452653/6250000000000 : ℝ)*(sp5) + (566326733292891/20000000000000 : ℝ)*(f.failure) + (2928752589918131/50000000000000 : ℝ)*(f.sum) + (215647456917/56468750000000000000000000 : ℝ)*base65 + (1651637040821579737/180700000000000000000000000000000 : ℝ)*base67 + (1324488312560679737/180700000000000000000000000000000 : ℝ)*base69 + (1281565220174479737/180700000000000000000000000000000 : ℝ)*base71 + (5355194457719/1807000000000000000000000000 : ℝ)*base73 + (3013420749590920263/180700000000000000000000000000000 : ℝ)*base76 + (52210279880479737/180700000000000000000000000000000 : ℝ)*base77 + (163755471020979737/180700000000000000000000000000000 : ℝ)*base79 + (44341642797/225875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1631687/400000000000000000000 : ℝ)*base89 + (1631687/400000000000000000000 : ℝ)*base91 + (1631687/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1309_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30685957/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3671/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1107/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11071/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3671/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1309_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1309_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30685957/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11059/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11071/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3671/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1309_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1309_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1309_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30685957/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11059/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11071/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3671/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1309_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
