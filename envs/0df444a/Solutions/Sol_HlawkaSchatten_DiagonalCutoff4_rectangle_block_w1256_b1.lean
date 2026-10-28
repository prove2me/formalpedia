-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1256_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:29:29.084852+00:00
-- url     : https://prove2.me/submissions/548ff57c-9835-4fab-a482-f9f2dc33b7a5

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
theorem support_rectangle_w1256_s3_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2110800479/10000000000 : ℝ)*x 0 + (21673783/40000000 : ℝ)*x 1 + (655210239/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110800479/10000000000 : ℝ)^8449 ≤ (2566457347269/20000000000000 : ℝ)^6401 := by
    have hnat : (2110800479 : ℕ)^8449*20000000000000^6401 ≤ 2566457347269^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110800479 10000000000 2566457347269 20000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21673783/40000000 : ℝ)^8449 ≤ (44537716568729/100000000000000 : ℝ)^6401 := by
    have hnat : (21673783 : ℕ)^8449*100000000000000^6401 ≤ 44537716568729^6401*40000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21673783 40000000 44537716568729 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655210239/1250000000 : ℝ)^8449 ≤ (42629996679967/100000000000000 : ℝ)^6401 := by
    have hnat : (655210239 : ℕ)^8449*100000000000000^6401 ≤ 42629996679967^6401*1250000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655210239 1250000000 42629996679967 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2110800479/10000000000 : ℝ), (21673783/40000000 : ℝ), (655210239/1250000000 : ℝ)] ![(2566457347269/20000000000000 : ℝ), (44537716568729/100000000000000 : ℝ), (42629996679967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2110800479/10000000000 : ℝ)|^8449 ≤ (2566457347269/20000000000000 : ℝ)^6401
        have hw : |(-2110800479/10000000000 : ℝ)|=(2110800479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21673783/40000000 : ℝ)|^8449 ≤ (44537716568729/100000000000000 : ℝ)^6401
        have hw : |(21673783/40000000 : ℝ)|=(21673783/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655210239/1250000000 : ℝ)|^8449 ≤ (42629996679967/100000000000000 : ℝ)^6401
        have hw : |(655210239/1250000000 : ℝ)|=(655210239/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s3_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5351183517/10000000000 : ℝ)*x 0 + (-2200951797/10000000000 : ℝ)*x 1 + (5241682009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351183517/10000000000 : ℝ)^8449 ≤ (43809406638317/100000000000000 : ℝ)^6401 := by
    have hnat : (5351183517 : ℕ)^8449*100000000000000^6401 ≤ 43809406638317^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351183517 10000000000 43809406638317 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2200951797/10000000000 : ℝ)^8449 ≤ (6780297811543/50000000000000 : ℝ)^6401 := by
    have hnat : (2200951797 : ℕ)^8449*50000000000000^6401 ≤ 6780297811543^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200951797 10000000000 6780297811543 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241682009/10000000000 : ℝ)^8449 ≤ (21314998860631/50000000000000 : ℝ)^6401 := by
    have hnat : (5241682009 : ℕ)^8449*50000000000000^6401 ≤ 21314998860631^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241682009 10000000000 21314998860631 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351183517/10000000000 : ℝ), (-2200951797/10000000000 : ℝ), (5241682009/10000000000 : ℝ)] ![(43809406638317/100000000000000 : ℝ), (6780297811543/50000000000000 : ℝ), (21314998860631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351183517/10000000000 : ℝ)|^8449 ≤ (43809406638317/100000000000000 : ℝ)^6401
        have hw : |(5351183517/10000000000 : ℝ)|=(5351183517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2200951797/10000000000 : ℝ)|^8449 ≤ (6780297811543/50000000000000 : ℝ)^6401
        have hw : |(-2200951797/10000000000 : ℝ)|=(2200951797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241682009/10000000000 : ℝ)|^8449 ≤ (21314998860631/50000000000000 : ℝ)^6401
        have hw : |(5241682009/10000000000 : ℝ)|=(5241682009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s3_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5351183483/10000000000 : ℝ)*x 0 + (5241682481/10000000000 : ℝ)*x 1 + (-2200951219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351183483/10000000000 : ℝ)^8449 ≤ (8761881254181/20000000000000 : ℝ)^6401 := by
    have hnat : (5351183483 : ℕ)^8449*20000000000000^6401 ≤ 8761881254181^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351183483 10000000000 8761881254181 20000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241682481/10000000000 : ℝ)^8449 ≤ (42630002788183/100000000000000 : ℝ)^6401 := by
    have hnat : (5241682481 : ℕ)^8449*100000000000000^6401 ≤ 42630002788183^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241682481 10000000000 42630002788183 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2200951219/10000000000 : ℝ)^8449 ≤ (13560590922483/100000000000000 : ℝ)^6401 := by
    have hnat : (2200951219 : ℕ)^8449*100000000000000^6401 ≤ 13560590922483^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200951219 10000000000 13560590922483 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351183483/10000000000 : ℝ), (5241682481/10000000000 : ℝ), (-2200951219/10000000000 : ℝ)] ![(8761881254181/20000000000000 : ℝ), (42630002788183/100000000000000 : ℝ), (13560590922483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351183483/10000000000 : ℝ)|^8449 ≤ (8761881254181/20000000000000 : ℝ)^6401
        have hw : |(5351183483/10000000000 : ℝ)|=(5351183483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241682481/10000000000 : ℝ)|^8449 ≤ (42630002788183/100000000000000 : ℝ)^6401
        have hw : |(5241682481/10000000000 : ℝ)|=(5241682481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2200951219/10000000000 : ℝ)|^8449 ≤ (13560590922483/100000000000000 : ℝ)^6401
        have hw : |(-2200951219/10000000000 : ℝ)|=(2200951219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s3_3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347224553/10000000000 : ℝ)*x 0 + (4171050501/10000000000 : ℝ)*x 1 + (4530596283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347224553/10000000000 : ℝ)^8449 ≤ (16650528716669/50000000000000 : ℝ)^6401 := by
    have hnat : (4347224553 : ℕ)^8449*50000000000000^6401 ≤ 16650528716669^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347224553 10000000000 16650528716669 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171050501/10000000000 : ℝ)^8449 ≤ (7882844959853/25000000000000 : ℝ)^6401 := by
    have hnat : (4171050501 : ℕ)^8449*25000000000000^6401 ≤ 7882844959853^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171050501 10000000000 7882844959853 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4530596283/10000000000 : ℝ)^8449 ≤ (35167562704239/100000000000000 : ℝ)^6401 := by
    have hnat : (4530596283 : ℕ)^8449*100000000000000^6401 ≤ 35167562704239^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530596283 10000000000 35167562704239 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347224553/10000000000 : ℝ), (4171050501/10000000000 : ℝ), (4530596283/10000000000 : ℝ)] ![(16650528716669/50000000000000 : ℝ), (7882844959853/25000000000000 : ℝ), (35167562704239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347224553/10000000000 : ℝ)|^8449 ≤ (16650528716669/50000000000000 : ℝ)^6401
        have hw : |(4347224553/10000000000 : ℝ)|=(4347224553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171050501/10000000000 : ℝ)|^8449 ≤ (7882844959853/25000000000000 : ℝ)^6401
        have hw : |(4171050501/10000000000 : ℝ)|=(4171050501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4530596283/10000000000 : ℝ)|^8449 ≤ (35167562704239/100000000000000 : ℝ)^6401
        have hw : |(4530596283/10000000000 : ℝ)|=(4530596283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s3_4 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-527703651/2500000000 : ℝ)*x 0 + (5242318801/10000000000 : ℝ)*x 1 + (5417805113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527703651/2500000000 : ℝ)^8449 ≤ (6416200040791/50000000000000 : ℝ)^6401 := by
    have hnat : (527703651 : ℕ)^8449*50000000000000^6401 ≤ 6416200040791^6401*2500000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527703651 2500000000 6416200040791 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242318801/10000000000 : ℝ)^8449 ≤ (42636833817383/100000000000000 : ℝ)^6401 := by
    have hnat : (5242318801 : ℕ)^8449*100000000000000^6401 ≤ 42636833817383^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242318801 10000000000 42636833817383 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417805113/10000000000 : ℝ)^8449 ≤ (69579322021/156250000000 : ℝ)^6401 := by
    have hnat : (5417805113 : ℕ)^8449*156250000000^6401 ≤ 69579322021^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417805113 10000000000 69579322021 156250000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527703651/2500000000 : ℝ), (5242318801/10000000000 : ℝ), (5417805113/10000000000 : ℝ)] ![(6416200040791/50000000000000 : ℝ), (42636833817383/100000000000000 : ℝ), (69579322021/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527703651/2500000000 : ℝ)|^8449 ≤ (6416200040791/50000000000000 : ℝ)^6401
        have hw : |(-527703651/2500000000 : ℝ)|=(527703651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242318801/10000000000 : ℝ)|^8449 ≤ (42636833817383/100000000000000 : ℝ)^6401
        have hw : |(5242318801/10000000000 : ℝ)|=(5242318801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417805113/10000000000 : ℝ)|^8449 ≤ (69579322021/156250000000 : ℝ)^6401
        have hw : |(5417805113/10000000000 : ℝ)|=(5417805113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s3_5 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5306045309/10000000000 : ℝ)*x 0 + (-25310351/125000000 : ℝ)*x 1 + (5417804951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5306045309/10000000000 : ℝ)^8449 ≤ (43322291355439/100000000000000 : ℝ)^6401 := by
    have hnat : (5306045309 : ℕ)^8449*100000000000000^6401 ≤ 43322291355439^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5306045309 10000000000 43322291355439 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25310351/125000000 : ℝ)^8449 ≤ (759184018121/6250000000000 : ℝ)^6401 := by
    have hnat : (25310351 : ℕ)^8449*6250000000000^6401 ≤ 759184018121^6401*125000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25310351 125000000 759184018121 6250000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417804951/10000000000 : ℝ)^8449 ≤ (11132691083971/25000000000000 : ℝ)^6401 := by
    have hnat : (5417804951 : ℕ)^8449*25000000000000^6401 ≤ 11132691083971^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417804951 10000000000 11132691083971 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5306045309/10000000000 : ℝ), (-25310351/125000000 : ℝ), (5417804951/10000000000 : ℝ)] ![(43322291355439/100000000000000 : ℝ), (759184018121/6250000000000 : ℝ), (11132691083971/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5306045309/10000000000 : ℝ)|^8449 ≤ (43322291355439/100000000000000 : ℝ)^6401
        have hw : |(5306045309/10000000000 : ℝ)|=(5306045309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-25310351/125000000 : ℝ)|^8449 ≤ (759184018121/6250000000000 : ℝ)^6401
        have hw : |(-25310351/125000000 : ℝ)|=(25310351/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417804951/10000000000 : ℝ)|^8449 ≤ (11132691083971/25000000000000 : ℝ)^6401
        have hw : |(5417804951/10000000000 : ℝ)|=(5417804951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s3_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5306044661/10000000000 : ℝ)*x 0 + (169306419/312500000 : ℝ)*x 1 + (-126551771/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5306044661/10000000000 : ℝ)^8449 ≤ (21661142185971/50000000000000 : ℝ)^6401 := by
    have hnat : (5306044661 : ℕ)^8449*50000000000000^6401 ≤ 21661142185971^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5306044661 10000000000 21661142185971 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169306419/312500000 : ℝ)^8449 ≤ (44530769293929/100000000000000 : ℝ)^6401 := by
    have hnat : (169306419 : ℕ)^8449*100000000000000^6401 ≤ 44530769293929^6401*312500000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169306419 312500000 44530769293929 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126551771/625000000 : ℝ)^8449 ≤ (6073473158521/50000000000000 : ℝ)^6401 := by
    have hnat : (126551771 : ℕ)^8449*50000000000000^6401 ≤ 6073473158521^6401*625000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126551771 625000000 6073473158521 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5306044661/10000000000 : ℝ), (169306419/312500000 : ℝ), (-126551771/625000000 : ℝ)] ![(21661142185971/50000000000000 : ℝ), (44530769293929/100000000000000 : ℝ), (6073473158521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5306044661/10000000000 : ℝ)|^8449 ≤ (21661142185971/50000000000000 : ℝ)^6401
        have hw : |(5306044661/10000000000 : ℝ)|=(5306044661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169306419/312500000 : ℝ)|^8449 ≤ (44530769293929/100000000000000 : ℝ)^6401
        have hw : |(169306419/312500000 : ℝ)|=(169306419/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-126551771/625000000 : ℝ)|^8449 ≤ (6073473158521/50000000000000 : ℝ)^6401
        have hw : |(-126551771/625000000 : ℝ)|=(126551771/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s3_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347252787/10000000000 : ℝ)*x 0 + (1132325009/2500000000 : ℝ)*x 1 + (4172352763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347252787/10000000000 : ℝ)^8449 ≤ (33301342913737/100000000000000 : ℝ)^6401 := by
    have hnat : (4347252787 : ℕ)^8449*100000000000000^6401 ≤ 33301342913737^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347252787 10000000000 33301342913737 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1132325009/2500000000 : ℝ)^8449 ≤ (17577141135029/50000000000000 : ℝ)^6401 := by
    have hnat : (1132325009 : ℕ)^8449*50000000000000^6401 ≤ 17577141135029^6401*2500000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132325009 2500000000 17577141135029 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172352763/10000000000 : ℝ)^8449 ≤ (31544374803047/100000000000000 : ℝ)^6401 := by
    have hnat : (4172352763 : ℕ)^8449*100000000000000^6401 ≤ 31544374803047^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172352763 10000000000 31544374803047 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347252787/10000000000 : ℝ), (1132325009/2500000000 : ℝ), (4172352763/10000000000 : ℝ)] ![(33301342913737/100000000000000 : ℝ), (17577141135029/50000000000000 : ℝ), (31544374803047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347252787/10000000000 : ℝ)|^8449 ≤ (33301342913737/100000000000000 : ℝ)^6401
        have hw : |(4347252787/10000000000 : ℝ)|=(4347252787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1132325009/2500000000 : ℝ)|^8449 ≤ (17577141135029/50000000000000 : ℝ)^6401
        have hw : |(1132325009/2500000000 : ℝ)|=(1132325009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172352763/10000000000 : ℝ)|^8449 ≤ (31544374803047/100000000000000 : ℝ)^6401
        have hw : |(4172352763/10000000000 : ℝ)|=(4172352763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1256_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16187/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2389/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10947/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (459/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16187/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2389/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16187/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2389/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16187/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2389/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16187/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2389/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16187/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2389/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16187/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2389/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2389/25000 : ℝ) ^ (33/8 : ℝ) ≤ (6217833407523691/100000000000000000000 : ℝ) := by
    have hpowers : (2389/25000 : ℝ)^33 ≤ (6217833407523691/100000000000000000000 : ℝ)^8 := by
      have hnat : (2389 : ℕ)^33*100000000000000000000^8 ≤ 6217833407523691^8*25000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2389 25000 6217833407523691 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2389/25000 : ℝ)) (X := (6217833407523691/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hpowhi : (16187/100000 : ℝ) ^ (33/8 : ℝ) ≤ (1093556580665851/2000000000000000000 : ℝ) := by
    have hpowers : (16187/100000 : ℝ)^33 ≤ (1093556580665851/2000000000000000000 : ℝ)^8 := by
      have hnat : (16187 : ℕ)^33*2000000000000000000^8 ≤ 1093556580665851^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16187 100000 1093556580665851 2000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16187/100000 : ℝ)) (X := (1093556580665851/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006217833407523691/50000000000000000000 : ℝ) ≤ (5000150728255493/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (50006217833407523691/50000000000000000000 : ℝ)^8 ≤ (5000150728255493/5000000000000000 : ℝ)^33 := by
      have hnat : (50006217833407523691 : ℕ)^8*5000000000000000^33 ≤ 5000150728255493^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006217833407523691 50000000000000000000 5000150728255493 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000150728255493/5000000000000000 : ℝ)) (X := (50006217833407523691/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner10 : (100060895662440816241/100000000000000000000 : ℝ) ≤ (10001475918083113/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (100060895662440816241/100000000000000000000 : ℝ)^8 ≤ (10001475918083113/10000000000000000 : ℝ)^33 := by
      have hnat : (100060895662440816241 : ℕ)^8*10000000000000000^33 ≤ 10001475918083113^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100060895662440816241 100000000000000000000 10001475918083113 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001475918083113/10000000000000000 : ℝ)) (X := (100060895662440816241/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner11 : (1001093556580665851/1000000000000000000 : ℝ) ≤ (250066259491381/250000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (1001093556580665851/1000000000000000000 : ℝ)^8 ≤ (250066259491381/250000000000000 : ℝ)^33 := by
      have hnat : (1001093556580665851 : ℕ)^8*250000000000000^33 ≤ 250066259491381^33*1000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1001093556580665851 1000000000000000000 250066259491381 250000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250066259491381/250000000000000 : ℝ)) (X := (1001093556580665851/1000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6217833407523691/100000000000000000000 : ℝ) ≤ ((33144776324278928471/33155000000000000000 : ℝ)+2*(1174461572127/663100000000000 : ℝ)*(2389/25000 : ℝ))^(33/8 : ℝ) := by
    rw [show (33144776324278928471/33155000000000000000 : ℝ)+2*(1174461572127/663100000000000 : ℝ)*(2389/25000 : ℝ)=(5000150728255493/5000000000000000 : ℝ) by norm_num, show 1+2*(6217833407523691/100000000000000000000 : ℝ)=(50006217833407523691/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1093556580665851/2000000000000000000 : ℝ)+(6217833407523691/100000000000000000000 : ℝ) ≤ ((33144776324278928471/33155000000000000000 : ℝ)+(1174461572127/663100000000000 : ℝ)*((16187/100000 : ℝ)+(2389/25000 : ℝ)))^(33/8 : ℝ) := by
    rw [show (33144776324278928471/33155000000000000000 : ℝ)+(1174461572127/663100000000000 : ℝ)*((16187/100000 : ℝ)+(2389/25000 : ℝ))=(10001475918083113/10000000000000000 : ℝ) by norm_num, show 1+(1093556580665851/2000000000000000000 : ℝ)+(6217833407523691/100000000000000000000 : ℝ)=(100060895662440816241/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1093556580665851/2000000000000000000 : ℝ) ≤ ((33144776324278928471/33155000000000000000 : ℝ)+2*(1174461572127/663100000000000 : ℝ)*(16187/100000 : ℝ))^(33/8 : ℝ) := by
    rw [show (33144776324278928471/33155000000000000000 : ℝ)+2*(1174461572127/663100000000000 : ℝ)*(16187/100000 : ℝ)=(250066259491381/250000000000000 : ℝ) by norm_num, show 1+2*(1093556580665851/2000000000000000000 : ℝ)=(1001093556580665851/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33144776324278928471/33155000000000000000 : ℝ)*(X 1 0+X 2 0)+(1174461572127/663100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (2389/25000 : ℝ)) (hi := (16187/100000 : ℝ)) (c := (33144776324278928471/33155000000000000000 : ℝ)) (alpha := (1174461572127/663100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33144776324278928471/33155000000000000000 : ℝ)*(X 0 1+X 2 1)+(1174461572127/663100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (2389/25000 : ℝ)) (hi := (16187/100000 : ℝ)) (c := (33144776324278928471/33155000000000000000 : ℝ)) (alpha := (1174461572127/663100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33144776324278928471/33155000000000000000 : ℝ)*(X 0 2+X 1 2)+(1174461572127/663100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (2389/25000 : ℝ)) (hi := (16187/100000 : ℝ)) (c := (33144776324278928471/33155000000000000000 : ℝ)) (alpha := (1174461572127/663100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2110800479/10000000000 : ℝ)*X 0 0+(21673783/40000000 : ℝ)*X 0 1+(655210239/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351183517/10000000000 : ℝ)*X 1 0+(-2200951797/10000000000 : ℝ)*X 1 1+(5241682009/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351183483/10000000000 : ℝ)*X 2 0+(5241682481/10000000000 : ℝ)*X 2 1+(-2200951219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4347224553/10000000000 : ℝ)*X 0 0+(4171050501/10000000000 : ℝ)*X 0 1+(4530596283/10000000000 : ℝ)*X 0 2+(4347224553/10000000000 : ℝ)*X 1 0+(4171050501/10000000000 : ℝ)*X 1 1+(4530596283/10000000000 : ℝ)*X 1 2+(4347224553/10000000000 : ℝ)*X 2 0+(4171050501/10000000000 : ℝ)*X 2 1+(4530596283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-527703651/2500000000 : ℝ)*X 0 0+(5242318801/10000000000 : ℝ)*X 0 1+(5417805113/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5306045309/10000000000 : ℝ)*X 1 0+(-25310351/125000000 : ℝ)*X 1 1+(5417804951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5306044661/10000000000 : ℝ)*X 2 0+(169306419/312500000 : ℝ)*X 2 1+(-126551771/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4347252787/10000000000 : ℝ)*X 0 0+(1132325009/2500000000 : ℝ)*X 0 1+(4172352763/10000000000 : ℝ)*X 0 2+(4347252787/10000000000 : ℝ)*X 1 0+(1132325009/2500000000 : ℝ)*X 1 1+(4172352763/10000000000 : ℝ)*X 1 2+(4347252787/10000000000 : ℝ)*X 2 0+(1132325009/2500000000 : ℝ)*X 2 1+(4172352763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3012047435730236066263375407/828875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24876641/50000000000000 : ℝ)*(base19) + (138341229/100000000000000 : ℝ)*(lower2) + (59507987/50000000000000 : ℝ)*(lower3) + (9031749/12500000000000 : ℝ)*(lower4) + (4219301427881139/100000000000000 : ℝ)*(major0) + (4219301427881139/100000000000000 : ℝ)*(major1) + (210965071394057/5000000000000 : ℝ)*(major2) + (5657283836424933/100000000000000 : ℝ)*(sp0) + (1131459000828869/20000000000000 : ℝ)*(sp1) + (5657308058000631/100000000000000 : ℝ)*(sp2) + (695322814505271/25000000000000 : ℝ)*(sp3) + (12110787849/50000000000000 : ℝ)*(sp4) + (3251025751/25000000000000 : ℝ)*(sp5) + (427326327/12500000000000 : ℝ)*(sp7) + (27812946766317/1000000000000 : ℝ)*(f.failure) + (5657308058000631/100000000000000 : ℝ)*(f.sum) + (7521396486657/3490000000000000000000000000 : ℝ)*base65 + (33804508153963991531/3315500000000000000000000000000000 : ℝ)*base68 + (677884848437120653/165775000000000000000000000000000 : ℝ)*base70 + (12385395893987491531/3315500000000000000000000000000000 : ℝ)*base72 + (2836318473957/3490000000000000000000000000 : ℝ)*base73 + (579036761370154347/165775000000000000000000000000000 : ℝ)*base75 + (28461326566859841531/3315500000000000000000000000000000 : ℝ)*base78 + (15699803791746841531/3315500000000000000000000000000000 : ℝ)*base80 + (6542731418369/4144375000000000000000000000 : ℝ)*base82 + (560211/100000000000000000000 : ℝ)*base89 + (560211/100000000000000000000 : ℝ)*base91 + (439789/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2377679750140053811967412339/1657750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1018316261/50000000000000 : ℝ)*(base19) + (257687501/20000000000000 : ℝ)*(base23) + (28623371/50000000000000 : ℝ)*(lower4) + (165804529/50000000000000 : ℝ)*(upper5) + (4249992739340297/100000000000000 : ℝ)*(major0) + (4249992739340297/100000000000000 : ℝ)*(major1) + (4249992739340297/100000000000000 : ℝ)*(major2) + (1170850677/50000000000000 : ℝ)*(sp0) + (50087313149/100000000000000 : ℝ)*(sp1) + (31259753073/100000000000000 : ℝ)*(sp2) + (2849228600328231/50000000000000 : ℝ)*(sp4) + (1139681483682429/20000000000000 : ℝ)*(sp5) + (2849213497083619/50000000000000 : ℝ)*(sp6) + (1400762944256697/50000000000000 : ℝ)*(sp7) + (1400762944256697/50000000000000 : ℝ)*(f.failure) + (712307442794727/12500000000000 : ℝ)*(f.sum) + (156923166322799/33155000000000000000000000000 : ℝ)*base65 + (10325823980813845887/3315500000000000000000000000000000 : ℝ)*base67 + (29652414139398845887/3315500000000000000000000000000000 : ℝ)*base69 + (2901086086178845887/3315500000000000000000000000000000 : ℝ)*base71 + (82609897522457/16577500000000000000000000000 : ℝ)*base73 + (20852522847477845887/3315500000000000000000000000000000 : ℝ)*base75 + (4641897686975654113/3315500000000000000000000000000000 : ℝ)*base78 + (22787896900338654113/3315500000000000000000000000000000 : ℝ)*base80 + (41059490606167/16577500000000000000000000000 : ℝ)*base81 + (48712249/5000000000000000000000 : ℝ)*base90 + (48712249/5000000000000000000000 : ℝ)*base92 + (48712249/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1256_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16187/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2389/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10947/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (459/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1256_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1256_s4_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056504211/5000000000 : ℝ)*x 0 + (5396931719/10000000000 : ℝ)*x 1 + (2630874319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056504211/5000000000 : ℝ)^8449 ≤ (12850007191067/100000000000000 : ℝ)^6401 := by
    have hnat : (1056504211 : ℕ)^8449*100000000000000^6401 ≤ 12850007191067^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056504211 5000000000 12850007191067 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396931719/10000000000 : ℝ)^8449 ≤ (44304447960909/100000000000000 : ℝ)^6401 := by
    have hnat : (5396931719 : ℕ)^8449*100000000000000^6401 ≤ 44304447960909^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396931719 10000000000 44304447960909 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630874319/5000000000 : ℝ)^8449 ≤ (428455448321/1000000000000 : ℝ)^6401 := by
    have hnat : (2630874319 : ℕ)^8449*1000000000000^6401 ≤ 428455448321^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630874319 5000000000 428455448321 1000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056504211/5000000000 : ℝ), (5396931719/10000000000 : ℝ), (2630874319/5000000000 : ℝ)] ![(12850007191067/100000000000000 : ℝ), (44304447960909/100000000000000 : ℝ), (428455448321/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056504211/5000000000 : ℝ)|^8449 ≤ (12850007191067/100000000000000 : ℝ)^6401
        have hw : |(-1056504211/5000000000 : ℝ)|=(1056504211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396931719/10000000000 : ℝ)|^8449 ≤ (44304447960909/100000000000000 : ℝ)^6401
        have hw : |(5396931719/10000000000 : ℝ)|=(5396931719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630874319/5000000000 : ℝ)|^8449 ≤ (428455448321/1000000000000 : ℝ)^6401
        have hw : |(2630874319/5000000000 : ℝ)|=(2630874319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s4_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345752861/10000000000 : ℝ)*x 0 + (-2181635209/10000000000 : ℝ)*x 1 + (105234973/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345752861/10000000000 : ℝ)^8449 ≤ (10937682785481/25000000000000 : ℝ)^6401 := by
    have hnat : (5345752861 : ℕ)^8449*25000000000000^6401 ≤ 10937682785481^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345752861 10000000000 10937682785481 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2181635209/10000000000 : ℝ)^8449 ≤ (13403723877183/100000000000000 : ℝ)^6401 := by
    have hnat : (2181635209 : ℕ)^8449*100000000000000^6401 ≤ 13403723877183^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181635209 10000000000 13403723877183 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105234973/200000000 : ℝ)^8449 ≤ (21422772480539/50000000000000 : ℝ)^6401 := by
    have hnat : (105234973 : ℕ)^8449*50000000000000^6401 ≤ 21422772480539^6401*200000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105234973 200000000 21422772480539 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345752861/10000000000 : ℝ), (-2181635209/10000000000 : ℝ), (105234973/200000000 : ℝ)] ![(10937682785481/25000000000000 : ℝ), (13403723877183/100000000000000 : ℝ), (21422772480539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345752861/10000000000 : ℝ)|^8449 ≤ (10937682785481/25000000000000 : ℝ)^6401
        have hw : |(5345752861/10000000000 : ℝ)|=(5345752861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2181635209/10000000000 : ℝ)|^8449 ≤ (13403723877183/100000000000000 : ℝ)^6401
        have hw : |(-2181635209/10000000000 : ℝ)|=(2181635209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105234973/200000000 : ℝ)|^8449 ≤ (21422772480539/50000000000000 : ℝ)^6401
        have hw : |(105234973/200000000 : ℝ)|=(105234973/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s4_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672876471/5000000000 : ℝ)*x 0 + (2630874291/5000000000 : ℝ)*x 1 + (-272704399/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672876471/5000000000 : ℝ)^8449 ≤ (21875366008473/50000000000000 : ℝ)^6401 := by
    have hnat : (2672876471 : ℕ)^8449*50000000000000^6401 ≤ 21875366008473^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672876471 5000000000 21875366008473 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630874291/5000000000 : ℝ)^8449 ≤ (8569108846041/20000000000000 : ℝ)^6401 := by
    have hnat : (2630874291 : ℕ)^8449*20000000000000^6401 ≤ 8569108846041^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630874291 5000000000 8569108846041 20000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272704399/1250000000 : ℝ)^8449 ≤ (13403723739319/100000000000000 : ℝ)^6401 := by
    have hnat : (272704399 : ℕ)^8449*100000000000000^6401 ≤ 13403723739319^6401*1250000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272704399 1250000000 13403723739319 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672876471/5000000000 : ℝ), (2630874291/5000000000 : ℝ), (-272704399/1250000000 : ℝ)] ![(21875366008473/50000000000000 : ℝ), (8569108846041/20000000000000 : ℝ), (13403723739319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672876471/5000000000 : ℝ)|^8449 ≤ (21875366008473/50000000000000 : ℝ)^6401
        have hw : |(2672876471/5000000000 : ℝ)|=(2672876471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630874291/5000000000 : ℝ)|^8449 ≤ (8569108846041/20000000000000 : ℝ)^6401
        have hw : |(2630874291/5000000000 : ℝ)|=(2630874291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272704399/1250000000 : ℝ)|^8449 ≤ (13403723739319/100000000000000 : ℝ)^6401
        have hw : |(-272704399/1250000000 : ℝ)|=(272704399/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s4_3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (271784309/625000000 : ℝ)*x 0 + (263323111/625000000 : ℝ)*x 1 + (897627943/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271784309/625000000 : ℝ)^8449 ≤ (8328612322699/25000000000000 : ℝ)^6401 := by
    have hnat : (271784309 : ℕ)^8449*25000000000000^6401 ≤ 8328612322699^6401*625000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271784309 625000000 8328612322699 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263323111/625000000 : ℝ)^8449 ≤ (31952334485199/100000000000000 : ℝ)^6401 := by
    have hnat : (263323111 : ℕ)^8449*100000000000000^6401 ≤ 31952334485199^6401*625000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263323111 625000000 31952334485199 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897627943/2000000000 : ℝ)^8449 ≤ (4341652025397/12500000000000 : ℝ)^6401 := by
    have hnat : (897627943 : ℕ)^8449*12500000000000^6401 ≤ 4341652025397^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897627943 2000000000 4341652025397 12500000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271784309/625000000 : ℝ), (263323111/625000000 : ℝ), (897627943/2000000000 : ℝ)] ![(8328612322699/25000000000000 : ℝ), (31952334485199/100000000000000 : ℝ), (4341652025397/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271784309/625000000 : ℝ)|^8449 ≤ (8328612322699/25000000000000 : ℝ)^6401
        have hw : |(271784309/625000000 : ℝ)|=(271784309/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263323111/625000000 : ℝ)|^8449 ≤ (31952334485199/100000000000000 : ℝ)^6401
        have hw : |(263323111/625000000 : ℝ)|=(263323111/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897627943/2000000000 : ℝ)|^8449 ≤ (4341652025397/12500000000000 : ℝ)^6401
        have hw : |(897627943/2000000000 : ℝ)|=(897627943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s4_4 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-528253577/2500000000 : ℝ)*x 0 + (82220653/156250000 : ℝ)*x 1 + (5396557213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528253577/2500000000 : ℝ)^8449 ≤ (6425027219351/50000000000000 : ℝ)^6401 := by
    have hnat : (528253577 : ℕ)^8449*50000000000000^6401 ≤ 6425027219351^6401*2500000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528253577 2500000000 6425027219351 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82220653/156250000 : ℝ)^8449 ≤ (535619444833/1250000000000 : ℝ)^6401 := by
    have hnat : (82220653 : ℕ)^8449*1250000000000^6401 ≤ 535619444833^6401*156250000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82220653 156250000 535619444833 1250000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396557213/10000000000 : ℝ)^8449 ≤ (44300389962731/100000000000000 : ℝ)^6401 := by
    have hnat : (5396557213 : ℕ)^8449*100000000000000^6401 ≤ 44300389962731^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396557213 10000000000 44300389962731 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528253577/2500000000 : ℝ), (82220653/156250000 : ℝ), (5396557213/10000000000 : ℝ)] ![(6425027219351/50000000000000 : ℝ), (535619444833/1250000000000 : ℝ), (44300389962731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528253577/2500000000 : ℝ)|^8449 ≤ (6425027219351/50000000000000 : ℝ)^6401
        have hw : |(-528253577/2500000000 : ℝ)|=(528253577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82220653/156250000 : ℝ)|^8449 ≤ (535619444833/1250000000000 : ℝ)^6401
        have hw : |(82220653/156250000 : ℝ)|=(82220653/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396557213/10000000000 : ℝ)|^8449 ≤ (44300389962731/100000000000000 : ℝ)^6401
        have hw : |(5396557213/10000000000 : ℝ)|=(5396557213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s4_5 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311229643/10000000000 : ℝ)*x 0 + (-2046826551/10000000000 : ℝ)*x 1 + (2698278597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311229643/10000000000 : ℝ)^8449 ≤ (21689085831189/50000000000000 : ℝ)^6401 := by
    have hnat : (5311229643 : ℕ)^8449*50000000000000^6401 ≤ 21689085831189^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311229643 10000000000 21689085831189 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2046826551/10000000000 : ℝ)^8449 ≤ (2464287712523/20000000000000 : ℝ)^6401 := by
    have hnat : (2046826551 : ℕ)^8449*20000000000000^6401 ≤ 2464287712523^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046826551 10000000000 2464287712523 20000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698278597/5000000000 : ℝ)^8449 ≤ (5537548719607/12500000000000 : ℝ)^6401 := by
    have hnat : (2698278597 : ℕ)^8449*12500000000000^6401 ≤ 5537548719607^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698278597 5000000000 5537548719607 12500000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311229643/10000000000 : ℝ), (-2046826551/10000000000 : ℝ), (2698278597/5000000000 : ℝ)] ![(21689085831189/50000000000000 : ℝ), (2464287712523/20000000000000 : ℝ), (5537548719607/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311229643/10000000000 : ℝ)|^8449 ≤ (21689085831189/50000000000000 : ℝ)^6401
        have hw : |(5311229643/10000000000 : ℝ)|=(5311229643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2046826551/10000000000 : ℝ)|^8449 ≤ (2464287712523/20000000000000 : ℝ)^6401
        have hw : |(-2046826551/10000000000 : ℝ)|=(2046826551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698278597/5000000000 : ℝ)|^8449 ≤ (5537548719607/12500000000000 : ℝ)^6401
        have hw : |(2698278597/5000000000 : ℝ)|=(2698278597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s4_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311229421/10000000000 : ℝ)*x 0 + (5396557397/10000000000 : ℝ)*x 1 + (-81873063/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311229421/10000000000 : ℝ)^8449 ≤ (2711135579321/6250000000000 : ℝ)^6401 := by
    have hnat : (5311229421 : ℕ)^8449*6250000000000^6401 ≤ 2711135579321^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311229421 10000000000 2711135579321 6250000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396557397/10000000000 : ℝ)^8449 ≤ (44300391956459/100000000000000 : ℝ)^6401 := by
    have hnat : (5396557397 : ℕ)^8449*100000000000000^6401 ≤ 44300391956459^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396557397 10000000000 44300391956459 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81873063/400000000 : ℝ)^8449 ≤ (6160719376657/50000000000000 : ℝ)^6401 := by
    have hnat : (81873063 : ℕ)^8449*50000000000000^6401 ≤ 6160719376657^6401*400000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81873063 400000000 6160719376657 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311229421/10000000000 : ℝ), (5396557397/10000000000 : ℝ), (-81873063/400000000 : ℝ)] ![(2711135579321/6250000000000 : ℝ), (44300391956459/100000000000000 : ℝ), (6160719376657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311229421/10000000000 : ℝ)|^8449 ≤ (2711135579321/6250000000000 : ℝ)^6401
        have hw : |(5311229421/10000000000 : ℝ)|=(5311229421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396557397/10000000000 : ℝ)|^8449 ≤ (44300391956459/100000000000000 : ℝ)^6401
        have hw : |(5396557397/10000000000 : ℝ)|=(5396557397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-81873063/400000000 : ℝ)|^8449 ≤ (6160719376657/50000000000000 : ℝ)^6401
        have hw : |(-81873063/400000000 : ℝ)|=(81873063/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s4_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174280543/5000000000 : ℝ)*x 0 + (4487381091/10000000000 : ℝ)*x 1 + (2106965797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174280543/5000000000 : ℝ)^8449 ≤ (16657286036607/50000000000000 : ℝ)^6401 := by
    have hnat : (2174280543 : ℕ)^8449*50000000000000^6401 ≤ 16657286036607^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174280543 5000000000 16657286036607 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4487381091/10000000000 : ℝ)^8449 ≤ (34725467108829/100000000000000 : ℝ)^6401 := by
    have hnat : (4487381091 : ℕ)^8449*100000000000000^6401 ≤ 34725467108829^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487381091 10000000000 34725467108829 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106965797/5000000000 : ℝ)^8449 ≤ (6391992160633/20000000000000 : ℝ)^6401 := by
    have hnat : (2106965797 : ℕ)^8449*20000000000000^6401 ≤ 6391992160633^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106965797 5000000000 6391992160633 20000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174280543/5000000000 : ℝ), (4487381091/10000000000 : ℝ), (2106965797/5000000000 : ℝ)] ![(16657286036607/50000000000000 : ℝ), (34725467108829/100000000000000 : ℝ), (6391992160633/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174280543/5000000000 : ℝ)|^8449 ≤ (16657286036607/50000000000000 : ℝ)^6401
        have hw : |(2174280543/5000000000 : ℝ)|=(2174280543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4487381091/10000000000 : ℝ)|^8449 ≤ (34725467108829/100000000000000 : ℝ)^6401
        have hw : |(4487381091/10000000000 : ℝ)|=(4487381091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2106965797/5000000000 : ℝ)|^8449 ≤ (6391992160633/20000000000000 : ℝ)^6401
        have hw : |(2106965797/5000000000 : ℝ)|=(2106965797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1256_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (459/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10947/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (91/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7119/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (459/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10947/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (459/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10947/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (459/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10947/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (459/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10947/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (459/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10947/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (459/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10947/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10947/100000 : ℝ) ^ (33/8 : ℝ) ≤ (2722904256136787/25000000000000000000 : ℝ) := by
    have hpowers : (10947/100000 : ℝ)^33 ≤ (2722904256136787/25000000000000000000 : ℝ)^8 := by
      have hnat : (10947 : ℕ)^33*25000000000000000000^8 ≤ 2722904256136787^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10947 100000 2722904256136787 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10947/100000 : ℝ)) (X := (2722904256136787/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hpowhi : (459/3125 : ℝ) ^ (33/8 : ℝ) ≤ (7324044663867807/20000000000000000000 : ℝ) := by
    have hpowers : (459/3125 : ℝ)^33 ≤ (7324044663867807/20000000000000000000 : ℝ)^8 := by
      have hnat : (459 : ℕ)^33*20000000000000000000^8 ≤ 7324044663867807^8*3125^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        459 3125 7324044663867807 20000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (459/3125 : ℝ)) (X := (7324044663867807/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502722904256136787/12500000000000000000 : ℝ) ≤ (10000528034833813/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (12502722904256136787/12500000000000000000 : ℝ)^8 ≤ (10000528034833813/10000000000000000 : ℝ)^33 := by
      have hnat : (12502722904256136787 : ℕ)^8*10000000000000000^33 ≤ 10000528034833813^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502722904256136787 12500000000000000000 10000528034833813 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000528034833813/10000000000000000 : ℝ)) (X := (12502722904256136787/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047511840343886183/100000000000000000000 : ℝ) ≤ (10001151594959041/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (100047511840343886183/100000000000000000000 : ℝ)^8 ≤ (10001151594959041/10000000000000000 : ℝ)^33 := by
      have hnat : (100047511840343886183 : ℕ)^8*10000000000000000^33 ≤ 10001151594959041^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047511840343886183 100000000000000000000 10001151594959041 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001151594959041/10000000000000000 : ℝ)) (X := (100047511840343886183/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007324044663867807/10000000000000000000 : ℝ) ≤ (10001775155084269/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (10007324044663867807/10000000000000000000 : ℝ)^8 ≤ (10001775155084269/10000000000000000 : ℝ)^33 := by
      have hnat : (10007324044663867807 : ℕ)^8*10000000000000000^33 ≤ 10001775155084269^33*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007324044663867807 10000000000000000000 10001775155084269 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001775155084269/10000000000000000 : ℝ)) (X := (10007324044663867807/10000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2722904256136787/25000000000000000000 : ℝ) ≤ ((12466107717643850867/12470000000000000000 : ℝ)+2*(51963343769/31175000000000 : ℝ)*(10947/100000 : ℝ))^(33/8 : ℝ) := by
    rw [show (12466107717643850867/12470000000000000000 : ℝ)+2*(51963343769/31175000000000 : ℝ)*(10947/100000 : ℝ)=(10000528034833813/10000000000000000 : ℝ) by norm_num, show 1+2*(2722904256136787/25000000000000000000 : ℝ)=(12502722904256136787/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7324044663867807/20000000000000000000 : ℝ)+(2722904256136787/25000000000000000000 : ℝ) ≤ ((12466107717643850867/12470000000000000000 : ℝ)+(51963343769/31175000000000 : ℝ)*((459/3125 : ℝ)+(10947/100000 : ℝ)))^(33/8 : ℝ) := by
    rw [show (12466107717643850867/12470000000000000000 : ℝ)+(51963343769/31175000000000 : ℝ)*((459/3125 : ℝ)+(10947/100000 : ℝ))=(10001151594959041/10000000000000000 : ℝ) by norm_num, show 1+(7324044663867807/20000000000000000000 : ℝ)+(2722904256136787/25000000000000000000 : ℝ)=(100047511840343886183/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7324044663867807/20000000000000000000 : ℝ) ≤ ((12466107717643850867/12470000000000000000 : ℝ)+2*(51963343769/31175000000000 : ℝ)*(459/3125 : ℝ))^(33/8 : ℝ) := by
    rw [show (12466107717643850867/12470000000000000000 : ℝ)+2*(51963343769/31175000000000 : ℝ)*(459/3125 : ℝ)=(10001775155084269/10000000000000000 : ℝ) by norm_num, show 1+2*(7324044663867807/20000000000000000000 : ℝ)=(10007324044663867807/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12466107717643850867/12470000000000000000 : ℝ)*(X 1 0+X 2 0)+(51963343769/31175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (10947/100000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (12466107717643850867/12470000000000000000 : ℝ)) (alpha := (51963343769/31175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12466107717643850867/12470000000000000000 : ℝ)*(X 0 1+X 2 1)+(51963343769/31175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (10947/100000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (12466107717643850867/12470000000000000000 : ℝ)) (alpha := (51963343769/31175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12466107717643850867/12470000000000000000 : ℝ)*(X 0 2+X 1 2)+(51963343769/31175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (10947/100000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (12466107717643850867/12470000000000000000 : ℝ)) (alpha := (51963343769/31175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1056504211/5000000000 : ℝ)*X 0 0+(5396931719/10000000000 : ℝ)*X 0 1+(2630874319/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345752861/10000000000 : ℝ)*X 1 0+(-2181635209/10000000000 : ℝ)*X 1 1+(105234973/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672876471/5000000000 : ℝ)*X 2 0+(2630874291/5000000000 : ℝ)*X 2 1+(-272704399/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((271784309/625000000 : ℝ)*X 0 0+(263323111/625000000 : ℝ)*X 0 1+(897627943/2000000000 : ℝ)*X 0 2+(271784309/625000000 : ℝ)*X 1 0+(263323111/625000000 : ℝ)*X 1 1+(897627943/2000000000 : ℝ)*X 1 2+(271784309/625000000 : ℝ)*X 2 0+(263323111/625000000 : ℝ)*X 2 1+(897627943/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-528253577/2500000000 : ℝ)*X 0 0+(82220653/156250000 : ℝ)*X 0 1+(5396557213/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311229643/10000000000 : ℝ)*X 1 0+(-2046826551/10000000000 : ℝ)*X 1 1+(2698278597/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311229421/10000000000 : ℝ)*X 2 0+(5396557397/10000000000 : ℝ)*X 2 1+(-81873063/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2174280543/5000000000 : ℝ)*X 0 0+(4487381091/10000000000 : ℝ)*X 0 1+(2106965797/5000000000 : ℝ)*X 0 2+(2174280543/5000000000 : ℝ)*X 1 0+(4487381091/10000000000 : ℝ)*X 1 1+(2106965797/5000000000 : ℝ)*X 1 2+(2174280543/5000000000 : ℝ)*X 2 0+(4487381091/10000000000 : ℝ)*X 2 1+(2106965797/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (209161122176711968641596301/124700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (553389371/100000000000000 : ℝ)*(base19) + (505899459/100000000000000 : ℝ)*(base23) + (15444539/12500000000000 : ℝ)*(upper3) + (17061169/20000000000000 : ℝ)*(upper4) + (11100169/20000000000000 : ℝ)*(upper5) + (689635567688271/12500000000000 : ℝ)*(major0) + (689635567688271/12500000000000 : ℝ)*(major1) + (5517084541506169/100000000000000 : ℝ)*(major2) + (924673243440559/12500000000000 : ℝ)*(sp0) + (3698698168913707/50000000000000 : ℝ)*(sp1) + (3698698192658663/50000000000000 : ℝ)*(sp2) + (1818382680876249/50000000000000 : ℝ)*(sp3) + (10943692313/100000000000000 : ℝ)*(sp4) + (6774132557/100000000000000 : ℝ)*(sp7) + (1818386067942527/50000000000000 : ℝ)*(f.failure) + (1479479378243357/20000000000000 : ℝ)*(f.sum) + (1715031108701/1558750000000000000000000000 : ℝ)*base66 + (3957790879676994043/155875000000000000000000000000000 : ℝ)*base68 + (10143264441777701477/1247000000000000000000000000000000 : ℝ)*base70 + (2570874061182369043/155875000000000000000000000000000 : ℝ)*base72 + (9412357759191/6235000000000000000000000000 : ℝ)*base73 + (23806666255642701477/1247000000000000000000000000000000 : ℝ)*base76 + (1038624356194069043/155875000000000000000000000000000 : ℝ)*base78 + (5215934031439944043/155875000000000000000000000000000 : ℝ)*base80 + (38084378601/779375000000000000000000000 : ℝ)*base81 + (29952641/5000000000000000000000 : ℝ)*base89 + (29952641/5000000000000000000000 : ℝ)*base91 + (20047359/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1323309913201435670797972173/155875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1334175091/100000000000000 : ℝ)*(base19) + (1084479831/100000000000000 : ℝ)*(base23) + (186776393/100000000000000 : ℝ)*(upper3) + (24137449/100000000000000 : ℝ)*(lower4) + (68418063/100000000000000 : ℝ)*(upper5) + (2773872506177373/50000000000000 : ℝ)*(major0) + (2773872506177373/50000000000000 : ℝ)*(major1) + (2773872506177373/50000000000000 : ℝ)*(major2) + (30656092123/100000000000000 : ℝ)*(sp1) + (33082715911/100000000000000 : ℝ)*(sp2) + (3719253361792439/50000000000000 : ℝ)*(sp4) + (7438474733317663/100000000000000 : ℝ)*(sp5) + (1487694511277827/20000000000000 : ℝ)*(sp6) + (1828491509069661/50000000000000 : ℝ)*(sp7) + (1828491509069661/50000000000000 : ℝ)*(f.failure) + (3719253361792439/50000000000000 : ℝ)*(f.sum) + (1478872093821/1558750000000000000000000000 : ℝ)*base66 + (10876445875236367609/623500000000000000000000000000000 : ℝ)*base68 + (13838471538830367609/623500000000000000000000000000000 : ℝ)*base70 + (3675083366147367609/623500000000000000000000000000000 : ℝ)*base72 + (6721009416287/3117500000000000000000000000 : ℝ)*base74 + (24832133622743367609/623500000000000000000000000000000 : ℝ)*base76 + (2031623347405132391/623500000000000000000000000000000 : ℝ)*base77 + (6276455175729867609/623500000000000000000000000000000 : ℝ)*base80 + (2656717192911/6235000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (14566563/5000000000000000000000 : ℝ)*base89 + (14566563/5000000000000000000000 : ℝ)*base91 + (14566563/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1256_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (459/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10947/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1256_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1256_s5_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-42268693/200000000 : ℝ)*x 0 + (2696036423/5000000000 : ℝ)*x 1 + (5266327431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42268693/200000000 : ℝ)^8449 ≤ (3213357170937/25000000000000 : ℝ)^6401 := by
    have hnat : (42268693 : ℕ)^8449*25000000000000^6401 ≤ 3213357170937^6401*200000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42268693 200000000 3213357170937 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696036423/5000000000 : ℝ)^8449 ≤ (4425180614407/10000000000000 : ℝ)^6401 := by
    have hnat : (2696036423 : ℕ)^8449*10000000000000^6401 ≤ 4425180614407^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696036423 5000000000 4425180614407 10000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266327431/10000000000 : ℝ)^8449 ≤ (42894765160607/100000000000000 : ℝ)^6401 := by
    have hnat : (5266327431 : ℕ)^8449*100000000000000^6401 ≤ 42894765160607^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266327431 10000000000 42894765160607 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42268693/200000000 : ℝ), (2696036423/5000000000 : ℝ), (5266327431/10000000000 : ℝ)] ![(3213357170937/25000000000000 : ℝ), (4425180614407/10000000000000 : ℝ), (42894765160607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42268693/200000000 : ℝ)|^8449 ≤ (3213357170937/25000000000000 : ℝ)^6401
        have hw : |(-42268693/200000000 : ℝ)|=(42268693/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696036423/5000000000 : ℝ)|^8449 ≤ (4425180614407/10000000000000 : ℝ)^6401
        have hw : |(2696036423/5000000000 : ℝ)|=(2696036423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266327431/10000000000 : ℝ)|^8449 ≤ (42894765160607/100000000000000 : ℝ)^6401
        have hw : |(5266327431/10000000000 : ℝ)|=(5266327431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s5_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344522321/10000000000 : ℝ)*x 0 + (-1088601749/5000000000 : ℝ)*x 1 + (658290933/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344522321/10000000000 : ℝ)^8449 ≤ (10934359606967/25000000000000 : ℝ)^6401 := by
    have hnat : (5344522321 : ℕ)^8449*25000000000000^6401 ≤ 10934359606967^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344522321 10000000000 10934359606967 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088601749/5000000000 : ℝ)^8449 ≤ (13367796043391/100000000000000 : ℝ)^6401 := by
    have hnat : (1088601749 : ℕ)^8449*100000000000000^6401 ≤ 13367796043391^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088601749 5000000000 13367796043391 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658290933/1250000000 : ℝ)^8449 ≤ (21447382757697/50000000000000 : ℝ)^6401 := by
    have hnat : (658290933 : ℕ)^8449*50000000000000^6401 ≤ 21447382757697^6401*1250000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658290933 1250000000 21447382757697 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344522321/10000000000 : ℝ), (-1088601749/5000000000 : ℝ), (658290933/1250000000 : ℝ)] ![(10934359606967/25000000000000 : ℝ), (13367796043391/100000000000000 : ℝ), (21447382757697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344522321/10000000000 : ℝ)|^8449 ≤ (10934359606967/25000000000000 : ℝ)^6401
        have hw : |(5344522321/10000000000 : ℝ)|=(5344522321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1088601749/5000000000 : ℝ)|^8449 ≤ (13367796043391/100000000000000 : ℝ)^6401
        have hw : |(-1088601749/5000000000 : ℝ)|=(1088601749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658290933/1250000000 : ℝ)|^8449 ≤ (21447382757697/50000000000000 : ℝ)^6401
        have hw : |(658290933/1250000000 : ℝ)|=(658290933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s5_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267226137/500000000 : ℝ)*x 0 + (526632737/1000000000 : ℝ)*x 1 + (-272150383/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267226137/500000000 : ℝ)^8449 ≤ (43737442953883/100000000000000 : ℝ)^6401 := by
    have hnat : (267226137 : ℕ)^8449*100000000000000^6401 ≤ 43737442953883^6401*500000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267226137 500000000 43737442953883 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526632737/1000000000 : ℝ)^8449 ≤ (10723691126197/25000000000000 : ℝ)^6401 := by
    have hnat : (526632737 : ℕ)^8449*25000000000000^6401 ≤ 10723691126197^6401*1000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526632737 1000000000 10723691126197 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272150383/1250000000 : ℝ)^8449 ≤ (6683896263051/50000000000000 : ℝ)^6401 := by
    have hnat : (272150383 : ℕ)^8449*50000000000000^6401 ≤ 6683896263051^6401*1250000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272150383 1250000000 6683896263051 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267226137/500000000 : ℝ), (526632737/1000000000 : ℝ), (-272150383/1250000000 : ℝ)] ![(43737442953883/100000000000000 : ℝ), (10723691126197/25000000000000 : ℝ), (6683896263051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267226137/500000000 : ℝ)|^8449 ≤ (43737442953883/100000000000000 : ℝ)^6401
        have hw : |(267226137/500000000 : ℝ)|=(267226137/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526632737/1000000000 : ℝ)|^8449 ≤ (10723691126197/25000000000000 : ℝ)^6401
        have hw : |(526632737/1000000000 : ℝ)|=(526632737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272150383/1250000000 : ℝ)|^8449 ≤ (6683896263051/50000000000000 : ℝ)^6401
        have hw : |(-272150383/1250000000 : ℝ)|=(272150383/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s5_3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (869760089/2000000000 : ℝ)*x 0 + (844547299/2000000000 : ℝ)*x 1 + (895701777/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869760089/2000000000 : ℝ)^8449 ≤ (33316992543373/100000000000000 : ℝ)^6401 := by
    have hnat : (869760089 : ℕ)^8449*100000000000000^6401 ≤ 33316992543373^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869760089 2000000000 33316992543373 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844547299/2000000000 : ℝ)^8449 ≤ (8012033967259/25000000000000 : ℝ)^6401 := by
    have hnat : (844547299 : ℕ)^8449*25000000000000^6401 ≤ 8012033967259^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844547299 2000000000 8012033967259 25000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (895701777/2000000000 : ℝ)^8449 ≤ (6926974314741/20000000000000 : ℝ)^6401 := by
    have hnat : (895701777 : ℕ)^8449*20000000000000^6401 ≤ 6926974314741^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895701777 2000000000 6926974314741 20000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869760089/2000000000 : ℝ), (844547299/2000000000 : ℝ), (895701777/2000000000 : ℝ)] ![(33316992543373/100000000000000 : ℝ), (8012033967259/25000000000000 : ℝ), (6926974314741/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869760089/2000000000 : ℝ)|^8449 ≤ (33316992543373/100000000000000 : ℝ)^6401
        have hw : |(869760089/2000000000 : ℝ)|=(869760089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(844547299/2000000000 : ℝ)|^8449 ≤ (8012033967259/25000000000000 : ℝ)^6401
        have hw : |(844547299/2000000000 : ℝ)|=(844547299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(895701777/2000000000 : ℝ)|^8449 ≤ (6926974314741/20000000000000 : ℝ)^6401
        have hw : |(895701777/2000000000 : ℝ)|=(895701777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s5_4 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056719791/5000000000 : ℝ)*x 0 + (5266650417/10000000000 : ℝ)*x 1 + (1347937157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056719791/5000000000 : ℝ)^8449 ≤ (6426734138031/50000000000000 : ℝ)^6401 := by
    have hnat : (1056719791 : ℕ)^8449*50000000000000^6401 ≤ 6426734138031^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056719791 5000000000 6426734138031 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266650417/10000000000 : ℝ)^8449 ≤ (42898237657603/100000000000000 : ℝ)^6401 := by
    have hnat : (5266650417 : ℕ)^8449*100000000000000^6401 ≤ 42898237657603^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266650417 10000000000 42898237657603 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347937157/2500000000 : ℝ)^8449 ≤ (44248294053733/100000000000000 : ℝ)^6401 := by
    have hnat : (1347937157 : ℕ)^8449*100000000000000^6401 ≤ 44248294053733^6401*2500000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347937157 2500000000 44248294053733 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056719791/5000000000 : ℝ), (5266650417/10000000000 : ℝ), (1347937157/2500000000 : ℝ)] ![(6426734138031/50000000000000 : ℝ), (42898237657603/100000000000000 : ℝ), (44248294053733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056719791/5000000000 : ℝ)|^8449 ≤ (6426734138031/50000000000000 : ℝ)^6401
        have hw : |(-1056719791/5000000000 : ℝ)|=(1056719791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266650417/10000000000 : ℝ)|^8449 ≤ (42898237657603/100000000000000 : ℝ)^6401
        have hw : |(5266650417/10000000000 : ℝ)|=(5266650417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347937157/2500000000 : ℝ)|^8449 ≤ (44248294053733/100000000000000 : ℝ)^6401
        have hw : |(1347937157/2500000000 : ℝ)|=(1347937157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s5_5 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062481623/2000000000 : ℝ)*x 0 + (-1025891039/5000000000 : ℝ)*x 1 + (1347937157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062481623/2000000000 : ℝ)^8449 ≤ (21695438238453/50000000000000 : ℝ)^6401 := by
    have hnat : (1062481623 : ℕ)^8449*50000000000000^6401 ≤ 21695438238453^6401*2000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062481623 2000000000 21695438238453 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025891039/5000000000 : ℝ)^8449 ≤ (12360829451973/100000000000000 : ℝ)^6401 := by
    have hnat : (1025891039 : ℕ)^8449*100000000000000^6401 ≤ 12360829451973^6401*5000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025891039 5000000000 12360829451973 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347937157/2500000000 : ℝ)^8449 ≤ (44248294053733/100000000000000 : ℝ)^6401 := by
    have hnat : (1347937157 : ℕ)^8449*100000000000000^6401 ≤ 44248294053733^6401*2500000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347937157 2500000000 44248294053733 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062481623/2000000000 : ℝ), (-1025891039/5000000000 : ℝ), (1347937157/2500000000 : ℝ)] ![(21695438238453/50000000000000 : ℝ), (12360829451973/100000000000000 : ℝ), (44248294053733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062481623/2000000000 : ℝ)|^8449 ≤ (21695438238453/50000000000000 : ℝ)^6401
        have hw : |(1062481623/2000000000 : ℝ)|=(1062481623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1025891039/5000000000 : ℝ)|^8449 ≤ (12360829451973/100000000000000 : ℝ)^6401
        have hw : |(-1025891039/5000000000 : ℝ)|=(1025891039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347937157/2500000000 : ℝ)|^8449 ≤ (44248294053733/100000000000000 : ℝ)^6401
        have hw : |(1347937157/2500000000 : ℝ)|=(1347937157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s5_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (332025507/625000000 : ℝ)*x 0 + (5391748631/10000000000 : ℝ)*x 1 + (-2051782079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332025507/625000000 : ℝ)^8449 ≤ (21695438222281/50000000000000 : ℝ)^6401 := by
    have hnat : (332025507 : ℕ)^8449*50000000000000^6401 ≤ 21695438222281^6401*625000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332025507 625000000 21695438222281 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391748631/10000000000 : ℝ)^8449 ≤ (4424829408623/10000000000000 : ℝ)^6401 := by
    have hnat : (5391748631 : ℕ)^8449*10000000000000^6401 ≤ 4424829408623^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391748631 10000000000 4424829408623 10000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2051782079/10000000000 : ℝ)^8449 ≤ (494433178397/4000000000000 : ℝ)^6401 := by
    have hnat : (2051782079 : ℕ)^8449*4000000000000^6401 ≤ 494433178397^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051782079 10000000000 494433178397 4000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332025507/625000000 : ℝ), (5391748631/10000000000 : ℝ), (-2051782079/10000000000 : ℝ)] ![(21695438222281/50000000000000 : ℝ), (4424829408623/10000000000000 : ℝ), (494433178397/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332025507/625000000 : ℝ)|^8449 ≤ (21695438222281/50000000000000 : ℝ)^6401
        have hw : |(332025507/625000000 : ℝ)|=(332025507/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391748631/10000000000 : ℝ)|^8449 ≤ (4424829408623/10000000000000 : ℝ)^6401
        have hw : |(5391748631/10000000000 : ℝ)|=(5391748631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2051782079/10000000000 : ℝ)|^8449 ≤ (494433178397/4000000000000 : ℝ)^6401
        have hw : |(-2051782079/10000000000 : ℝ)|=(2051782079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1256_s5_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348810339/10000000000 : ℝ)*x 0 + (111946307/250000000 : ℝ)*x 1 + (4223395551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348810339/10000000000 : ℝ)^8449 ≤ (520579571803/1562500000000 : ℝ)^6401 := by
    have hnat : (4348810339 : ℕ)^8449*1562500000000^6401 ≤ 520579571803^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348810339 10000000000 520579571803 1562500000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111946307/250000000 : ℝ)^8449 ≤ (17314084576973/50000000000000 : ℝ)^6401 := by
    have hnat : (111946307 : ℕ)^8449*50000000000000^6401 ≤ 17314084576973^6401*250000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111946307 250000000 17314084576973 50000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4223395551/10000000000 : ℝ)^8449 ≤ (32054738232601/100000000000000 : ℝ)^6401 := by
    have hnat : (4223395551 : ℕ)^8449*100000000000000^6401 ≤ 32054738232601^6401*10000000000^8449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223395551 10000000000 32054738232601 100000000000000 8449 6401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8449/2048 : ℝ)) 8449 6401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348810339/10000000000 : ℝ), (111946307/250000000 : ℝ), (4223395551/10000000000 : ℝ)] ![(520579571803/1562500000000 : ℝ), (17314084576973/50000000000000 : ℝ), (32054738232601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348810339/10000000000 : ℝ)|^8449 ≤ (520579571803/1562500000000 : ℝ)^6401
        have hw : |(4348810339/10000000000 : ℝ)|=(4348810339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(111946307/250000000 : ℝ)|^8449 ≤ (17314084576973/50000000000000 : ℝ)^6401
        have hw : |(111946307/250000000 : ℝ)|=(111946307/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4223395551/10000000000 : ℝ)|^8449 ≤ (32054738232601/100000000000000 : ℝ)^6401
        have hw : |(4223395551/10000000000 : ℝ)|=(4223395551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1256_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h) :
    (717/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1767/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (91/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (91/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (91/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (91/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (91/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (91/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (91/800 : ℝ) ^ (33/8 : ℝ) ≤ (797406119683447/6250000000000000000 : ℝ) := by
    have hpowers : (91/800 : ℝ)^33 ≤ (797406119683447/6250000000000000000 : ℝ)^8 := by
      have hnat : (91 : ℕ)^33*6250000000000000000^8 ≤ 797406119683447^8*800^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91 800 797406119683447 6250000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91/800 : ℝ)) (X := (797406119683447/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hpowhi : (7119/50000 : ℝ) ^ (33/8 : ℝ) ≤ (3220898788069129/10000000000000000000 : ℝ) := by
    have hpowers : (7119/50000 : ℝ)^33 ≤ (3220898788069129/10000000000000000000 : ℝ)^8 := by
      have hnat : (7119 : ℕ)^33*10000000000000000000^8 ≤ 3220898788069129^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7119 50000 3220898788069129 10000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7119/50000 : ℝ)) (X := (3220898788069129/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125797406119683447/3125000000000000000 : ℝ) ≤ (1250077316757109/1250000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3125797406119683447/3125000000000000000 : ℝ)^8 ≤ (1250077316757109/1250000000000000 : ℝ)^33 := by
      have hnat : (3125797406119683447 : ℕ)^8*1250000000000000^33 ≤ 1250077316757109^33*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125797406119683447 3125000000000000000 1250077316757109 1250000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250077316757109/1250000000000000 : ℝ)) (X := (3125797406119683447/3125000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022483742897813221/50000000000000000000 : ℝ) ≤ (10001089935234877/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (50022483742897813221/50000000000000000000 : ℝ)^8 ≤ (10001089935234877/10000000000000000 : ℝ)^33 := by
      have hnat : (50022483742897813221 : ℕ)^8*10000000000000000^33 ≤ 10001089935234877^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022483742897813221 50000000000000000000 10001089935234877 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001089935234877/10000000000000000 : ℝ)) (X := (50022483742897813221/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003220898788069129/5000000000000000000 : ℝ) ≤ (5000780668206441/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (5003220898788069129/5000000000000000000 : ℝ)^8 ≤ (5000780668206441/5000000000000000 : ℝ)^33 := by
      have hnat : (5003220898788069129 : ℕ)^8*5000000000000000^33 ≤ 5000780668206441^33*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003220898788069129 5000000000000000000 5000780668206441 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000780668206441/5000000000000000 : ℝ)) (X := (5003220898788069129/5000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(797406119683447/6250000000000000000 : ℝ) ≤ ((2044360463300372199/2045000000000000000 : ℝ)+2*(94280235601/57260000000000 : ℝ)*(91/800 : ℝ))^(33/8 : ℝ) := by
    rw [show (2044360463300372199/2045000000000000000 : ℝ)+2*(94280235601/57260000000000 : ℝ)*(91/800 : ℝ)=(1250077316757109/1250000000000000 : ℝ) by norm_num, show 1+2*(797406119683447/6250000000000000000 : ℝ)=(3125797406119683447/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3220898788069129/10000000000000000000 : ℝ)+(797406119683447/6250000000000000000 : ℝ) ≤ ((2044360463300372199/2045000000000000000 : ℝ)+(94280235601/57260000000000 : ℝ)*((7119/50000 : ℝ)+(91/800 : ℝ)))^(33/8 : ℝ) := by
    rw [show (2044360463300372199/2045000000000000000 : ℝ)+(94280235601/57260000000000 : ℝ)*((7119/50000 : ℝ)+(91/800 : ℝ))=(10001089935234877/10000000000000000 : ℝ) by norm_num, show 1+(3220898788069129/10000000000000000000 : ℝ)+(797406119683447/6250000000000000000 : ℝ)=(50022483742897813221/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3220898788069129/10000000000000000000 : ℝ) ≤ ((2044360463300372199/2045000000000000000 : ℝ)+2*(94280235601/57260000000000 : ℝ)*(7119/50000 : ℝ))^(33/8 : ℝ) := by
    rw [show (2044360463300372199/2045000000000000000 : ℝ)+2*(94280235601/57260000000000 : ℝ)*(7119/50000 : ℝ)=(5000780668206441/5000000000000000 : ℝ) by norm_num, show 1+2*(3220898788069129/10000000000000000000 : ℝ)=(5003220898788069129/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2044360463300372199/2045000000000000000 : ℝ)*(X 1 0+X 2 0)+(94280235601/57260000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (91/800 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (2044360463300372199/2045000000000000000 : ℝ)) (alpha := (94280235601/57260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2044360463300372199/2045000000000000000 : ℝ)*(X 0 1+X 2 1)+(94280235601/57260000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (91/800 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (2044360463300372199/2045000000000000000 : ℝ)) (alpha := (94280235601/57260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2044360463300372199/2045000000000000000 : ℝ)*(X 0 2+X 1 2)+(94280235601/57260000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (33/8 : ℝ)) (lo := (91/800 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (2044360463300372199/2045000000000000000 : ℝ)) (alpha := (94280235601/57260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-42268693/200000000 : ℝ)*X 0 0+(2696036423/5000000000 : ℝ)*X 0 1+(5266327431/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344522321/10000000000 : ℝ)*X 1 0+(-1088601749/5000000000 : ℝ)*X 1 1+(658290933/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267226137/500000000 : ℝ)*X 2 0+(526632737/1000000000 : ℝ)*X 2 1+(-272150383/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((869760089/2000000000 : ℝ)*X 0 0+(844547299/2000000000 : ℝ)*X 0 1+(895701777/2000000000 : ℝ)*X 0 2+(869760089/2000000000 : ℝ)*X 1 0+(844547299/2000000000 : ℝ)*X 1 1+(895701777/2000000000 : ℝ)*X 1 2+(869760089/2000000000 : ℝ)*X 2 0+(844547299/2000000000 : ℝ)*X 2 1+(895701777/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1056719791/5000000000 : ℝ)*X 0 0+(5266650417/10000000000 : ℝ)*X 0 1+(1347937157/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062481623/2000000000 : ℝ)*X 1 0+(-1025891039/5000000000 : ℝ)*X 1 1+(1347937157/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((332025507/625000000 : ℝ)*X 2 0+(5391748631/10000000000 : ℝ)*X 2 1+(-2051782079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4348810339/10000000000 : ℝ)*X 0 0+(111946307/250000000 : ℝ)*X 0 1+(4223395551/10000000000 : ℝ)*X 0 2+(4348810339/10000000000 : ℝ)*X 1 0+(111946307/250000000 : ℝ)*X 1 1+(4223395551/10000000000 : ℝ)*X 1 2+(4348810339/10000000000 : ℝ)*X 2 0+(111946307/250000000 : ℝ)*X 2 1+(4223395551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1256_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (136690904559014027918356281/17893750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1118333181/100000000000000 : ℝ)*(base19) + (163912909/10000000000000 : ℝ)*(base23) + (21295383/20000000000000 : ℝ)*(lower2) + (279107961/100000000000000 : ℝ)*(upper5) + (5931216894970439/100000000000000 : ℝ)*(major0) + (5931216894970439/100000000000000 : ℝ)*(major1) + (148280422374261/2500000000000 : ℝ)*(major2) + (795261173864443/10000000000000 : ℝ)*(sp0) + (3976327460560971/50000000000000 : ℝ)*(sp1) + (318106818726203/4000000000000 : ℝ)*(sp2) + (1954872086727007/50000000000000 : ℝ)*(sp3) + (7546079967/12500000000000 : ℝ)*(sp4) + (16067829043/100000000000000 : ℝ)*(sp5) + (17254568331/100000000000000 : ℝ)*(sp7) + (1954880714011173/50000000000000 : ℝ)*(f.failure) + (1590534421456833/20000000000000 : ℝ)*(f.sum) + (3724558407883/5726000000000000000000000000 : ℝ)*base66 + (10410218709586022473/1431500000000000000000000000000000 : ℝ)*base68 + (443783408814895823/35787500000000000000000000000000 : ℝ)*base69 + (12492705450802022473/1431500000000000000000000000000000 : ℝ)*base72 + (34348414065639/5726000000000000000000000000 : ℝ)*base73 + (117659917888620823/35787500000000000000000000000000 : ℝ)*base75 + (12769519791648227527/1431500000000000000000000000000000 : ℝ)*base77 + (52985118220986727527/1431500000000000000000000000000000 : ℝ)*base79 + (1137313950933/1431500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (87194459/5000000000000000000000 : ℝ)*base89 + (87194459/5000000000000000000000 : ℝ)*base91 + (37194459/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (298476556973551284825068907/44734375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1203823501/100000000000000 : ℝ)*(base19) + (51993979/4000000000000 : ℝ)*(base23) + (16982851/12500000000000 : ℝ)*(upper3) + (45732007/100000000000000 : ℝ)*(lower4) + (68154607/50000000000000 : ℝ)*(upper5) + (372614349084671/6250000000000 : ℝ)*(major0) + (372614349084671/6250000000000 : ℝ)*(major1) + (372614349084671/6250000000000 : ℝ)*(major2) + (33398615257/100000000000000 : ℝ)*(sp1) + (7157861271/20000000000000 : ℝ)*(sp2) + (7993718134128957/100000000000000 : ℝ)*(sp4) + (7993683531690199/100000000000000 : ℝ)*(sp5) + (7993681044973127/100000000000000 : ℝ)*(sp6) + (3929940814173947/100000000000000 : ℝ)*(sp7) + (3929940814173947/100000000000000 : ℝ)*(f.failure) + (7993718134128957/100000000000000 : ℝ)*(f.sum) + (6923409918581/2863000000000000000000000000 : ℝ)*base66 + (614883523625136953/89468750000000000000000000000000 : ℝ)*base67 + (948328494164761953/89468750000000000000000000000000 : ℝ)*base69 + (557330049483949453/89468750000000000000000000000000 : ℝ)*base71 + (59249882417/143150000000000000000000000 : ℝ)*base74 + (716505489063738047/89468750000000000000000000000000 : ℝ)*base76 + (68866234554386953/89468750000000000000000000000000 : ℝ)*base77 + (1127570737789699453/89468750000000000000000000000000 : ℝ)*base79 + (5210358617341/715750000000000000000000000 : ℝ)*base81 + (5994501/10000000000000000000000 : ℝ)*base89 + (5994501/10000000000000000000000 : ℝ)*base91 + (5994501/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1256_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (91/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (717/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1767/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1256_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1256_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16187/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2389/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (717/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1767/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1256_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1256_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1256_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151702783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16187/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2389/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (717/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1767/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1256_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
