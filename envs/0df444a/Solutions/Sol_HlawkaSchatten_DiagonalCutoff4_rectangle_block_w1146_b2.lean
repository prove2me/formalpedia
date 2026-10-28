-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1146_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:33:38.712231+00:00
-- url     : https://prove2.me/submissions/b670975c-af42-4fe6-bbcc-26ed44c71689

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
theorem support_rectangle_w1146_s6_0 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2164946769/10000000000 : ℝ)*x 0 + (168540577/312500000 : ℝ)*x 1 + (5265485311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164946769/10000000000 : ℝ)^8339 ≤ (13155451818753/100000000000000 : ℝ)^6291 := by
    have hnat : (2164946769 : ℕ)^8339*100000000000000^6291 ≤ 13155451818753^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164946769 10000000000 13155451818753 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168540577/312500000 : ℝ)^8339 ≤ (11028112177551/25000000000000 : ℝ)^6291 := by
    have hnat : (168540577 : ℕ)^8339*25000000000000^6291 ≤ 11028112177551^6291*312500000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168540577 312500000 11028112177551 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265485311/10000000000 : ℝ)^8339 ≤ (42732099453531/100000000000000 : ℝ)^6291 := by
    have hnat : (5265485311 : ℕ)^8339*100000000000000^6291 ≤ 42732099453531^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265485311 10000000000 42732099453531 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2164946769/10000000000 : ℝ), (168540577/312500000 : ℝ), (5265485311/10000000000 : ℝ)] ![(13155451818753/100000000000000 : ℝ), (11028112177551/25000000000000 : ℝ), (42732099453531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2164946769/10000000000 : ℝ)|^8339 ≤ (13155451818753/100000000000000 : ℝ)^6291
        have hw : |(-2164946769/10000000000 : ℝ)|=(2164946769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168540577/312500000 : ℝ)|^8339 ≤ (11028112177551/25000000000000 : ℝ)^6291
        have hw : |(168540577/312500000 : ℝ)|=(168540577/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265485311/10000000000 : ℝ)|^8339 ≤ (42732099453531/100000000000000 : ℝ)^6291
        have hw : |(5265485311/10000000000 : ℝ)|=(5265485311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s6_1 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668103447/1250000000 : ℝ)*x 0 + (-557444873/2500000000 : ℝ)*x 1 + (5265485311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668103447/1250000000 : ℝ)^8339 ≤ (10896926956407/25000000000000 : ℝ)^6291 := by
    have hnat : (668103447 : ℕ)^8339*25000000000000^6291 ≤ 10896926956407^6291*1250000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668103447 1250000000 10896926956407 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (557444873/2500000000 : ℝ)^8339 ≤ (13680192700343/100000000000000 : ℝ)^6291 := by
    have hnat : (557444873 : ℕ)^8339*100000000000000^6291 ≤ 13680192700343^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557444873 2500000000 13680192700343 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265485311/10000000000 : ℝ)^8339 ≤ (42732099453531/100000000000000 : ℝ)^6291 := by
    have hnat : (5265485311 : ℕ)^8339*100000000000000^6291 ≤ 42732099453531^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265485311 10000000000 42732099453531 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668103447/1250000000 : ℝ), (-557444873/2500000000 : ℝ), (5265485311/10000000000 : ℝ)] ![(10896926956407/25000000000000 : ℝ), (13680192700343/100000000000000 : ℝ), (42732099453531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668103447/1250000000 : ℝ)|^8339 ≤ (10896926956407/25000000000000 : ℝ)^6291
        have hw : |(668103447/1250000000 : ℝ)|=(668103447/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-557444873/2500000000 : ℝ)|^8339 ≤ (13680192700343/100000000000000 : ℝ)^6291
        have hw : |(-557444873/2500000000 : ℝ)|=(557444873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265485311/10000000000 : ℝ)|^8339 ≤ (42732099453531/100000000000000 : ℝ)^6291
        have hw : |(5265485311/10000000000 : ℝ)|=(5265485311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s6_2 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336206887/2500000000 : ℝ)*x 0 + (2632742667/5000000000 : ℝ)*x 1 + (-4459559/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336206887/2500000000 : ℝ)^8339 ≤ (43587707522949/100000000000000 : ℝ)^6291 := by
    have hnat : (1336206887 : ℕ)^8339*100000000000000^6291 ≤ 43587707522949^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336206887 2500000000 43587707522949 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632742667/5000000000 : ℝ)^8339 ≤ (42732099700953/100000000000000 : ℝ)^6291 := by
    have hnat : (2632742667 : ℕ)^8339*100000000000000^6291 ≤ 42732099700953^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632742667 5000000000 42732099700953 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4459559/20000000 : ℝ)^8339 ≤ (13680192765403/100000000000000 : ℝ)^6291 := by
    have hnat : (4459559 : ℕ)^8339*100000000000000^6291 ≤ 13680192765403^6291*20000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4459559 20000000 13680192765403 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336206887/2500000000 : ℝ), (2632742667/5000000000 : ℝ), (-4459559/20000000 : ℝ)] ![(43587707522949/100000000000000 : ℝ), (42732099700953/100000000000000 : ℝ), (13680192765403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336206887/2500000000 : ℝ)|^8339 ≤ (43587707522949/100000000000000 : ℝ)^6291
        have hw : |(1336206887/2500000000 : ℝ)|=(1336206887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632742667/5000000000 : ℝ)|^8339 ≤ (42732099700953/100000000000000 : ℝ)^6291
        have hw : |(2632742667/5000000000 : ℝ)|=(2632742667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4459559/20000000 : ℝ)|^8339 ≤ (13680192765403/100000000000000 : ℝ)^6291
        have hw : |(-4459559/20000000 : ℝ)|=(4459559/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s6_3 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2182046621/5000000000 : ℝ)*x 0 + (4238697061/10000000000 : ℝ)*x 1 + (4493177521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182046621/5000000000 : ℝ)^8339 ≤ (33316818726977/100000000000000 : ℝ)^6291 := by
    have hnat : (2182046621 : ℕ)^8339*100000000000000^6291 ≤ 33316818726977^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182046621 5000000000 33316818726977 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4238697061/10000000000 : ℝ)^8339 ≤ (32053832006497/100000000000000 : ℝ)^6291 := by
    have hnat : (4238697061 : ℕ)^8339*100000000000000^6291 ≤ 32053832006497^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238697061 10000000000 32053832006497 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493177521/10000000000 : ℝ)^8339 ≤ (34629349248603/100000000000000 : ℝ)^6291 := by
    have hnat : (4493177521 : ℕ)^8339*100000000000000^6291 ≤ 34629349248603^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493177521 10000000000 34629349248603 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182046621/5000000000 : ℝ), (4238697061/10000000000 : ℝ), (4493177521/10000000000 : ℝ)] ![(33316818726977/100000000000000 : ℝ), (32053832006497/100000000000000 : ℝ), (34629349248603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182046621/5000000000 : ℝ)|^8339 ≤ (33316818726977/100000000000000 : ℝ)^6291
        have hw : |(2182046621/5000000000 : ℝ)|=(2182046621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4238697061/10000000000 : ℝ)|^8339 ≤ (32053832006497/100000000000000 : ℝ)^6291
        have hw : |(4238697061/10000000000 : ℝ)|=(4238697061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493177521/10000000000 : ℝ)|^8339 ≤ (34629349248603/100000000000000 : ℝ)^6291
        have hw : |(4493177521/10000000000 : ℝ)|=(4493177521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s6_4 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2164951763/10000000000 : ℝ)*x 0 + (1316452021/2500000000 : ℝ)*x 1 + (1078594897/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164951763/10000000000 : ℝ)^8339 ≤ (13155492044261/100000000000000 : ℝ)^6291 := by
    have hnat : (2164951763 : ℕ)^8339*100000000000000^6291 ≤ 13155492044261^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164951763 10000000000 13155492044261 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316452021/2500000000 : ℝ)^8339 ≤ (13354866159/31250000000 : ℝ)^6291 := by
    have hnat : (1316452021 : ℕ)^8339*31250000000^6291 ≤ 13354866159^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316452021 2500000000 13354866159 31250000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078594897/2000000000 : ℝ)^8339 ≤ (44108936232191/100000000000000 : ℝ)^6291 := by
    have hnat : (1078594897 : ℕ)^8339*100000000000000^6291 ≤ 44108936232191^6291*2000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078594897 2000000000 44108936232191 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2164951763/10000000000 : ℝ), (1316452021/2500000000 : ℝ), (1078594897/2000000000 : ℝ)] ![(13155492044261/100000000000000 : ℝ), (13354866159/31250000000 : ℝ), (44108936232191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2164951763/10000000000 : ℝ)|^8339 ≤ (13155492044261/100000000000000 : ℝ)^6291
        have hw : |(-2164951763/10000000000 : ℝ)|=(2164951763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316452021/2500000000 : ℝ)|^8339 ≤ (13354866159/31250000000 : ℝ)^6291
        have hw : |(1316452021/2500000000 : ℝ)|=(1316452021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078594897/2000000000 : ℝ)|^8339 ≤ (44108936232191/100000000000000 : ℝ)^6291
        have hw : |(1078594897/2000000000 : ℝ)|=(1078594897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s6_5 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328109001/2500000000 : ℝ)*x 0 + (-2102290397/10000000000 : ℝ)*x 1 + (168530451/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328109001/2500000000 : ℝ)^8339 ≤ (2161895084001/5000000000000 : ℝ)^6291 := by
    have hnat : (1328109001 : ℕ)^8339*5000000000000^6291 ≤ 2161895084001^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328109001 2500000000 2161895084001 5000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2102290397/10000000000 : ℝ)^8339 ≤ (12653162649579/100000000000000 : ℝ)^6291 := by
    have hnat : (2102290397 : ℕ)^8339*100000000000000^6291 ≤ 12653162649579^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102290397 10000000000 12653162649579 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168530451/312500000 : ℝ)^8339 ≤ (11027233914397/25000000000000 : ℝ)^6291 := by
    have hnat : (168530451 : ℕ)^8339*25000000000000^6291 ≤ 11027233914397^6291*312500000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168530451 312500000 11027233914397 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328109001/2500000000 : ℝ), (-2102290397/10000000000 : ℝ), (168530451/312500000 : ℝ)] ![(2161895084001/5000000000000 : ℝ), (12653162649579/100000000000000 : ℝ), (11027233914397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328109001/2500000000 : ℝ)|^8339 ≤ (2161895084001/5000000000000 : ℝ)^6291
        have hw : |(1328109001/2500000000 : ℝ)|=(1328109001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2102290397/10000000000 : ℝ)|^8339 ≤ (12653162649579/100000000000000 : ℝ)^6291
        have hw : |(-2102290397/10000000000 : ℝ)|=(2102290397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168530451/312500000 : ℝ)|^8339 ≤ (11027233914397/25000000000000 : ℝ)^6291
        have hw : |(168530451/312500000 : ℝ)|=(168530451/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s6_6 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (83006813/156250000 : ℝ)*x 0 + (5392974379/10000000000 : ℝ)*x 1 + (-2102290431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83006813/156250000 : ℝ)^8339 ≤ (43237901982101/100000000000000 : ℝ)^6291 := by
    have hnat : (83006813 : ℕ)^8339*100000000000000^6291 ≤ 43237901982101^6291*156250000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83006813 156250000 43237901982101 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392974379/10000000000 : ℝ)^8339 ≤ (5513616885373/12500000000000 : ℝ)^6291 := by
    have hnat : (5392974379 : ℕ)^8339*12500000000000^6291 ≤ 5513616885373^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392974379 10000000000 5513616885373 12500000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2102290431/10000000000 : ℝ)^8339 ≤ (2530632584167/20000000000000 : ℝ)^6291 := by
    have hnat : (2102290431 : ℕ)^8339*20000000000000^6291 ≤ 2530632584167^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102290431 10000000000 2530632584167 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83006813/156250000 : ℝ), (5392974379/10000000000 : ℝ), (-2102290431/10000000000 : ℝ)] ![(43237901982101/100000000000000 : ℝ), (5513616885373/12500000000000 : ℝ), (2530632584167/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83006813/156250000 : ℝ)|^8339 ≤ (43237901982101/100000000000000 : ℝ)^6291
        have hw : |(83006813/156250000 : ℝ)|=(83006813/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392974379/10000000000 : ℝ)|^8339 ≤ (5513616885373/12500000000000 : ℝ)^6291
        have hw : |(5392974379/10000000000 : ℝ)|=(5392974379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2102290431/10000000000 : ℝ)|^8339 ≤ (2530632584167/20000000000000 : ℝ)^6291
        have hw : |(-2102290431/10000000000 : ℝ)|=(2102290431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s6_7 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2182051517/5000000000 : ℝ)*x 0 + (1123133701/2500000000 : ℝ)*x 1 + (2119671089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182051517/5000000000 : ℝ)^8339 ≤ (16658458909119/50000000000000 : ℝ)^6291 := by
    have hnat : (2182051517 : ℕ)^8339*50000000000000^6291 ≤ 16658458909119^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182051517 5000000000 16658458909119 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123133701/2500000000 : ℝ)^8339 ≤ (17311391670881/50000000000000 : ℝ)^6291 := by
    have hnat : (1123133701 : ℕ)^8339*50000000000000^6291 ≤ 17311391670881^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123133701 2500000000 17311391670881 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119671089/5000000000 : ℝ)^8339 ≤ (16030149415769/50000000000000 : ℝ)^6291 := by
    have hnat : (2119671089 : ℕ)^8339*50000000000000^6291 ≤ 16030149415769^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119671089 5000000000 16030149415769 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182051517/5000000000 : ℝ), (1123133701/2500000000 : ℝ), (2119671089/5000000000 : ℝ)] ![(16658458909119/50000000000000 : ℝ), (17311391670881/50000000000000 : ℝ), (16030149415769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182051517/5000000000 : ℝ)|^8339 ≤ (16658458909119/50000000000000 : ℝ)^6291
        have hw : |(2182051517/5000000000 : ℝ)|=(2182051517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123133701/2500000000 : ℝ)|^8339 ≤ (17311391670881/50000000000000 : ℝ)^6291
        have hw : |(1123133701/2500000000 : ℝ)|=(1123133701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2119671089/5000000000 : ℝ)|^8339 ≤ (16030149415769/50000000000000 : ℝ)^6291
        have hw : |(2119671089/5000000000 : ℝ)|=(2119671089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1146_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11351/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14059/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1409/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11321/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11321/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11321/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11321/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11321/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11321/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11321/100000 : ℝ) ^ (4169/1024 : ℝ) ≤ (14063437753008211/100000000000000000000 : ℝ) := by
    have hpowers : (11321/100000 : ℝ)^4169 ≤ (14063437753008211/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11321 : ℕ)^4169*100000000000000000000^1024 ≤ 14063437753008211^1024*100000^4169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11321 100000 14063437753008211 100000000000000000000 4169 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11321/100000 : ℝ)) (X := (14063437753008211/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1409/10000 : ℝ) ^ (4169/1024 : ℝ) ≤ (34274461097048197/100000000000000000000 : ℝ) := by
    have hpowers : (1409/10000 : ℝ)^4169 ≤ (34274461097048197/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1409 : ℕ)^4169*100000000000000000000^1024 ≤ 34274461097048197^1024*10000^4169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409 10000 34274461097048197 100000000000000000000 4169 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1409/10000 : ℝ)) (X := (34274461097048197/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014063437753008211/50000000000000000000 : ℝ) ≤ (10000690785929099/10000000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (50014063437753008211/50000000000000000000 : ℝ)^1024 ≤ (10000690785929099/10000000000000000 : ℝ)^4169 := by
      have hnat : (50014063437753008211 : ℕ)^1024*10000000000000000^4169 ≤ 10000690785929099^4169*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014063437753008211 50000000000000000000 10000690785929099 10000000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000690785929099/10000000000000000 : ℝ)) (X := (50014063437753008211/50000000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506042237356257051/12500000000000000000 : ℝ) ≤ (5000593535455049/5000000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (12506042237356257051/12500000000000000000 : ℝ)^1024 ≤ (5000593535455049/5000000000000000 : ℝ)^4169 := by
      have hnat : (12506042237356257051 : ℕ)^1024*5000000000000000^4169 ≤ 5000593535455049^4169*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506042237356257051 12500000000000000000 5000593535455049 5000000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000593535455049/5000000000000000 : ℝ)) (X := (12506042237356257051/12500000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034274461097048197/50000000000000000000 : ℝ) ≤ (10001683355891097/10000000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (50034274461097048197/50000000000000000000 : ℝ)^1024 ≤ (10001683355891097/10000000000000000 : ℝ)^4169 := by
      have hnat : (50034274461097048197 : ℕ)^1024*10000000000000000^4169 ≤ 10001683355891097^4169*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034274461097048197 50000000000000000000 10001683355891097 10000000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001683355891097/10000000000000000 : ℝ)) (X := (50034274461097048197/50000000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14063437753008211/100000000000000000000 : ℝ) ≤ ((27680675901697895773/27690000000000000000 : ℝ)+2*(496284980999/276900000000000 : ℝ)*(11321/100000 : ℝ))^(4169/1024 : ℝ) := by
    rw [show (27680675901697895773/27690000000000000000 : ℝ)+2*(496284980999/276900000000000 : ℝ)*(11321/100000 : ℝ)=(10000690785929099/10000000000000000 : ℝ) by norm_num, show 1+2*(14063437753008211/100000000000000000000 : ℝ)=(50014063437753008211/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34274461097048197/100000000000000000000 : ℝ)+(14063437753008211/100000000000000000000 : ℝ) ≤ ((27680675901697895773/27690000000000000000 : ℝ)+(496284980999/276900000000000 : ℝ)*((1409/10000 : ℝ)+(11321/100000 : ℝ)))^(4169/1024 : ℝ) := by
    rw [show (27680675901697895773/27690000000000000000 : ℝ)+(496284980999/276900000000000 : ℝ)*((1409/10000 : ℝ)+(11321/100000 : ℝ))=(5000593535455049/5000000000000000 : ℝ) by norm_num, show 1+(34274461097048197/100000000000000000000 : ℝ)+(14063437753008211/100000000000000000000 : ℝ)=(12506042237356257051/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34274461097048197/100000000000000000000 : ℝ) ≤ ((27680675901697895773/27690000000000000000 : ℝ)+2*(496284980999/276900000000000 : ℝ)*(1409/10000 : ℝ))^(4169/1024 : ℝ) := by
    rw [show (27680675901697895773/27690000000000000000 : ℝ)+2*(496284980999/276900000000000 : ℝ)*(1409/10000 : ℝ)=(10001683355891097/10000000000000000 : ℝ) by norm_num, show 1+2*(34274461097048197/100000000000000000000 : ℝ)=(50034274461097048197/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27680675901697895773/27690000000000000000 : ℝ)*(X 1 0+X 2 0)+(496284980999/276900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (11321/100000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (27680675901697895773/27690000000000000000 : ℝ)) (alpha := (496284980999/276900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27680675901697895773/27690000000000000000 : ℝ)*(X 0 1+X 2 1)+(496284980999/276900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (11321/100000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (27680675901697895773/27690000000000000000 : ℝ)) (alpha := (496284980999/276900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27680675901697895773/27690000000000000000 : ℝ)*(X 0 2+X 1 2)+(496284980999/276900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (11321/100000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (27680675901697895773/27690000000000000000 : ℝ)) (alpha := (496284980999/276900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2164946769/10000000000 : ℝ)*X 0 0+(168540577/312500000 : ℝ)*X 0 1+(5265485311/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668103447/1250000000 : ℝ)*X 1 0+(-557444873/2500000000 : ℝ)*X 1 1+(5265485311/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336206887/2500000000 : ℝ)*X 2 0+(2632742667/5000000000 : ℝ)*X 2 1+(-4459559/20000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2182046621/5000000000 : ℝ)*X 0 0+(4238697061/10000000000 : ℝ)*X 0 1+(4493177521/10000000000 : ℝ)*X 0 2+(2182046621/5000000000 : ℝ)*X 1 0+(4238697061/10000000000 : ℝ)*X 1 1+(4493177521/10000000000 : ℝ)*X 1 2+(2182046621/5000000000 : ℝ)*X 2 0+(4238697061/10000000000 : ℝ)*X 2 1+(4493177521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2164951763/10000000000 : ℝ)*X 0 0+(1316452021/2500000000 : ℝ)*X 0 1+(1078594897/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328109001/2500000000 : ℝ)*X 1 0+(-2102290397/10000000000 : ℝ)*X 1 1+(168530451/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((83006813/156250000 : ℝ)*X 2 0+(5392974379/10000000000 : ℝ)*X 2 1+(-2102290431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182051517/5000000000 : ℝ)*X 0 0+(1123133701/2500000000 : ℝ)*X 0 1+(2119671089/5000000000 : ℝ)*X 0 2+(2182051517/5000000000 : ℝ)*X 1 0+(1123133701/2500000000 : ℝ)*X 1 1+(2119671089/5000000000 : ℝ)*X 1 2+(2182051517/5000000000 : ℝ)*X 2 0+(1123133701/2500000000 : ℝ)*X 2 1+(2119671089/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8074028853409229291489591/812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (525485397/25000000000000 : ℝ)*(base19) + (236194351/12500000000000 : ℝ)*(base23) + (91609771/100000000000000 : ℝ)*(lower2) + (271864017/100000000000000 : ℝ)*(upper3) + (31356411/25000000000000 : ℝ)*(upper5) + (734604584877857/12500000000000 : ℝ)*(major0) + (734604584877857/12500000000000 : ℝ)*(major1) + (734604584877857/12500000000000 : ℝ)*(major2) + (3911991176326987/50000000000000 : ℝ)*(sp0) + (7824036985201681/100000000000000 : ℝ)*(sp1) + (7824037197588461/100000000000000 : ℝ)*(sp2) + (392960246111127/10000000000000 : ℝ)*(sp3) + (3545905581/6250000000000 : ℝ)*(sp4) + (31478548949/100000000000000 : ℝ)*(sp7) + (196481696983011/5000000000000 : ℝ)*(f.failure) + (7824039087143269/100000000000000 : ℝ)*(f.sum) + (922168849897/432656250000000000000000000 : ℝ)*base65 + (2056620739469450513/115375000000000000000000000000000 : ℝ)*base68 + (539699983144450513/115375000000000000000000000000000 : ℝ)*base70 + (4556870898232950513/115375000000000000000000000000000 : ℝ)*base72 + (1624367179343/6922500000000000000000000000 : ℝ)*base74 + (2819833188156674487/115375000000000000000000000000000 : ℝ)*base75 + (748269274152450513/115375000000000000000000000000000 : ℝ)*base78 + (161213713205299487/115375000000000000000000000000000 : ℝ)*base79 + (11325075173899/3461250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (8166349/500000000000000000000 : ℝ)*base89 + (8166349/500000000000000000000 : ℝ)*base91 + (8166349/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38952906976787195834457/4615000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1709199739/100000000000000 : ℝ)*(base19) + (1773248759/100000000000000 : ℝ)*(base23) + (4587313/3125000000000 : ℝ)*(upper3) + (1058891/5000000000000 : ℝ)*(lower4) + (198415111/100000000000000 : ℝ)*(upper5) + (2953318947172813/50000000000000 : ℝ)*(major0) + (2953318947172813/50000000000000 : ℝ)*(major1) + (2953318947172813/50000000000000 : ℝ)*(major2) + (23490670479/50000000000000 : ℝ)*(sp1) + (44150253503/100000000000000 : ℝ)*(sp2) + (1965928635850981/25000000000000 : ℝ)*(sp4) + (7863665852863227/100000000000000 : ℝ)*(sp5) + (3931834309950831/50000000000000 : ℝ)*(sp6) + (1974780481968663/50000000000000 : ℝ)*(sp7) + (1974780481968663/50000000000000 : ℝ)*(f.failure) + (1965928635850981/25000000000000 : ℝ)*(f.sum) + (26961670620733/6922500000000000000000000000 : ℝ)*base66 + (399685998942693517/461500000000000000000000000000000 : ℝ)*base68 + (4398991255805306483/461500000000000000000000000000000 : ℝ)*base69 + (6445019446862693517/461500000000000000000000000000000 : ℝ)*base72 + (58735871230031/13845000000000000000000000000 : ℝ)*base74 + (1881600657992306483/461500000000000000000000000000000 : ℝ)*base75 + (2819615333050693517/461500000000000000000000000000000 : ℝ)*base78 + (2730381778491306483/461500000000000000000000000000000 : ℝ)*base79 + (3948265585837/1730625000000000000000000000 : ℝ)*base82 + (34528217/5000000000000000000000 : ℝ)*base89 + (34528217/5000000000000000000000 : ℝ)*base91 + (34528217/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1146_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1146_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1146_s7_0 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2164972303/10000000000 : ℝ)*x 0 + (337061809/625000000 : ℝ)*x 1 + (5265778133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164972303/10000000000 : ℝ)^8339 ≤ (13155657489499/100000000000000 : ℝ)^6291 := by
    have hnat : (2164972303 : ℕ)^8339*100000000000000^6291 ≤ 13155657489499^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164972303 10000000000 13155657489499 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337061809/625000000 : ℝ)^8339 ≤ (44109092990639/100000000000000 : ℝ)^6291 := by
    have hnat : (337061809 : ℕ)^8339*100000000000000^6291 ≤ 44109092990639^6291*625000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337061809 625000000 44109092990639 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265778133/10000000000 : ℝ)^8339 ≤ (10683812376427/25000000000000 : ℝ)^6291 := by
    have hnat : (5265778133 : ℕ)^8339*25000000000000^6291 ≤ 10683812376427^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265778133 10000000000 10683812376427 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2164972303/10000000000 : ℝ), (337061809/625000000 : ℝ), (5265778133/10000000000 : ℝ)] ![(13155657489499/100000000000000 : ℝ), (44109092990639/100000000000000 : ℝ), (10683812376427/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2164972303/10000000000 : ℝ)|^8339 ≤ (13155657489499/100000000000000 : ℝ)^6291
        have hw : |(-2164972303/10000000000 : ℝ)|=(2164972303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337061809/625000000 : ℝ)|^8339 ≤ (44109092990639/100000000000000 : ℝ)^6291
        have hw : |(337061809/625000000 : ℝ)|=(337061809/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265778133/10000000000 : ℝ)|^8339 ≤ (10683812376427/25000000000000 : ℝ)^6291
        have hw : |(5265778133/10000000000 : ℝ)|=(5265778133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s7_1 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068950011/2000000000 : ℝ)*x 0 + (-2229495167/10000000000 : ℝ)*x 1 + (105315563/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068950011/2000000000 : ℝ)^8339 ≤ (10896717456917/25000000000000 : ℝ)^6291 := by
    have hnat : (1068950011 : ℕ)^8339*25000000000000^6291 ≤ 10896717456917^6291*2000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068950011 2000000000 10896717456917 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2229495167/10000000000 : ℝ)^8339 ≤ (13677880472533/100000000000000 : ℝ)^6291 := by
    have hnat : (2229495167 : ℕ)^8339*100000000000000^6291 ≤ 13677880472533^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229495167 10000000000 13677880472533 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105315563/200000000 : ℝ)^8339 ≤ (10683812422147/25000000000000 : ℝ)^6291 := by
    have hnat : (105315563 : ℕ)^8339*25000000000000^6291 ≤ 10683812422147^6291*200000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105315563 200000000 10683812422147 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068950011/2000000000 : ℝ), (-2229495167/10000000000 : ℝ), (105315563/200000000 : ℝ)] ![(10896717456917/25000000000000 : ℝ), (13677880472533/100000000000000 : ℝ), (10683812422147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068950011/2000000000 : ℝ)|^8339 ≤ (10896717456917/25000000000000 : ℝ)^6291
        have hw : |(1068950011/2000000000 : ℝ)|=(1068950011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2229495167/10000000000 : ℝ)|^8339 ≤ (13677880472533/100000000000000 : ℝ)^6291
        have hw : |(-2229495167/10000000000 : ℝ)|=(2229495167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105315563/200000000 : ℝ)|^8339 ≤ (10683812422147/25000000000000 : ℝ)^6291
        have hw : |(105315563/200000000 : ℝ)|=(105315563/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s7_2 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344750043/10000000000 : ℝ)*x 0 + (2632889063/5000000000 : ℝ)*x 1 + (-445899043/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344750043/10000000000 : ℝ)^8339 ≤ (43586869697949/100000000000000 : ℝ)^6291 := by
    have hnat : (5344750043 : ℕ)^8339*100000000000000^6291 ≤ 43586869697949^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344750043 10000000000 43586869697949 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632889063/5000000000 : ℝ)^8339 ≤ (10683812357601/25000000000000 : ℝ)^6291 := by
    have hnat : (2632889063 : ℕ)^8339*25000000000000^6291 ≤ 10683812357601^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632889063 5000000000 10683812357601 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (445899043/2000000000 : ℝ)^8339 ≤ (13677880862877/100000000000000 : ℝ)^6291 := by
    have hnat : (445899043 : ℕ)^8339*100000000000000^6291 ≤ 13677880862877^6291*2000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445899043 2000000000 13677880862877 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344750043/10000000000 : ℝ), (2632889063/5000000000 : ℝ), (-445899043/2000000000 : ℝ)] ![(43586869697949/100000000000000 : ℝ), (10683812357601/25000000000000 : ℝ), (13677880862877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344750043/10000000000 : ℝ)|^8339 ≤ (43586869697949/100000000000000 : ℝ)^6291
        have hw : |(5344750043/10000000000 : ℝ)|=(5344750043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632889063/5000000000 : ℝ)|^8339 ≤ (10683812357601/25000000000000 : ℝ)^6291
        have hw : |(2632889063/5000000000 : ℝ)|=(2632889063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-445899043/2000000000 : ℝ)|^8339 ≤ (13677880862877/100000000000000 : ℝ)^6291
        have hw : |(-445899043/2000000000 : ℝ)|=(445899043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s7_3 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364108597/10000000000 : ℝ)*x 0 + (264955923/625000000 : ℝ)*x 1 + (561571977/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364108597/10000000000 : ℝ)^8339 ≤ (8329243528421/25000000000000 : ℝ)^6291 := by
    have hnat : (4364108597 : ℕ)^8339*25000000000000^6291 ≤ 8329243528421^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364108597 10000000000 8329243528421 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264955923/625000000 : ℝ)^8339 ≤ (32059823570133/100000000000000 : ℝ)^6291 := by
    have hnat : (264955923 : ℕ)^8339*100000000000000^6291 ≤ 32059823570133^6291*625000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264955923 625000000 32059823570133 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561571977/1250000000 : ℝ)^8339 ≤ (8655800576369/25000000000000 : ℝ)^6291 := by
    have hnat : (561571977 : ℕ)^8339*25000000000000^6291 ≤ 8655800576369^6291*1250000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561571977 1250000000 8655800576369 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364108597/10000000000 : ℝ), (264955923/625000000 : ℝ), (561571977/1250000000 : ℝ)] ![(8329243528421/25000000000000 : ℝ), (32059823570133/100000000000000 : ℝ), (8655800576369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364108597/10000000000 : ℝ)|^8339 ≤ (8329243528421/25000000000000 : ℝ)^6291
        have hw : |(4364108597/10000000000 : ℝ)|=(4364108597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264955923/625000000 : ℝ)|^8339 ≤ (32059823570133/100000000000000 : ℝ)^6291
        have hw : |(264955923/625000000 : ℝ)|=(264955923/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561571977/1250000000 : ℝ)|^8339 ≤ (8655800576369/25000000000000 : ℝ)^6291
        have hw : |(561571977/1250000000 : ℝ)|=(561571977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s7_4 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-216497739/1000000000 : ℝ)*x 0 + (5266098211/10000000000 : ℝ)*x 1 + (2696333779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216497739/1000000000 : ℝ)^8339 ≤ (13155698464257/100000000000000 : ℝ)^6291 := by
    have hnat : (216497739 : ℕ)^8339*100000000000000^6291 ≤ 13155698464257^6291*1000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216497739 1000000000 13155698464257 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266098211/10000000000 : ℝ)^8339 ≤ (8547738566271/20000000000000 : ℝ)^6291 := by
    have hnat : (5266098211 : ℕ)^8339*20000000000000^6291 ≤ 8547738566271^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266098211 10000000000 8547738566271 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696333779/5000000000 : ℝ)^8339 ≤ (22052804344971/50000000000000 : ℝ)^6291 := by
    have hnat : (2696333779 : ℕ)^8339*50000000000000^6291 ≤ 22052804344971^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696333779 5000000000 22052804344971 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-216497739/1000000000 : ℝ), (5266098211/10000000000 : ℝ), (2696333779/5000000000 : ℝ)] ![(13155698464257/100000000000000 : ℝ), (8547738566271/20000000000000 : ℝ), (22052804344971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-216497739/1000000000 : ℝ)|^8339 ≤ (13155698464257/100000000000000 : ℝ)^6291
        have hw : |(-216497739/1000000000 : ℝ)|=(216497739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266098211/10000000000 : ℝ)|^8339 ≤ (8547738566271/20000000000000 : ℝ)^6291
        have hw : |(5266098211/10000000000 : ℝ)|=(5266098211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696333779/5000000000 : ℝ)|^8339 ≤ (22052804344971/50000000000000 : ℝ)^6291
        have hw : |(2696333779/5000000000 : ℝ)|=(2696333779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s7_5 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312510991/10000000000 : ℝ)*x 0 + (-2102605259/10000000000 : ℝ)*x 1 + (5392668101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312510991/10000000000 : ℝ)^8339 ≤ (8647742137361/20000000000000 : ℝ)^6291 := by
    have hnat : (5312510991 : ℕ)^8339*20000000000000^6291 ≤ 8647742137361^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312510991 10000000000 8647742137361 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2102605259/10000000000 : ℝ)^8339 ≤ (12655674718263/100000000000000 : ℝ)^6291 := by
    have hnat : (2102605259 : ℕ)^8339*100000000000000^6291 ≤ 12655674718263^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102605259 10000000000 12655674718263 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392668101/10000000000 : ℝ)^8339 ≤ (4410561457681/10000000000000 : ℝ)^6291 := by
    have hnat : (5392668101 : ℕ)^8339*10000000000000^6291 ≤ 4410561457681^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392668101 10000000000 4410561457681 10000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312510991/10000000000 : ℝ), (-2102605259/10000000000 : ℝ), (5392668101/10000000000 : ℝ)] ![(8647742137361/20000000000000 : ℝ), (12655674718263/100000000000000 : ℝ), (4410561457681/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312510991/10000000000 : ℝ)|^8339 ≤ (8647742137361/20000000000000 : ℝ)^6291
        have hw : |(5312510991/10000000000 : ℝ)|=(5312510991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2102605259/10000000000 : ℝ)|^8339 ≤ (12655674718263/100000000000000 : ℝ)^6291
        have hw : |(-2102605259/10000000000 : ℝ)|=(2102605259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392668101/10000000000 : ℝ)|^8339 ≤ (4410561457681/10000000000000 : ℝ)^6291
        have hw : |(5392668101/10000000000 : ℝ)|=(5392668101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s7_6 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312511451/10000000000 : ℝ)*x 0 + (269633373/500000000 : ℝ)*x 1 + (-2102605509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312511451/10000000000 : ℝ)^8339 ≤ (8647743129917/20000000000000 : ℝ)^6291 := by
    have hnat : (5312511451 : ℕ)^8339*20000000000000^6291 ≤ 8647743129917^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312511451 10000000000 8647743129917 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269633373/500000000 : ℝ)^8339 ≤ (44105607627487/100000000000000 : ℝ)^6291 := by
    have hnat : (269633373 : ℕ)^8339*100000000000000^6291 ≤ 44105607627487^6291*500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269633373 500000000 44105607627487 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2102605509/10000000000 : ℝ)^8339 ≤ (12655676712891/100000000000000 : ℝ)^6291 := by
    have hnat : (2102605509 : ℕ)^8339*100000000000000^6291 ≤ 12655676712891^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102605509 10000000000 12655676712891 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312511451/10000000000 : ℝ), (269633373/500000000 : ℝ), (-2102605509/10000000000 : ℝ)] ![(8647743129917/20000000000000 : ℝ), (44105607627487/100000000000000 : ℝ), (12655676712891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312511451/10000000000 : ℝ)|^8339 ≤ (8647743129917/20000000000000 : ℝ)^6291
        have hw : |(5312511451/10000000000 : ℝ)|=(5312511451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269633373/500000000 : ℝ)|^8339 ≤ (44105607627487/100000000000000 : ℝ)^6291
        have hw : |(269633373/500000000 : ℝ)|=(269633373/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2102605509/10000000000 : ℝ)|^8339 ≤ (12655676712891/100000000000000 : ℝ)^6291
        have hw : |(-2102605509/10000000000 : ℝ)|=(2102605509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s7_7 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364118159/10000000000 : ℝ)*x 0 + (4491939321/10000000000 : ℝ)*x 1 + (2119966859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364118159/10000000000 : ℝ)^8339 ≤ (4164633859693/12500000000000 : ℝ)^6291 := by
    have hnat : (4364118159 : ℕ)^8339*12500000000000^6291 ≤ 4164633859693^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364118159 10000000000 4164633859693 12500000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491939321/10000000000 : ℝ)^8339 ≤ (6923340048751/20000000000000 : ℝ)^6291 := by
    have hnat : (4491939321 : ℕ)^8339*20000000000000^6291 ≤ 6923340048751^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491939321 10000000000 6923340048751 20000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119966859/5000000000 : ℝ)^8339 ≤ (32066228867993/100000000000000 : ℝ)^6291 := by
    have hnat : (2119966859 : ℕ)^8339*100000000000000^6291 ≤ 32066228867993^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119966859 5000000000 32066228867993 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364118159/10000000000 : ℝ), (4491939321/10000000000 : ℝ), (2119966859/5000000000 : ℝ)] ![(4164633859693/12500000000000 : ℝ), (6923340048751/20000000000000 : ℝ), (32066228867993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364118159/10000000000 : ℝ)|^8339 ≤ (4164633859693/12500000000000 : ℝ)^6291
        have hw : |(4364118159/10000000000 : ℝ)|=(4364118159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491939321/10000000000 : ℝ)|^8339 ≤ (6923340048751/20000000000000 : ℝ)^6291
        have hw : |(4491939321/10000000000 : ℝ)|=(4491939321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2119966859/5000000000 : ℝ)|^8339 ≤ (32066228867993/100000000000000 : ℝ)^6291
        have hw : |(2119966859/5000000000 : ℝ)|=(2119966859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1146_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5679/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3513/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11351/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14059/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11351/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11351/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14059/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11351/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11351/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14059/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11351/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11351/100000 : ℝ) ^ (4169/1024 : ℝ) ≤ (14215782273920939/100000000000000000000 : ℝ) := by
    have hpowers : (11351/100000 : ℝ)^4169 ≤ (14215782273920939/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11351 : ℕ)^4169*100000000000000000000^1024 ≤ 14215782273920939^1024*100000^4169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11351 100000 14215782273920939 100000000000000000000 4169 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11351/100000 : ℝ)) (X := (14215782273920939/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14059/100000 : ℝ) ^ (4169/1024 : ℝ) ≤ (8492121566775923/25000000000000000000 : ℝ) := by
    have hpowers : (14059/100000 : ℝ)^4169 ≤ (8492121566775923/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14059 : ℕ)^4169*25000000000000000000^1024 ≤ 8492121566775923^1024*100000^4169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14059 100000 8492121566775923 25000000000000000000 4169 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14059/100000 : ℝ)) (X := (8492121566775923/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014215782273920939/50000000000000000000 : ℝ) ≤ (625043641761243/625000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (50014215782273920939/50000000000000000000 : ℝ)^1024 ≤ (625043641761243/625000000000000 : ℝ)^4169 := by
      have hnat : (50014215782273920939 : ℕ)^1024*625000000000000^4169 ≤ 625043641761243^4169*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014215782273920939 50000000000000000000 625043641761243 625000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625043641761243/625000000000000 : ℝ)) (X := (50014215782273920939/50000000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048184268541024631/100000000000000000000 : ℝ) ≤ (2500295824694507/2500000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (100048184268541024631/100000000000000000000 : ℝ)^1024 ≤ (2500295824694507/2500000000000000 : ℝ)^4169 := by
      have hnat : (100048184268541024631 : ℕ)^1024*2500000000000000^4169 ≤ 2500295824694507^4169*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048184268541024631 100000000000000000000 2500295824694507 2500000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500295824694507/2500000000000000 : ℝ)) (X := (100048184268541024631/100000000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508492121566775923/12500000000000000000 : ℝ) ≤ (1250208541172021/1250000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (12508492121566775923/12500000000000000000 : ℝ)^1024 ≤ (1250208541172021/1250000000000000 : ℝ)^4169 := by
      have hnat : (12508492121566775923 : ℕ)^1024*1250000000000000^4169 ≤ 1250208541172021^4169*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508492121566775923 12500000000000000000 1250208541172021 1250000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250208541172021/1250000000000000 : ℝ)) (X := (12508492121566775923/12500000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14215782273920939/100000000000000000000 : ℝ) ≤ ((3383859968199020303/3385000000000000000 : ℝ)+2*(24251529907/13540000000000 : ℝ)*(11351/100000 : ℝ))^(4169/1024 : ℝ) := by
    rw [show (3383859968199020303/3385000000000000000 : ℝ)+2*(24251529907/13540000000000 : ℝ)*(11351/100000 : ℝ)=(625043641761243/625000000000000 : ℝ) by norm_num, show 1+2*(14215782273920939/100000000000000000000 : ℝ)=(50014215782273920939/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8492121566775923/25000000000000000000 : ℝ)+(14215782273920939/100000000000000000000 : ℝ) ≤ ((3383859968199020303/3385000000000000000 : ℝ)+(24251529907/13540000000000 : ℝ)*((14059/100000 : ℝ)+(11351/100000 : ℝ)))^(4169/1024 : ℝ) := by
    rw [show (3383859968199020303/3385000000000000000 : ℝ)+(24251529907/13540000000000 : ℝ)*((14059/100000 : ℝ)+(11351/100000 : ℝ))=(2500295824694507/2500000000000000 : ℝ) by norm_num, show 1+(8492121566775923/25000000000000000000 : ℝ)+(14215782273920939/100000000000000000000 : ℝ)=(100048184268541024631/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8492121566775923/25000000000000000000 : ℝ) ≤ ((3383859968199020303/3385000000000000000 : ℝ)+2*(24251529907/13540000000000 : ℝ)*(14059/100000 : ℝ))^(4169/1024 : ℝ) := by
    rw [show (3383859968199020303/3385000000000000000 : ℝ)+2*(24251529907/13540000000000 : ℝ)*(14059/100000 : ℝ)=(1250208541172021/1250000000000000 : ℝ) by norm_num, show 1+2*(8492121566775923/25000000000000000000 : ℝ)=(12508492121566775923/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3383859968199020303/3385000000000000000 : ℝ)*(X 1 0+X 2 0)+(24251529907/13540000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (11351/100000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (3383859968199020303/3385000000000000000 : ℝ)) (alpha := (24251529907/13540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3383859968199020303/3385000000000000000 : ℝ)*(X 0 1+X 2 1)+(24251529907/13540000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (11351/100000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (3383859968199020303/3385000000000000000 : ℝ)) (alpha := (24251529907/13540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3383859968199020303/3385000000000000000 : ℝ)*(X 0 2+X 1 2)+(24251529907/13540000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (11351/100000 : ℝ)) (hi := (14059/100000 : ℝ)) (c := (3383859968199020303/3385000000000000000 : ℝ)) (alpha := (24251529907/13540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2164972303/10000000000 : ℝ)*X 0 0+(337061809/625000000 : ℝ)*X 0 1+(5265778133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068950011/2000000000 : ℝ)*X 1 0+(-2229495167/10000000000 : ℝ)*X 1 1+(105315563/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344750043/10000000000 : ℝ)*X 2 0+(2632889063/5000000000 : ℝ)*X 2 1+(-445899043/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364108597/10000000000 : ℝ)*X 0 0+(264955923/625000000 : ℝ)*X 0 1+(561571977/1250000000 : ℝ)*X 0 2+(4364108597/10000000000 : ℝ)*X 1 0+(264955923/625000000 : ℝ)*X 1 1+(561571977/1250000000 : ℝ)*X 1 2+(4364108597/10000000000 : ℝ)*X 2 0+(264955923/625000000 : ℝ)*X 2 1+(561571977/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-216497739/1000000000 : ℝ)*X 0 0+(5266098211/10000000000 : ℝ)*X 0 1+(2696333779/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312510991/10000000000 : ℝ)*X 1 0+(-2102605259/10000000000 : ℝ)*X 1 1+(5392668101/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312511451/10000000000 : ℝ)*X 2 0+(269633373/500000000 : ℝ)*X 2 1+(-2102605509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4364118159/10000000000 : ℝ)*X 0 0+(4491939321/10000000000 : ℝ)*X 0 1+(2119966859/5000000000 : ℝ)*X 0 2+(4364118159/10000000000 : ℝ)*X 1 0+(4491939321/10000000000 : ℝ)*X 1 1+(2119966859/5000000000 : ℝ)*X 1 2+(4364118159/10000000000 : ℝ)*X 2 0+(4491939321/10000000000 : ℝ)*X 2 1+(2119966859/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (508834864293738480543720843/169250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5014591/781250000000 : ℝ)*(base19) + (8819671/1562500000000 : ℝ)*(base23) + (1606317/4000000000000 : ℝ)*(lower2) + (124363177/100000000000000 : ℝ)*(upper3) + (8218109/100000000000000 : ℝ)*(lower4) + (5904600925160727/100000000000000 : ℝ)*(major0) + (5904600925160727/100000000000000 : ℝ)*(major1) + (5904600925160727/100000000000000 : ℝ)*(major2) + (7860987635568281/100000000000000 : ℝ)*(sp0) + (7861002193936007/100000000000000 : ℝ)*(sp1) + (7861002271344711/100000000000000 : ℝ)*(sp2) + (3948189706760789/100000000000000 : ℝ)*(sp3) + (15200235373/100000000000000 : ℝ)*(sp4) + (9207543339/100000000000000 : ℝ)*(sp7) + (30845304018001/781250000000 : ℝ)*(f.failure) + (3930501417901827/50000000000000 : ℝ)*(f.sum) + (29029172529/21156250000000000000000000 : ℝ)*base66 + (1505461204504509719/338500000000000000000000000000000 : ℝ)*base68 + (1968401926812009719/338500000000000000000000000000000 : ℝ)*base70 + (1958387264173009719/338500000000000000000000000000000 : ℝ)*base72 + (567856698567/135400000000000000000000000 : ℝ)*base73 + (2340588953617509719/338500000000000000000000000000000 : ℝ)*base76 + (2203354405188990281/338500000000000000000000000000000 : ℝ)*base77 + (1654338597963990281/338500000000000000000000000000000 : ℝ)*base79 + (13546362281/21156250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (754991/78125000000000000000 : ℝ)*base90 + (754991/78125000000000000000 : ℝ)*base92 + (754991/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1358029556043978518181/677000000000000000000000000 : ℝ) := by norm_num
    linear_combination (349178651/50000000000000 : ℝ)*(base19) + (1762834589/100000000000000 : ℝ)*(base23) + (91736821/50000000000000 : ℝ)*(upper2) + (188366641/100000000000000 : ℝ)*(upper3) + (5934493045583891/100000000000000 : ℝ)*(major0) + (5934493045583891/100000000000000 : ℝ)*(major1) + (5934493045583891/100000000000000 : ℝ)*(major2) + (22161059303/50000000000000 : ℝ)*(sp1) + (1001810259/2000000000000 : ℝ)*(sp2) + (7665751211/100000000000000 : ℝ)*(sp3) + (3950399650339441/50000000000000 : ℝ)*(sp4) + (316030171208119/4000000000000 : ℝ)*(sp5) + (493796715458209/6250000000000 : ℝ)*(sp6) + (124005595558519/3125000000000 : ℝ)*(sp7) + (198409336181191/5000000000000 : ℝ)*(f.failure) + (3950399650339441/50000000000000 : ℝ)*(f.sum) + (523386492503/338500000000000000000000000 : ℝ)*base66 + (2693180385689988973/338500000000000000000000000000000 : ℝ)*base67 + (6560794540806988973/338500000000000000000000000000000 : ℝ)*base69 + (2933098480336011027/338500000000000000000000000000000 : ℝ)*base72 + (707011019271/169250000000000000000000000 : ℝ)*base73 + (4248847269824511027/338500000000000000000000000000000 : ℝ)*base76 + (313905796437511027/338500000000000000000000000000000 : ℝ)*base78 + (4970974697526988973/338500000000000000000000000000000 : ℝ)*base79 + (2902486397939/677000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1764969/500000000000000000000 : ℝ)*base89 + (1764969/500000000000000000000 : ℝ)*base91 + (1764969/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1146_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14059/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1146_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1146_s8_0 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2164977351/10000000000 : ℝ)*x 0 + (1348229739/2500000000 : ℝ)*x 1 + (5265844887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164977351/10000000000 : ℝ)^8339 ≤ (328892453753/2500000000000 : ℝ)^6291 := by
    have hnat : (2164977351 : ℕ)^8339*2500000000000^6291 ≤ 328892453753^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164977351 10000000000 328892453753 2500000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348229739/2500000000 : ℝ)^8339 ≤ (11027083552801/25000000000000 : ℝ)^6291 := by
    have hnat : (1348229739 : ℕ)^8339*25000000000000^6291 ≤ 11027083552801^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348229739 2500000000 11027083552801 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265844887/10000000000 : ℝ)^8339 ≤ (10683991906073/25000000000000 : ℝ)^6291 := by
    have hnat : (5265844887 : ℕ)^8339*25000000000000^6291 ≤ 10683991906073^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265844887 10000000000 10683991906073 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2164977351/10000000000 : ℝ), (1348229739/2500000000 : ℝ), (5265844887/10000000000 : ℝ)] ![(328892453753/2500000000000 : ℝ), (11027083552801/25000000000000 : ℝ), (10683991906073/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2164977351/10000000000 : ℝ)|^8339 ≤ (328892453753/2500000000000 : ℝ)^6291
        have hw : |(-2164977351/10000000000 : ℝ)|=(2164977351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348229739/2500000000 : ℝ)|^8339 ≤ (11027083552801/25000000000000 : ℝ)^6291
        have hw : |(1348229739/2500000000 : ℝ)|=(1348229739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265844887/10000000000 : ℝ)|^8339 ≤ (10683991906073/25000000000000 : ℝ)^6291
        have hw : |(5265844887/10000000000 : ℝ)|=(5265844887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s8_1 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336183183/2500000000 : ℝ)*x 0 + (-2229429897/10000000000 : ℝ)*x 1 + (164557653/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336183183/2500000000 : ℝ)^8339 ≤ (10896670641871/25000000000000 : ℝ)^6291 := by
    have hnat : (1336183183 : ℕ)^8339*25000000000000^6291 ≤ 10896670641871^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336183183 2500000000 10896670641871 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2229429897/10000000000 : ℝ)^8339 ≤ (13677349688193/100000000000000 : ℝ)^6291 := by
    have hnat : (2229429897 : ℕ)^8339*100000000000000^6291 ≤ 13677349688193^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229429897 10000000000 13677349688193 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164557653/312500000 : ℝ)^8339 ≤ (5341995965139/12500000000000 : ℝ)^6291 := by
    have hnat : (164557653 : ℕ)^8339*12500000000000^6291 ≤ 5341995965139^6291*312500000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164557653 312500000 5341995965139 12500000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336183183/2500000000 : ℝ), (-2229429897/10000000000 : ℝ), (164557653/312500000 : ℝ)] ![(10896670641871/25000000000000 : ℝ), (13677349688193/100000000000000 : ℝ), (5341995965139/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336183183/2500000000 : ℝ)|^8339 ≤ (10896670641871/25000000000000 : ℝ)^6291
        have hw : |(1336183183/2500000000 : ℝ)|=(1336183183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2229429897/10000000000 : ℝ)|^8339 ≤ (13677349688193/100000000000000 : ℝ)^6291
        have hw : |(-2229429897/10000000000 : ℝ)|=(2229429897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164557653/312500000 : ℝ)|^8339 ≤ (5341995965139/12500000000000 : ℝ)^6291
        have hw : |(164557653/312500000 : ℝ)|=(164557653/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s8_2 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344732731/10000000000 : ℝ)*x 0 + (1053168979/2000000000 : ℝ)*x 1 + (-2229429901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344732731/10000000000 : ℝ)^8339 ≤ (21793341278337/50000000000000 : ℝ)^6291 := by
    have hnat : (5344732731 : ℕ)^8339*50000000000000^6291 ≤ 21793341278337^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344732731 10000000000 21793341278337 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053168979/2000000000 : ℝ)^8339 ≤ (21367983855177/50000000000000 : ℝ)^6291 := by
    have hnat : (1053168979 : ℕ)^8339*50000000000000^6291 ≤ 21367983855177^6291*2000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053168979 2000000000 21367983855177 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2229429901/10000000000 : ℝ)^8339 ≤ (6838674860361/50000000000000 : ℝ)^6291 := by
    have hnat : (2229429901 : ℕ)^8339*50000000000000^6291 ≤ 6838674860361^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229429901 10000000000 6838674860361 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344732731/10000000000 : ℝ), (1053168979/2000000000 : ℝ), (-2229429901/10000000000 : ℝ)] ![(21793341278337/50000000000000 : ℝ), (21367983855177/50000000000000 : ℝ), (6838674860361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344732731/10000000000 : ℝ)|^8339 ≤ (21793341278337/50000000000000 : ℝ)^6291
        have hw : |(5344732731/10000000000 : ℝ)|=(5344732731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053168979/2000000000 : ℝ)|^8339 ≤ (21367983855177/50000000000000 : ℝ)^6291
        have hw : |(1053168979/2000000000 : ℝ)|=(1053168979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2229429901/10000000000 : ℝ)|^8339 ≤ (6838674860361/50000000000000 : ℝ)^6291
        have hw : |(-2229429901/10000000000 : ℝ)|=(2229429901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s8_3 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1091028011/2500000000 : ℝ)*x 0 + (4239430383/10000000000 : ℝ)*x 1 + (2246219661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091028011/2500000000 : ℝ)^8339 ≤ (1332680359841/4000000000000 : ℝ)^6291 := by
    have hnat : (1091028011 : ℕ)^8339*4000000000000^6291 ≤ 1332680359841^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091028011 2500000000 1332680359841 4000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4239430383/10000000000 : ℝ)^8339 ≤ (4007647880863/12500000000000 : ℝ)^6291 := by
    have hnat : (4239430383 : ℕ)^8339*12500000000000^6291 ≤ 4007647880863^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239430383 10000000000 4007647880863 12500000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246219661/5000000000 : ℝ)^8339 ≤ (34621807937113/100000000000000 : ℝ)^6291 := by
    have hnat : (2246219661 : ℕ)^8339*100000000000000^6291 ≤ 34621807937113^6291*5000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246219661 5000000000 34621807937113 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091028011/2500000000 : ℝ), (4239430383/10000000000 : ℝ), (2246219661/5000000000 : ℝ)] ![(1332680359841/4000000000000 : ℝ), (4007647880863/12500000000000 : ℝ), (34621807937113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091028011/2500000000 : ℝ)|^8339 ≤ (1332680359841/4000000000000 : ℝ)^6291
        have hw : |(1091028011/2500000000 : ℝ)|=(1091028011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4239430383/10000000000 : ℝ)|^8339 ≤ (4007647880863/12500000000000 : ℝ)^6291
        have hw : |(4239430383/10000000000 : ℝ)|=(4239430383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246219661/5000000000 : ℝ)|^8339 ≤ (34621807937113/100000000000000 : ℝ)^6291
        have hw : |(2246219661/5000000000 : ℝ)|=(2246219661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s8_4 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-270622779/1250000000 : ℝ)*x 0 + (5266163997/10000000000 : ℝ)*x 1 + (5392598681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270622779/1250000000 : ℝ)^8339 ≤ (657786873281/5000000000000 : ℝ)^6291 := by
    have hnat : (270622779 : ℕ)^8339*5000000000000^6291 ≤ 657786873281^6291*1250000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270622779 1250000000 657786873281 5000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266163997/10000000000 : ℝ)^8339 ≤ (21369700275241/50000000000000 : ℝ)^6291 := by
    have hnat : (5266163997 : ℕ)^8339*50000000000000^6291 ≤ 21369700275241^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266163997 10000000000 21369700275241 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392598681/10000000000 : ℝ)^8339 ≤ (44104861969947/100000000000000 : ℝ)^6291 := by
    have hnat : (5392598681 : ℕ)^8339*100000000000000^6291 ≤ 44104861969947^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392598681 10000000000 44104861969947 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-270622779/1250000000 : ℝ), (5266163997/10000000000 : ℝ), (5392598681/10000000000 : ℝ)] ![(657786873281/5000000000000 : ℝ), (21369700275241/50000000000000 : ℝ), (44104861969947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-270622779/1250000000 : ℝ)|^8339 ≤ (657786873281/5000000000000 : ℝ)^6291
        have hw : |(-270622779/1250000000 : ℝ)|=(270622779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266163997/10000000000 : ℝ)|^8339 ≤ (21369700275241/50000000000000 : ℝ)^6291
        have hw : |(5266163997/10000000000 : ℝ)|=(5266163997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392598681/10000000000 : ℝ)|^8339 ≤ (44104861969947/100000000000000 : ℝ)^6291
        have hw : |(5392598681/10000000000 : ℝ)|=(5392598681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s8_5 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312528347/10000000000 : ℝ)*x 0 + (-52566903/250000000 : ℝ)*x 1 + (5392598681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312528347/10000000000 : ℝ)^8339 ≤ (10809724483687/25000000000000 : ℝ)^6291 := by
    have hnat : (5312528347 : ℕ)^8339*25000000000000^6291 ≤ 10809724483687^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312528347 10000000000 10809724483687 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52566903/250000000 : ℝ)^8339 ≤ (1265624008663/10000000000000 : ℝ)^6291 := by
    have hnat : (52566903 : ℕ)^8339*10000000000000^6291 ≤ 1265624008663^6291*250000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52566903 250000000 1265624008663 10000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392598681/10000000000 : ℝ)^8339 ≤ (44104861969947/100000000000000 : ℝ)^6291 := by
    have hnat : (5392598681 : ℕ)^8339*100000000000000^6291 ≤ 44104861969947^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392598681 10000000000 44104861969947 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312528347/10000000000 : ℝ), (-52566903/250000000 : ℝ), (5392598681/10000000000 : ℝ)] ![(10809724483687/25000000000000 : ℝ), (1265624008663/10000000000000 : ℝ), (44104861969947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312528347/10000000000 : ℝ)|^8339 ≤ (10809724483687/25000000000000 : ℝ)^6291
        have hw : |(5312528347/10000000000 : ℝ)|=(5312528347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-52566903/250000000 : ℝ)|^8339 ≤ (1265624008663/10000000000000 : ℝ)^6291
        have hw : |(-52566903/250000000 : ℝ)|=(52566903/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392598681/10000000000 : ℝ)|^8339 ≤ (44104861969947/100000000000000 : ℝ)^6291
        have hw : |(5392598681/10000000000 : ℝ)|=(5392598681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s8_6 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312528347/10000000000 : ℝ)*x 0 + (5392598681/10000000000 : ℝ)*x 1 + (-52566903/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312528347/10000000000 : ℝ)^8339 ≤ (10809724483687/25000000000000 : ℝ)^6291 := by
    have hnat : (5312528347 : ℕ)^8339*25000000000000^6291 ≤ 10809724483687^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312528347 10000000000 10809724483687 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392598681/10000000000 : ℝ)^8339 ≤ (44104861969947/100000000000000 : ℝ)^6291 := by
    have hnat : (5392598681 : ℕ)^8339*100000000000000^6291 ≤ 44104861969947^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392598681 10000000000 44104861969947 100000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52566903/250000000 : ℝ)^8339 ≤ (1265624008663/10000000000000 : ℝ)^6291 := by
    have hnat : (52566903 : ℕ)^8339*10000000000000^6291 ≤ 1265624008663^6291*250000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52566903 250000000 1265624008663 10000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312528347/10000000000 : ℝ), (5392598681/10000000000 : ℝ), (-52566903/250000000 : ℝ)] ![(10809724483687/25000000000000 : ℝ), (44104861969947/100000000000000 : ℝ), (1265624008663/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312528347/10000000000 : ℝ)|^8339 ≤ (10809724483687/25000000000000 : ℝ)^6291
        have hw : |(5312528347/10000000000 : ℝ)|=(5312528347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392598681/10000000000 : ℝ)|^8339 ≤ (44104861969947/100000000000000 : ℝ)^6291
        have hw : |(5392598681/10000000000 : ℝ)|=(5392598681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-52566903/250000000 : ℝ)|^8339 ≤ (1265624008663/10000000000000 : ℝ)^6291
        have hw : |(-52566903/250000000 : ℝ)|=(52566903/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1146_s8_7 (p : ℝ) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1091030429/2500000000 : ℝ)*x 0 + (4491803959/10000000000 : ℝ)*x 1 + (530008507/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091030429/2500000000 : ℝ)^8339 ≤ (3331710687307/10000000000000 : ℝ)^6291 := by
    have hnat : (1091030429 : ℕ)^8339*10000000000000^6291 ≤ 3331710687307^6291*2500000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091030429 2500000000 3331710687307 10000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491803959/10000000000 : ℝ)^8339 ≤ (17307658751589/50000000000000 : ℝ)^6291 := by
    have hnat : (4491803959 : ℕ)^8339*50000000000000^6291 ≤ 17307658751589^6291*10000000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491803959 10000000000 17307658751589 50000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530008507/1250000000 : ℝ)^8339 ≤ (8016893902361/25000000000000 : ℝ)^6291 := by
    have hnat : (530008507 : ℕ)^8339*25000000000000^6291 ≤ 8016893902361^6291*1250000000^8339 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530008507 1250000000 8016893902361 25000000000000 8339 6291 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8339/2048 : ℝ)) 8339 6291 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091030429/2500000000 : ℝ), (4491803959/10000000000 : ℝ), (530008507/1250000000 : ℝ)] ![(3331710687307/10000000000000 : ℝ), (17307658751589/50000000000000 : ℝ), (8016893902361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091030429/2500000000 : ℝ)|^8339 ≤ (3331710687307/10000000000000 : ℝ)^6291
        have hw : |(1091030429/2500000000 : ℝ)|=(1091030429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491803959/10000000000 : ℝ)|^8339 ≤ (17307658751589/50000000000000 : ℝ)^6291
        have hw : |(4491803959/10000000000 : ℝ)|=(4491803959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(530008507/1250000000 : ℝ)|^8339 ≤ (8016893902361/25000000000000 : ℝ)^6291
        have hw : |(530008507/1250000000 : ℝ)|=(530008507/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1146_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11359/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14051/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3513/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5679/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3513/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5679/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3513/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5679/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3513/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5679/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3513/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5679/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3513/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5679/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5679/50000 : ℝ) ^ (4169/1024 : ℝ) ≤ (712575386902789/5000000000000000000 : ℝ) := by
    have hpowers : (5679/50000 : ℝ)^4169 ≤ (712575386902789/5000000000000000000 : ℝ)^1024 := by
      have hnat : (5679 : ℕ)^4169*5000000000000000000^1024 ≤ 712575386902789^1024*50000^4169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5679 50000 712575386902789 5000000000000000000 4169 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5679/50000 : ℝ)) (X := (712575386902789/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3513/25000 : ℝ) ^ (4169/1024 : ℝ) ≤ (33899681319714843/100000000000000000000 : ℝ) := by
    have hpowers : (3513/25000 : ℝ)^4169 ≤ (33899681319714843/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3513 : ℕ)^4169*100000000000000000000^1024 ≤ 33899681319714843^1024*25000^4169 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3513 25000 33899681319714843 100000000000000000000 4169 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3513/25000 : ℝ)) (X := (33899681319714843/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500712575386902789/2500000000000000000 : ℝ) ≤ (10000700022798311/10000000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (2500712575386902789/2500000000000000000 : ℝ)^1024 ≤ (10000700022798311/10000000000000000 : ℝ)^4169 := by
      have hnat : (2500712575386902789 : ℕ)^1024*10000000000000000^4169 ≤ 10000700022798311^4169*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500712575386902789 2500000000000000000 10000700022798311 10000000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000700022798311/10000000000000000 : ℝ)) (X := (2500712575386902789/2500000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048151189057770623/100000000000000000000 : ℝ) ≤ (2500295621641691/2500000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (100048151189057770623/100000000000000000000 : ℝ)^1024 ≤ (2500295621641691/2500000000000000 : ℝ)^4169 := by
      have hnat : (100048151189057770623 : ℕ)^1024*2500000000000000^4169 ≤ 2500295621641691^4169*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048151189057770623 100000000000000000000 2500295621641691 2500000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500295621641691/2500000000000000 : ℝ)) (X := (100048151189057770623/100000000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033899681319714843/50000000000000000000 : ℝ) ≤ (10001664950335217/10000000000000000 : ℝ) ^ (4169/1024 : ℝ) := by
    have hpowers : (50033899681319714843/50000000000000000000 : ℝ)^1024 ≤ (10001664950335217/10000000000000000 : ℝ)^4169 := by
      have hnat : (50033899681319714843 : ℕ)^1024*10000000000000000^4169 ≤ 10001664950335217^4169*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033899681319714843 50000000000000000000 10001664950335217 10000000000000000 1024 4169 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001664950335217/10000000000000000 : ℝ)) (X := (50033899681319714843/50000000000000000000 : ℝ)) (by norm_num) 4169 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(712575386902789/5000000000000000000 : ℝ) ≤ ((4488487702409078581/4490000000000000000 : ℝ)+2*(160821256151/89800000000000 : ℝ)*(5679/50000 : ℝ))^(4169/1024 : ℝ) := by
    rw [show (4488487702409078581/4490000000000000000 : ℝ)+2*(160821256151/89800000000000 : ℝ)*(5679/50000 : ℝ)=(10000700022798311/10000000000000000 : ℝ) by norm_num, show 1+2*(712575386902789/5000000000000000000 : ℝ)=(2500712575386902789/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33899681319714843/100000000000000000000 : ℝ)+(712575386902789/5000000000000000000 : ℝ) ≤ ((4488487702409078581/4490000000000000000 : ℝ)+(160821256151/89800000000000 : ℝ)*((3513/25000 : ℝ)+(5679/50000 : ℝ)))^(4169/1024 : ℝ) := by
    rw [show (4488487702409078581/4490000000000000000 : ℝ)+(160821256151/89800000000000 : ℝ)*((3513/25000 : ℝ)+(5679/50000 : ℝ))=(2500295621641691/2500000000000000 : ℝ) by norm_num, show 1+(33899681319714843/100000000000000000000 : ℝ)+(712575386902789/5000000000000000000 : ℝ)=(100048151189057770623/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33899681319714843/100000000000000000000 : ℝ) ≤ ((4488487702409078581/4490000000000000000 : ℝ)+2*(160821256151/89800000000000 : ℝ)*(3513/25000 : ℝ))^(4169/1024 : ℝ) := by
    rw [show (4488487702409078581/4490000000000000000 : ℝ)+2*(160821256151/89800000000000 : ℝ)*(3513/25000 : ℝ)=(10001664950335217/10000000000000000 : ℝ) by norm_num, show 1+2*(33899681319714843/100000000000000000000 : ℝ)=(50033899681319714843/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4488487702409078581/4490000000000000000 : ℝ)*(X 1 0+X 2 0)+(160821256151/89800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (5679/50000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (4488487702409078581/4490000000000000000 : ℝ)) (alpha := (160821256151/89800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4488487702409078581/4490000000000000000 : ℝ)*(X 0 1+X 2 1)+(160821256151/89800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (5679/50000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (4488487702409078581/4490000000000000000 : ℝ)) (alpha := (160821256151/89800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4488487702409078581/4490000000000000000 : ℝ)*(X 0 2+X 1 2)+(160821256151/89800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4169/1024 : ℝ)) (lo := (5679/50000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (4488487702409078581/4490000000000000000 : ℝ)) (alpha := (160821256151/89800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2164977351/10000000000 : ℝ)*X 0 0+(1348229739/2500000000 : ℝ)*X 0 1+(5265844887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336183183/2500000000 : ℝ)*X 1 0+(-2229429897/10000000000 : ℝ)*X 1 1+(164557653/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344732731/10000000000 : ℝ)*X 2 0+(1053168979/2000000000 : ℝ)*X 2 1+(-2229429901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1091028011/2500000000 : ℝ)*X 0 0+(4239430383/10000000000 : ℝ)*X 0 1+(2246219661/5000000000 : ℝ)*X 0 2+(1091028011/2500000000 : ℝ)*X 1 0+(4239430383/10000000000 : ℝ)*X 1 1+(2246219661/5000000000 : ℝ)*X 1 2+(1091028011/2500000000 : ℝ)*X 2 0+(4239430383/10000000000 : ℝ)*X 2 1+(2246219661/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-270622779/1250000000 : ℝ)*X 0 0+(5266163997/10000000000 : ℝ)*X 0 1+(5392598681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312528347/10000000000 : ℝ)*X 1 0+(-52566903/250000000 : ℝ)*X 1 1+(5392598681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312528347/10000000000 : ℝ)*X 2 0+(5392598681/10000000000 : ℝ)*X 2 1+(-52566903/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1091030429/2500000000 : ℝ)*X 0 0+(4491803959/10000000000 : ℝ)*X 0 1+(530008507/1250000000 : ℝ)*X 0 2+(1091030429/2500000000 : ℝ)*X 1 0+(4491803959/10000000000 : ℝ)*X 1 1+(530008507/1250000000 : ℝ)*X 1 2+(1091030429/2500000000 : ℝ)*X 2 0+(4491803959/10000000000 : ℝ)*X 2 1+(530008507/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1146_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1564115255251286771045952039/224500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1395057457/100000000000000 : ℝ)*(base19) + (15817731/1250000000000 : ℝ)*(base23) + (4281351/6250000000000 : ℝ)*(lower2) + (94074523/50000000000000 : ℝ)*(upper3) + (87588779/100000000000000 : ℝ)*(upper5) + (5910986923479673/100000000000000 : ℝ)*(major0) + (5910986923479673/100000000000000 : ℝ)*(major1) + (5910986923479673/100000000000000 : ℝ)*(major2) + (7869466788594387/100000000000000 : ℝ)*(sp0) + (24592197540453/312500000000 : ℝ)*(sp1) + (7869503342583937/100000000000000 : ℝ)*(sp2) + (1976223928785127/50000000000000 : ℝ)*(sp3) + (3781940803/10000000000000 : ℝ)*(sp4) + (5287287451/25000000000000 : ℝ)*(sp7) + (1976234503360029/50000000000000 : ℝ)*(f.failure) + (7869504608002417/100000000000000 : ℝ)*(f.sum) + (35272842664447/4490000000000000000000000000 : ℝ)*base66 + (1842928759344334013/449000000000000000000000000000000 : ℝ)*base67 + (8492759081294665987/449000000000000000000000000000000 : ℝ)*base70 + (88586786295665987/449000000000000000000000000000000 : ℝ)*base72 + (14054005850397/4490000000000000000000000000 : ℝ)*base74 + (11754863722283665987/449000000000000000000000000000000 : ℝ)*base76 + (9235754527218665987/449000000000000000000000000000000 : ℝ)*base78 + (1360587935227334013/449000000000000000000000000000000 : ℝ)*base79 + (8487337016873/4490000000000000000000000000 : ℝ)*base81 + (97241011/5000000000000000000000 : ℝ)*base89 + (97241011/5000000000000000000000 : ℝ)*base91 + (97241011/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (375253637751775603800767739/44900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1527570693/100000000000000 : ℝ)*(base19) + (829969707/50000000000000 : ℝ)*(base23) + (134014579/25000000000000 : ℝ)*(lower1) + (167754821/100000000000000 : ℝ)*(upper3) + (30128199/50000000000000 : ℝ)*(lower4) + (42737873/25000000000000 : ℝ)*(upper5) + (1188157375509573/20000000000000 : ℝ)*(major0) + (1188157375509573/20000000000000 : ℝ)*(major1) + (1188157375509573/20000000000000 : ℝ)*(major2) + (1562656041/50000000000000 : ℝ)*(sp2) + (7909178288870361/100000000000000 : ℝ)*(sp4) + (1977294190324917/25000000000000 : ℝ)*(sp5) + (494323343976179/6250000000000 : ℝ)*(sp6) + (1986197593820299/50000000000000 : ℝ)*(sp7) + (1986197593820299/50000000000000 : ℝ)*(f.failure) + (7909178288870361/100000000000000 : ℝ)*(f.sum) + (436816491991/179600000000000000000000000 : ℝ)*base65 + (3823435183879294087/89800000000000000000000000000000 : ℝ)*base68 + (1056895725393294087/89800000000000000000000000000000 : ℝ)*base70 + (11418804224183705913/89800000000000000000000000000000 : ℝ)*base71 + (1933182242367/898000000000000000000000000 : ℝ)*base73 + (11892808097390105913/89800000000000000000000000000000 : ℝ)*base75 + (1380156740685494087/89800000000000000000000000000000 : ℝ)*base78 + (780656191637894087/89800000000000000000000000000000 : ℝ)*base80 + (177585519679/35920000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (4644059/5000000000000000000000 : ℝ)*base90 + (4644059/5000000000000000000000 : ℝ)*base92 + (4644059/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1146_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1146_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1146_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1146_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1146_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1146_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4169/1024 : ℝ) ≤ p) (hpb : p ≤ (8339/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149551759/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1146_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
