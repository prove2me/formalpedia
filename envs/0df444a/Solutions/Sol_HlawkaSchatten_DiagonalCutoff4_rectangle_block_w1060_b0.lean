-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1060_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:02:51.383171+00:00
-- url     : https://prove2.me/submissions/1085ada5-491c-4cc9-a82d-8aa7d777448a

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
theorem support_rectangle_w1060_s0_0 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-239754619/1250000000 : ℝ)*x 0 + (6073477093/10000000000 : ℝ)*x 1 + (4770015233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (239754619/1250000000 : ℝ)^8253 ≤ (1390174543687/12500000000000 : ℝ)^6205 := by
    have hnat : (239754619 : ℕ)^8253*12500000000000^6205 ≤ 1390174543687^6205*1250000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239754619 1250000000 1390174543687 12500000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6073477093/10000000000 : ℝ)^8253 ≤ (160993946057/312500000000 : ℝ)^6205 := by
    have hnat : (6073477093 : ℕ)^8253*312500000000^6205 ≤ 160993946057^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6073477093 10000000000 160993946057 312500000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4770015233/10000000000 : ℝ)^8253 ≤ (37360540901679/100000000000000 : ℝ)^6205 := by
    have hnat : (4770015233 : ℕ)^8253*100000000000000^6205 ≤ 37360540901679^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4770015233 10000000000 37360540901679 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-239754619/1250000000 : ℝ), (6073477093/10000000000 : ℝ), (4770015233/10000000000 : ℝ)] ![(1390174543687/12500000000000 : ℝ), (160993946057/312500000000 : ℝ), (37360540901679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-239754619/1250000000 : ℝ)|^8253 ≤ (1390174543687/12500000000000 : ℝ)^6205
        have hw : |(-239754619/1250000000 : ℝ)|=(239754619/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6073477093/10000000000 : ℝ)|^8253 ≤ (160993946057/312500000000 : ℝ)^6205
        have hw : |(6073477093/10000000000 : ℝ)|=(6073477093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4770015233/10000000000 : ℝ)|^8253 ≤ (37360540901679/100000000000000 : ℝ)^6205
        have hw : |(4770015233/10000000000 : ℝ)|=(4770015233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s0_1 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1380352833/2500000000 : ℝ)*x 0 + (-2668495401/10000000000 : ℝ)*x 1 + (4770015189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1380352833/2500000000 : ℝ)^8253 ≤ (45384973483213/100000000000000 : ℝ)^6205 := by
    have hnat : (1380352833 : ℕ)^8253*100000000000000^6205 ≤ 45384973483213^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380352833 2500000000 45384973483213 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2668495401/10000000000 : ℝ)^8253 ≤ (17254486058103/100000000000000 : ℝ)^6205 := by
    have hnat : (2668495401 : ℕ)^8253*100000000000000^6205 ≤ 17254486058103^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2668495401 10000000000 17254486058103 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4770015189/10000000000 : ℝ)^8253 ≤ (37360540443309/100000000000000 : ℝ)^6205 := by
    have hnat : (4770015189 : ℕ)^8253*100000000000000^6205 ≤ 37360540443309^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4770015189 10000000000 37360540443309 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1380352833/2500000000 : ℝ), (-2668495401/10000000000 : ℝ), (4770015189/10000000000 : ℝ)] ![(45384973483213/100000000000000 : ℝ), (17254486058103/100000000000000 : ℝ), (37360540443309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1380352833/2500000000 : ℝ)|^8253 ≤ (45384973483213/100000000000000 : ℝ)^6205
        have hw : |(1380352833/2500000000 : ℝ)|=(1380352833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2668495401/10000000000 : ℝ)|^8253 ≤ (17254486058103/100000000000000 : ℝ)^6205
        have hw : |(-2668495401/10000000000 : ℝ)|=(2668495401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4770015189/10000000000 : ℝ)|^8253 ≤ (37360540443309/100000000000000 : ℝ)^6205
        have hw : |(4770015189/10000000000 : ℝ)|=(4770015189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s0_2 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5521410383/10000000000 : ℝ)*x 0 + (1192503807/2500000000 : ℝ)*x 1 + (-33356207/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5521410383/10000000000 : ℝ)^8253 ≤ (45384963107971/100000000000000 : ℝ)^6205 := by
    have hnat : (5521410383 : ℕ)^8253*100000000000000^6205 ≤ 45384963107971^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521410383 10000000000 45384963107971 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1192503807/2500000000 : ℝ)^8253 ≤ (37360540849591/100000000000000 : ℝ)^6205 := by
    have hnat : (1192503807 : ℕ)^8253*100000000000000^6205 ≤ 37360540849591^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192503807 2500000000 37360540849591 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33356207/125000000 : ℝ)^8253 ≤ (17254496025669/100000000000000 : ℝ)^6205 := by
    have hnat : (33356207 : ℕ)^8253*100000000000000^6205 ≤ 17254496025669^6205*125000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33356207 125000000 17254496025669 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5521410383/10000000000 : ℝ), (1192503807/2500000000 : ℝ), (-33356207/125000000 : ℝ)] ![(45384963107971/100000000000000 : ℝ), (37360540849591/100000000000000 : ℝ), (17254496025669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5521410383/10000000000 : ℝ)|^8253 ≤ (45384963107971/100000000000000 : ℝ)^6205
        have hw : |(5521410383/10000000000 : ℝ)|=(5521410383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1192503807/2500000000 : ℝ)|^8253 ≤ (37360540849591/100000000000000 : ℝ)^6205
        have hw : |(1192503807/2500000000 : ℝ)|=(1192503807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-33356207/125000000 : ℝ)|^8253 ≤ (17254496025669/100000000000000 : ℝ)^6205
        have hw : |(-33356207/125000000 : ℝ)|=(33356207/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s0_3 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (841541349/2000000000 : ℝ)*x 0 + (3125187377/10000000000 : ℝ)*x 1 + (5676751997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (841541349/2000000000 : ℝ)^8253 ≤ (31619810380191/100000000000000 : ℝ)^6205 := by
    have hnat : (841541349 : ℕ)^8253*100000000000000^6205 ≤ 31619810380191^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841541349 2000000000 31619810380191 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3125187377/10000000000 : ℝ)^8253 ≤ (5322267251391/25000000000000 : ℝ)^6205 := by
    have hnat : (3125187377 : ℕ)^8253*25000000000000^6205 ≤ 5322267251391^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3125187377 10000000000 5322267251391 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5676751997/10000000000 : ℝ)^8253 ≤ (47091120598143/100000000000000 : ℝ)^6205 := by
    have hnat : (5676751997 : ℕ)^8253*100000000000000^6205 ≤ 47091120598143^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5676751997 10000000000 47091120598143 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(841541349/2000000000 : ℝ), (3125187377/10000000000 : ℝ), (5676751997/10000000000 : ℝ)] ![(31619810380191/100000000000000 : ℝ), (5322267251391/25000000000000 : ℝ), (47091120598143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(841541349/2000000000 : ℝ)|^8253 ≤ (31619810380191/100000000000000 : ℝ)^6205
        have hw : |(841541349/2000000000 : ℝ)|=(841541349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3125187377/10000000000 : ℝ)|^8253 ≤ (5322267251391/25000000000000 : ℝ)^6205
        have hw : |(3125187377/10000000000 : ℝ)|=(3125187377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5676751997/10000000000 : ℝ)|^8253 ≤ (47091120598143/100000000000000 : ℝ)^6205
        have hw : |(5676751997/10000000000 : ℝ)|=(5676751997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s0_4 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-192342861/1000000000 : ℝ)*x 0 + (4803672971/10000000000 : ℝ)*x 1 + (3019321231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (192342861/1000000000 : ℝ)^8253 ≤ (5581498304531/50000000000000 : ℝ)^6205 := by
    have hnat : (192342861 : ℕ)^8253*50000000000000^6205 ≤ 5581498304531^6205*1000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192342861 1000000000 5581498304531 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4803672971/10000000000 : ℝ)^8253 ≤ (37711577989727/100000000000000 : ℝ)^6205 := by
    have hnat : (4803672971 : ℕ)^8253*100000000000000^6205 ≤ 37711577989727^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4803672971 10000000000 37711577989727 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3019321231/5000000000 : ℝ)^8253 ≤ (51125425391659/100000000000000 : ℝ)^6205 := by
    have hnat : (3019321231 : ℕ)^8253*100000000000000^6205 ≤ 51125425391659^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3019321231 5000000000 51125425391659 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-192342861/1000000000 : ℝ), (4803672971/10000000000 : ℝ), (3019321231/5000000000 : ℝ)] ![(5581498304531/50000000000000 : ℝ), (37711577989727/100000000000000 : ℝ), (51125425391659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-192342861/1000000000 : ℝ)|^8253 ≤ (5581498304531/50000000000000 : ℝ)^6205
        have hw : |(-192342861/1000000000 : ℝ)|=(192342861/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4803672971/10000000000 : ℝ)|^8253 ≤ (37711577989727/100000000000000 : ℝ)^6205
        have hw : |(4803672971/10000000000 : ℝ)|=(4803672971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3019321231/5000000000 : ℝ)|^8253 ≤ (51125425391659/100000000000000 : ℝ)^6205
        have hw : |(3019321231/5000000000 : ℝ)|=(3019321231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s0_5 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5167663101/10000000000 : ℝ)*x 0 + (-349968163/2500000000 : ℝ)*x 1 + (6038640633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5167663101/10000000000 : ℝ)^8253 ≤ (41559001466391/100000000000000 : ℝ)^6205 := by
    have hnat : (5167663101 : ℕ)^8253*100000000000000^6205 ≤ 41559001466391^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167663101 10000000000 41559001466391 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (349968163/2500000000 : ℝ)^8253 ≤ (1463118742631/20000000000000 : ℝ)^6205 := by
    have hnat : (349968163 : ℕ)^8253*20000000000000^6205 ≤ 1463118742631^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349968163 2500000000 1463118742631 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6038640633/10000000000 : ℝ)^8253 ≤ (51125404795731/100000000000000 : ℝ)^6205 := by
    have hnat : (6038640633 : ℕ)^8253*100000000000000^6205 ≤ 51125404795731^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6038640633 10000000000 51125404795731 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5167663101/10000000000 : ℝ), (-349968163/2500000000 : ℝ), (6038640633/10000000000 : ℝ)] ![(41559001466391/100000000000000 : ℝ), (1463118742631/20000000000000 : ℝ), (51125404795731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5167663101/10000000000 : ℝ)|^8253 ≤ (41559001466391/100000000000000 : ℝ)^6205
        have hw : |(5167663101/10000000000 : ℝ)|=(5167663101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-349968163/2500000000 : ℝ)|^8253 ≤ (1463118742631/20000000000000 : ℝ)^6205
        have hw : |(-349968163/2500000000 : ℝ)|=(349968163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6038640633/10000000000 : ℝ)|^8253 ≤ (51125404795731/100000000000000 : ℝ)^6205
        have hw : |(6038640633/10000000000 : ℝ)|=(6038640633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s0_6 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1033532781/2000000000 : ℝ)*x 0 + (6038641/10000000 : ℝ)*x 1 + (-1399870821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033532781/2000000000 : ℝ)^8253 ≤ (41559010066363/100000000000000 : ℝ)^6205 := by
    have hnat : (1033532781 : ℕ)^8253*100000000000000^6205 ≤ 41559010066363^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033532781 2000000000 41559010066363 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6038641/10000000 : ℝ)^8253 ≤ (51125408928429/100000000000000 : ℝ)^6205 := by
    have hnat : (6038641 : ℕ)^8253*100000000000000^6205 ≤ 51125408928429^6205*10000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6038641 10000000 51125408928429 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1399870821/10000000000 : ℝ)^8253 ≤ (7315580986351/100000000000000 : ℝ)^6205 := by
    have hnat : (1399870821 : ℕ)^8253*100000000000000^6205 ≤ 7315580986351^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1399870821 10000000000 7315580986351 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1033532781/2000000000 : ℝ), (6038641/10000000 : ℝ), (-1399870821/10000000000 : ℝ)] ![(41559010066363/100000000000000 : ℝ), (51125408928429/100000000000000 : ℝ), (7315580986351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1033532781/2000000000 : ℝ)|^8253 ≤ (41559010066363/100000000000000 : ℝ)^6205
        have hw : |(1033532781/2000000000 : ℝ)|=(1033532781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6038641/10000000 : ℝ)|^8253 ≤ (51125408928429/100000000000000 : ℝ)^6205
        have hw : |(6038641/10000000 : ℝ)|=(6038641/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1399870821/10000000000 : ℝ)|^8253 ≤ (7315580986351/100000000000000 : ℝ)^6205
        have hw : |(-1399870821/10000000000 : ℝ)|=(1399870821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s0_7 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2109130143/5000000000 : ℝ)*x 0 + (2805430747/5000000000 : ℝ)*x 1 + (1596690107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109130143/5000000000 : ℝ)^8253 ≤ (396566711449/1250000000000 : ℝ)^6205 := by
    have hnat : (2109130143 : ℕ)^8253*1250000000000^6205 ≤ 396566711449^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109130143 5000000000 396566711449 1250000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2805430747/5000000000 : ℝ)^8253 ≤ (45278828947/97656250000 : ℝ)^6205 := by
    have hnat : (2805430747 : ℕ)^8253*97656250000^6205 ≤ 45278828947^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2805430747 5000000000 45278828947 97656250000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1596690107/5000000000 : ℝ)^8253 ≤ (4381828446043/20000000000000 : ℝ)^6205 := by
    have hnat : (1596690107 : ℕ)^8253*20000000000000^6205 ≤ 4381828446043^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596690107 5000000000 4381828446043 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2109130143/5000000000 : ℝ), (2805430747/5000000000 : ℝ), (1596690107/5000000000 : ℝ)] ![(396566711449/1250000000000 : ℝ), (45278828947/97656250000 : ℝ), (4381828446043/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2109130143/5000000000 : ℝ)|^8253 ≤ (396566711449/1250000000000 : ℝ)^6205
        have hw : |(2109130143/5000000000 : ℝ)|=(2109130143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2805430747/5000000000 : ℝ)|^8253 ≤ (45278828947/97656250000 : ℝ)^6205
        have hw : |(2805430747/5000000000 : ℝ)|=(2805430747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1596690107/5000000000 : ℝ)|^8253 ≤ (4381828446043/20000000000000 : ℝ)^6205
        have hw : |(1596690107/5000000000 : ℝ)|=(1596690107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1060_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (71/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28133/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (2063/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2063 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2063*1^512 ≤ 0^512*1^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2063/512 : ℝ) ≤ (498438479226722691/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2063 ≤ (498438479226722691/20000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2063*20000000000000000000^512 ≤ 498438479226722691^512*5^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 498438479226722691 20000000000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (498438479226722691/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2063 := by
      have hnat : (1 : ℕ)^512*1^2063 ≤ 1^2063*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20498438479226722691/20000000000000000000 : ℝ) ≤ (2012256126791339/2000000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (20498438479226722691/20000000000000000000 : ℝ)^512 ≤ (2012256126791339/2000000000000000 : ℝ)^2063 := by
      have hnat : (20498438479226722691 : ℕ)^512*2000000000000000^2063 ≤ 2012256126791339^2063*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20498438479226722691 20000000000000000000 2012256126791339 2000000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2012256126791339/2000000000000000 : ℝ)) (X := (20498438479226722691/20000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10498438479226722691/10000000000000000000 : ℝ) ≤ (1012256126791339/1000000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (10498438479226722691/10000000000000000000 : ℝ)^512 ≤ (1012256126791339/1000000000000000 : ℝ)^2063 := by
      have hnat : (10498438479226722691 : ℕ)^512*1000000000000000^2063 ≤ 1012256126791339^2063*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10498438479226722691 10000000000000000000 1012256126791339 1000000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1012256126791339/1000000000000000 : ℝ)) (X := (10498438479226722691/10000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(12256126791339/800000000000000 : ℝ)*(0 : ℝ))^(2063/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(12256126791339/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(498438479226722691/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(12256126791339/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2063/512 : ℝ) := by
    rw [show (1 : ℝ)+(12256126791339/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2012256126791339/2000000000000000 : ℝ) by norm_num, show 1+(498438479226722691/20000000000000000000 : ℝ)+(0 : ℝ)=(20498438479226722691/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(498438479226722691/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(12256126791339/800000000000000 : ℝ)*(2/5 : ℝ))^(2063/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(12256126791339/800000000000000 : ℝ)*(2/5 : ℝ)=(1012256126791339/1000000000000000 : ℝ) by norm_num, show 1+2*(498438479226722691/20000000000000000000 : ℝ)=(10498438479226722691/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(12256126791339/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12256126791339/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(12256126791339/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12256126791339/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(12256126791339/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12256126791339/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-239754619/1250000000 : ℝ)*X 0 0+(6073477093/10000000000 : ℝ)*X 0 1+(4770015233/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1380352833/2500000000 : ℝ)*X 1 0+(-2668495401/10000000000 : ℝ)*X 1 1+(4770015189/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5521410383/10000000000 : ℝ)*X 2 0+(1192503807/2500000000 : ℝ)*X 2 1+(-33356207/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((841541349/2000000000 : ℝ)*X 0 0+(3125187377/10000000000 : ℝ)*X 0 1+(5676751997/10000000000 : ℝ)*X 0 2+(841541349/2000000000 : ℝ)*X 1 0+(3125187377/10000000000 : ℝ)*X 1 1+(5676751997/10000000000 : ℝ)*X 1 2+(841541349/2000000000 : ℝ)*X 2 0+(3125187377/10000000000 : ℝ)*X 2 1+(5676751997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-192342861/1000000000 : ℝ)*X 0 0+(4803672971/10000000000 : ℝ)*X 0 1+(3019321231/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5167663101/10000000000 : ℝ)*X 1 0+(-349968163/2500000000 : ℝ)*X 1 1+(6038640633/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1033532781/2000000000 : ℝ)*X 2 0+(6038641/10000000 : ℝ)*X 2 1+(-1399870821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2109130143/5000000000 : ℝ)*X 0 0+(2805430747/5000000000 : ℝ)*X 0 1+(1596690107/5000000000 : ℝ)*X 0 2+(2109130143/5000000000 : ℝ)*X 1 0+(2805430747/5000000000 : ℝ)*X 1 1+(1596690107/5000000000 : ℝ)*X 1 2+(2109130143/5000000000 : ℝ)*X 2 0+(2805430747/5000000000 : ℝ)*X 2 1+(1596690107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52382552878892655387297/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93965491/100000000000000 : ℝ)*(base1) + (1970597/12500000000000 : ℝ)*(base16) + (1363749983/100000000000000 : ℝ)*(base19) + (1247652239/100000000000000 : ℝ)*(base23) + (264245899/100000000000000 : ℝ)*(upper3) + (579558199727841/100000000000000 : ℝ)*(major0) + (579558199727841/100000000000000 : ℝ)*(major1) + (579558199727841/100000000000000 : ℝ)*(major2) + (30687694039931/4000000000000 : ℝ)*(sp0) + (767193977531161/100000000000000 : ℝ)*(sp1) + (9589926367421/1250000000000 : ℝ)*(sp2) + (391918210080693/100000000000000 : ℝ)*(sp3) + (620002627/20000000000000 : ℝ)*(sp4) + (1281877531/50000000000000 : ℝ)*(sp7) + (78384173560249/20000000000000 : ℝ)*(f.failure) + (4794970981537/625000000000 : ℝ)*(f.sum) + (177717278710901/40000000000000000000000000000 : ℝ)*base66 + (415012287950901/80000000000000000000000000000 : ℝ)*base68 + (394981494750901/80000000000000000000000000000 : ℝ)*base70 + (666778281550901/80000000000000000000000000000 : ℝ)*base72 + (76190222849099/40000000000000000000000000000 : ℝ)*base73 + (268208933470901/80000000000000000000000000000 : ℝ)*base76 + (415423320590901/80000000000000000000000000000 : ℝ)*base78 + (111609918350901/80000000000000000000000000000 : ℝ)*base80 + (180233459590901/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (9566419/2000000000000000000000 : ℝ)*base89 + (9566419/2000000000000000000000 : ℝ)*base91 + (9566419/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (345624754704024161317707/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77721671/100000000000000 : ℝ)*(base1) + (493971657/25000000000000 : ℝ)*(base19) + (538956043/25000000000000 : ℝ)*(base23) + (362194353/100000000000000 : ℝ)*(base45) + (225491553/100000000000000 : ℝ)*(upper3) + (69916789/20000000000000 : ℝ)*(upper5) + (611693457679143/100000000000000 : ℝ)*(major0) + (611693457679143/100000000000000 : ℝ)*(major1) + (611693457679143/100000000000000 : ℝ)*(major2) + (788224757/100000000000000 : ℝ)*(sp2) + (404867333266599/50000000000000 : ℝ)*(sp4) + (809732612924899/100000000000000 : ℝ)*(sp5) + (809731644762597/100000000000000 : ℝ)*(sp6) + (51706495100557/12500000000000 : ℝ)*(sp7) + (413652038526127/100000000000000 : ℝ)*(f.failure) + (809734588811527/100000000000000 : ℝ)*(f.sum) + (20940787902477/40000000000000000000000000000 : ℝ)*base65 + (218021691582477/80000000000000000000000000000 : ℝ)*base67 + (113824591457523/80000000000000000000000000000 : ℝ)*base70 + (5039476142477/80000000000000000000000000000 : ℝ)*base71 + (69524168702477/40000000000000000000000000000 : ℝ)*base73 + (181906001262477/80000000000000000000000000000 : ℝ)*base75 + (324882562782477/80000000000000000000000000000 : ℝ)*base77 + (539582864542477/80000000000000000000000000000 : ℝ)*base79 + (16298247737523/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (8400037/10000000000000000000000 : ℝ)*base89 + (8400037/10000000000000000000000 : ℝ)*base91 + (8400037/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1060_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (71/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28133/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1060_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1060_s1_0 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064296927/5000000000 : ℝ)*x 0 + (5724017339/10000000000 : ℝ)*x 1 + (4984628197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064296927/5000000000 : ℝ)^8253 ≤ (12773959339977/100000000000000 : ℝ)^6205 := by
    have hnat : (1064296927 : ℕ)^8253*100000000000000^6205 ≤ 12773959339977^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064296927 5000000000 12773959339977 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5724017339/10000000000 : ℝ)^8253 ≤ (47613333015307/100000000000000 : ℝ)^6205 := by
    have hnat : (5724017339 : ℕ)^8253*100000000000000^6205 ≤ 47613333015307^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5724017339 10000000000 47613333015307 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4984628197/10000000000 : ℝ)^8253 ≤ (39612707630039/100000000000000 : ℝ)^6205 := by
    have hnat : (4984628197 : ℕ)^8253*100000000000000^6205 ≤ 39612707630039^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4984628197 10000000000 39612707630039 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064296927/5000000000 : ℝ), (5724017339/10000000000 : ℝ), (4984628197/10000000000 : ℝ)] ![(12773959339977/100000000000000 : ℝ), (47613333015307/100000000000000 : ℝ), (39612707630039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064296927/5000000000 : ℝ)|^8253 ≤ (12773959339977/100000000000000 : ℝ)^6205
        have hw : |(-1064296927/5000000000 : ℝ)|=(1064296927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5724017339/10000000000 : ℝ)|^8253 ≤ (47613333015307/100000000000000 : ℝ)^6205
        have hw : |(5724017339/10000000000 : ℝ)|=(5724017339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4984628197/10000000000 : ℝ)|^8253 ≤ (39612707630039/100000000000000 : ℝ)^6205
        have hw : |(4984628197/10000000000 : ℝ)|=(4984628197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s1_1 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2711823373/5000000000 : ℝ)*x 0 + (-101172987/400000000 : ℝ)*x 1 + (4984628521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711823373/5000000000 : ℝ)^8253 ≤ (44319266909581/100000000000000 : ℝ)^6205 := by
    have hnat : (2711823373 : ℕ)^8253*100000000000000^6205 ≤ 44319266909581^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711823373 5000000000 44319266909581 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (101172987/400000000 : ℝ)^8253 ≤ (16068022022979/100000000000000 : ℝ)^6205 := by
    have hnat : (101172987 : ℕ)^8253*100000000000000^6205 ≤ 16068022022979^6205*400000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101172987 400000000 16068022022979 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4984628521/10000000000 : ℝ)^8253 ≤ (19806355527347/50000000000000 : ℝ)^6205 := by
    have hnat : (4984628521 : ℕ)^8253*50000000000000^6205 ≤ 19806355527347^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4984628521 10000000000 19806355527347 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711823373/5000000000 : ℝ), (-101172987/400000000 : ℝ), (4984628521/10000000000 : ℝ)] ![(44319266909581/100000000000000 : ℝ), (16068022022979/100000000000000 : ℝ), (19806355527347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711823373/5000000000 : ℝ)|^8253 ≤ (44319266909581/100000000000000 : ℝ)^6205
        have hw : |(2711823373/5000000000 : ℝ)|=(2711823373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-101172987/400000000 : ℝ)|^8253 ≤ (16068022022979/100000000000000 : ℝ)^6205
        have hw : |(-101172987/400000000 : ℝ)|=(101172987/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4984628521/10000000000 : ℝ)|^8253 ≤ (19806355527347/50000000000000 : ℝ)^6205
        have hw : |(4984628521/10000000000 : ℝ)|=(4984628521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s1_2 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (169488977/312500000 : ℝ)*x 0 + (2492313959/5000000000 : ℝ)*x 1 + (-2529324763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (169488977/312500000 : ℝ)^8253 ≤ (8863854507897/20000000000000 : ℝ)^6205 := by
    have hnat : (169488977 : ℕ)^8253*20000000000000^6205 ≤ 8863854507897^6205*312500000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169488977 312500000 8863854507897 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2492313959/5000000000 : ℝ)^8253 ≤ (39612704681031/100000000000000 : ℝ)^6205 := by
    have hnat : (2492313959 : ℕ)^8253*100000000000000^6205 ≤ 39612704681031^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2492313959 5000000000 39612704681031 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2529324763/10000000000 : ℝ)^8253 ≤ (16068022766529/100000000000000 : ℝ)^6205 := by
    have hnat : (2529324763 : ℕ)^8253*100000000000000^6205 ≤ 16068022766529^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2529324763 10000000000 16068022766529 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(169488977/312500000 : ℝ), (2492313959/5000000000 : ℝ), (-2529324763/10000000000 : ℝ)] ![(8863854507897/20000000000000 : ℝ), (39612704681031/100000000000000 : ℝ), (16068022766529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(169488977/312500000 : ℝ)|^8253 ≤ (8863854507897/20000000000000 : ℝ)^6205
        have hw : |(169488977/312500000 : ℝ)|=(169488977/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2492313959/5000000000 : ℝ)|^8253 ≤ (39612704681031/100000000000000 : ℝ)^6205
        have hw : |(2492313959/5000000000 : ℝ)|=(2492313959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2529324763/10000000000 : ℝ)|^8253 ≤ (16068022766529/100000000000000 : ℝ)^6205
        have hw : |(-2529324763/10000000000 : ℝ)|=(2529324763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s1_3 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2162147963/5000000000 : ℝ)*x 0 + (3661363751/10000000000 : ℝ)*x 1 + (510873631/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162147963/5000000000 : ℝ)^8253 ≤ (4098802260767/12500000000000 : ℝ)^6205 := by
    have hnat : (2162147963 : ℕ)^8253*12500000000000^6205 ≤ 4098802260767^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162147963 5000000000 4098802260767 12500000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3661363751/10000000000 : ℝ)^8253 ≤ (3284962581251/12500000000000 : ℝ)^6205 := by
    have hnat : (3661363751 : ℕ)^8253*12500000000000^6205 ≤ 3284962581251^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3661363751 10000000000 3284962581251 12500000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (510873631/1000000000 : ℝ)^8253 ≤ (20464940629101/50000000000000 : ℝ)^6205 := by
    have hnat : (510873631 : ℕ)^8253*50000000000000^6205 ≤ 20464940629101^6205*1000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510873631 1000000000 20464940629101 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162147963/5000000000 : ℝ), (3661363751/10000000000 : ℝ), (510873631/1000000000 : ℝ)] ![(4098802260767/12500000000000 : ℝ), (3284962581251/12500000000000 : ℝ), (20464940629101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162147963/5000000000 : ℝ)|^8253 ≤ (4098802260767/12500000000000 : ℝ)^6205
        have hw : |(2162147963/5000000000 : ℝ)|=(2162147963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3661363751/10000000000 : ℝ)|^8253 ≤ (3284962581251/12500000000000 : ℝ)^6205
        have hw : |(3661363751/10000000000 : ℝ)|=(3661363751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(510873631/1000000000 : ℝ)|^8253 ≤ (20464940629101/50000000000000 : ℝ)^6205
        have hw : |(510873631/1000000000 : ℝ)|=(510873631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s1_4 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-85181019/400000000 : ℝ)*x 0 + (624380361/1250000000 : ℝ)*x 1 + (1142677709/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85181019/400000000 : ℝ)^8253 ≤ (12781395922787/100000000000000 : ℝ)^6205 := by
    have hnat : (85181019 : ℕ)^8253*100000000000000^6205 ≤ 12781395922787^6205*400000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85181019 400000000 12781395922787 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (624380361/1250000000 : ℝ)^8253 ≤ (39722828049701/100000000000000 : ℝ)^6205 := by
    have hnat : (624380361 : ℕ)^8253*100000000000000^6205 ≤ 39722828049701^6205*1250000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624380361 1250000000 39722828049701 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1142677709/2000000000 : ℝ)^8253 ≤ (23747888002459/50000000000000 : ℝ)^6205 := by
    have hnat : (1142677709 : ℕ)^8253*50000000000000^6205 ≤ 23747888002459^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142677709 2000000000 23747888002459 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85181019/400000000 : ℝ), (624380361/1250000000 : ℝ), (1142677709/2000000000 : ℝ)] ![(12781395922787/100000000000000 : ℝ), (39722828049701/100000000000000 : ℝ), (23747888002459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85181019/400000000 : ℝ)|^8253 ≤ (12781395922787/100000000000000 : ℝ)^6205
        have hw : |(-85181019/400000000 : ℝ)|=(85181019/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(624380361/1250000000 : ℝ)|^8253 ≤ (39722828049701/100000000000000 : ℝ)^6205
        have hw : |(624380361/1250000000 : ℝ)|=(624380361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1142677709/2000000000 : ℝ)|^8253 ≤ (23747888002459/50000000000000 : ℝ)^6205
        have hw : |(1142677709/2000000000 : ℝ)|=(1142677709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s1_5 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5234877507/10000000000 : ℝ)*x 0 + (-900281311/5000000000 : ℝ)*x 1 + (5713390109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5234877507/10000000000 : ℝ)^8253 ≤ (21139748964423/50000000000000 : ℝ)^6205 := by
    have hnat : (5234877507 : ℕ)^8253*50000000000000^6205 ≤ 21139748964423^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234877507 10000000000 21139748964423 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900281311/5000000000 : ℝ)^8253 ≤ (10224708769363/100000000000000 : ℝ)^6205 := by
    have hnat : (900281311 : ℕ)^8253*100000000000000^6205 ≤ 10224708769363^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900281311 5000000000 10224708769363 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5713390109/10000000000 : ℝ)^8253 ≤ (47495793297827/100000000000000 : ℝ)^6205 := by
    have hnat : (5713390109 : ℕ)^8253*100000000000000^6205 ≤ 47495793297827^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5713390109 10000000000 47495793297827 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5234877507/10000000000 : ℝ), (-900281311/5000000000 : ℝ), (5713390109/10000000000 : ℝ)] ![(21139748964423/50000000000000 : ℝ), (10224708769363/100000000000000 : ℝ), (47495793297827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5234877507/10000000000 : ℝ)|^8253 ≤ (21139748964423/50000000000000 : ℝ)^6205
        have hw : |(5234877507/10000000000 : ℝ)|=(5234877507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-900281311/5000000000 : ℝ)|^8253 ≤ (10224708769363/100000000000000 : ℝ)^6205
        have hw : |(-900281311/5000000000 : ℝ)|=(900281311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5713390109/10000000000 : ℝ)|^8253 ≤ (47495793297827/100000000000000 : ℝ)^6205
        have hw : |(5713390109/10000000000 : ℝ)|=(5713390109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s1_6 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2617437753/5000000000 : ℝ)*x 0 + (5713392313/10000000000 : ℝ)*x 1 + (-1800562241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2617437753/5000000000 : ℝ)^8253 ≤ (42279476433699/100000000000000 : ℝ)^6205 := by
    have hnat : (2617437753 : ℕ)^8253*100000000000000^6205 ≤ 42279476433699^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617437753 5000000000 42279476433699 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5713392313/10000000000 : ℝ)^8253 ≤ (47495817667121/100000000000000 : ℝ)^6205 := by
    have hnat : (5713392313 : ℕ)^8253*100000000000000^6205 ≤ 47495817667121^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5713392313 10000000000 47495817667121 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1800562241/10000000000 : ℝ)^8253 ≤ (5112352945857/50000000000000 : ℝ)^6205 := by
    have hnat : (1800562241 : ℕ)^8253*50000000000000^6205 ≤ 5112352945857^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800562241 10000000000 5112352945857 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2617437753/5000000000 : ℝ), (5713392313/10000000000 : ℝ), (-1800562241/10000000000 : ℝ)] ![(42279476433699/100000000000000 : ℝ), (47495817667121/100000000000000 : ℝ), (5112352945857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2617437753/5000000000 : ℝ)|^8253 ≤ (42279476433699/100000000000000 : ℝ)^6205
        have hw : |(2617437753/5000000000 : ℝ)|=(2617437753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5713392313/10000000000 : ℝ)|^8253 ≤ (47495817667121/100000000000000 : ℝ)^6205
        have hw : |(5713392313/10000000000 : ℝ)|=(5713392313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1800562241/10000000000 : ℝ)|^8253 ≤ (5112352945857/50000000000000 : ℝ)^6205
        have hw : |(-1800562241/10000000000 : ℝ)|=(1800562241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s1_7 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4326115867/10000000000 : ℝ)*x 0 + (5088345837/10000000000 : ℝ)*x 1 + (920541667/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326115867/10000000000 : ℝ)^8253 ≤ (16404387276097/50000000000000 : ℝ)^6205 := by
    have hnat : (4326115867 : ℕ)^8253*50000000000000^6205 ≤ 16404387276097^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326115867 10000000000 16404387276097 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5088345837/10000000000 : ℝ)^8253 ≤ (40712742200881/100000000000000 : ℝ)^6205 := by
    have hnat : (5088345837 : ℕ)^8253*100000000000000^6205 ≤ 40712742200881^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5088345837 10000000000 40712742200881 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (920541667/2500000000 : ℝ)^8253 ≤ (13239241619181/50000000000000 : ℝ)^6205 := by
    have hnat : (920541667 : ℕ)^8253*50000000000000^6205 ≤ 13239241619181^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920541667 2500000000 13239241619181 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326115867/10000000000 : ℝ), (5088345837/10000000000 : ℝ), (920541667/2500000000 : ℝ)] ![(16404387276097/50000000000000 : ℝ), (40712742200881/100000000000000 : ℝ), (13239241619181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326115867/10000000000 : ℝ)|^8253 ≤ (16404387276097/50000000000000 : ℝ)^6205
        have hw : |(4326115867/10000000000 : ℝ)|=(4326115867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5088345837/10000000000 : ℝ)|^8253 ≤ (40712742200881/100000000000000 : ℝ)^6205
        have hw : |(5088345837/10000000000 : ℝ)|=(5088345837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(920541667/2500000000 : ℝ)|^8253 ≤ (13239241619181/50000000000000 : ℝ)^6205
        have hw : |(920541667/2500000000 : ℝ)|=(920541667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1060_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28133/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2589/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1041/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28133/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (71/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28133/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (71/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28133/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (71/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28133/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (71/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28133/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (71/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28133/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (71/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (71/100000 : ℝ) ^ (2063/512 : ℝ) ≤ (160537/781250000000000000 : ℝ) := by
    have hpowers : (71/100000 : ℝ)^2063 ≤ (160537/781250000000000000 : ℝ)^512 := by
      have hnat : (71 : ℕ)^2063*781250000000000000^512 ≤ 160537^512*100000^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71 100000 160537 781250000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71/100000 : ℝ)) (X := (160537/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hpowhi : (28133/100000 : ℝ) ^ (2063/512 : ℝ) ≤ (150892601044940241/25000000000000000000 : ℝ) := by
    have hpowers : (28133/100000 : ℝ)^2063 ≤ (150892601044940241/25000000000000000000 : ℝ)^512 := by
      have hnat : (28133 : ℕ)^2063*25000000000000000000^512 ≤ 150892601044940241^512*100000^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28133 100000 150892601044940241 25000000000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28133/100000 : ℝ)) (X := (150892601044940241/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (390625000000160537/390625000000000000 : ℝ) ≤ (500000000000051/500000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (390625000000160537/390625000000000000 : ℝ)^512 ≤ (500000000000051/500000000000000 : ℝ)^2063 := by
      have hnat : (390625000000160537 : ℕ)^512*500000000000000^2063 ≤ 500000000000051^2063*390625000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390625000000160537 390625000000000000 500000000000051 500000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000000000051/500000000000000 : ℝ)) (X := (390625000000160537/390625000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (1006035704042003097/1000000000000000000 : ℝ) ≤ (500747283960251/500000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (1006035704042003097/1000000000000000000 : ℝ)^512 ≤ (500747283960251/500000000000000 : ℝ)^2063 := by
      have hnat : (1006035704042003097 : ℕ)^512*500000000000000^2063 ≤ 500747283960251^2063*1000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1006035704042003097 1000000000000000000 500747283960251 500000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500747283960251/500000000000000 : ℝ)) (X := (1006035704042003097/1000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12650892601044940241/12500000000000000000 : ℝ) ≤ (501494567920451/500000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (12650892601044940241/12500000000000000000 : ℝ)^512 ≤ (501494567920451/500000000000000 : ℝ)^2063 := by
      have hnat : (12650892601044940241 : ℕ)^512*500000000000000^2063 ≤ 501494567920451^2063*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12650892601044940241 12500000000000000000 501494567920451 500000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (501494567920451/500000000000000 : ℝ)) (X := (12650892601044940241/12500000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(160537/781250000000000000 : ℝ) ≤ ((2338482314279847127/2338500000000000000 : ℝ)+2*(1245473267/233850000000 : ℝ)*(71/100000 : ℝ))^(2063/512 : ℝ) := by
    rw [show (2338482314279847127/2338500000000000000 : ℝ)+2*(1245473267/233850000000 : ℝ)*(71/100000 : ℝ)=(500000000000051/500000000000000 : ℝ) by norm_num, show 1+2*(160537/781250000000000000 : ℝ)=(390625000000160537/390625000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(150892601044940241/25000000000000000000 : ℝ)+(160537/781250000000000000 : ℝ) ≤ ((2338482314279847127/2338500000000000000 : ℝ)+(1245473267/233850000000 : ℝ)*((28133/100000 : ℝ)+(71/100000 : ℝ)))^(2063/512 : ℝ) := by
    rw [show (2338482314279847127/2338500000000000000 : ℝ)+(1245473267/233850000000 : ℝ)*((28133/100000 : ℝ)+(71/100000 : ℝ))=(500747283960251/500000000000000 : ℝ) by norm_num, show 1+(150892601044940241/25000000000000000000 : ℝ)+(160537/781250000000000000 : ℝ)=(1006035704042003097/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(150892601044940241/25000000000000000000 : ℝ) ≤ ((2338482314279847127/2338500000000000000 : ℝ)+2*(1245473267/233850000000 : ℝ)*(28133/100000 : ℝ))^(2063/512 : ℝ) := by
    rw [show (2338482314279847127/2338500000000000000 : ℝ)+2*(1245473267/233850000000 : ℝ)*(28133/100000 : ℝ)=(501494567920451/500000000000000 : ℝ) by norm_num, show 1+2*(150892601044940241/25000000000000000000 : ℝ)=(12650892601044940241/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2338482314279847127/2338500000000000000 : ℝ)*(X 1 0+X 2 0)+(1245473267/233850000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (71/100000 : ℝ)) (hi := (28133/100000 : ℝ)) (c := (2338482314279847127/2338500000000000000 : ℝ)) (alpha := (1245473267/233850000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2338482314279847127/2338500000000000000 : ℝ)*(X 0 1+X 2 1)+(1245473267/233850000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (71/100000 : ℝ)) (hi := (28133/100000 : ℝ)) (c := (2338482314279847127/2338500000000000000 : ℝ)) (alpha := (1245473267/233850000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2338482314279847127/2338500000000000000 : ℝ)*(X 0 2+X 1 2)+(1245473267/233850000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (71/100000 : ℝ)) (hi := (28133/100000 : ℝ)) (c := (2338482314279847127/2338500000000000000 : ℝ)) (alpha := (1245473267/233850000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1064296927/5000000000 : ℝ)*X 0 0+(5724017339/10000000000 : ℝ)*X 0 1+(4984628197/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2711823373/5000000000 : ℝ)*X 1 0+(-101172987/400000000 : ℝ)*X 1 1+(4984628521/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((169488977/312500000 : ℝ)*X 2 0+(2492313959/5000000000 : ℝ)*X 2 1+(-2529324763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2162147963/5000000000 : ℝ)*X 0 0+(3661363751/10000000000 : ℝ)*X 0 1+(510873631/1000000000 : ℝ)*X 0 2+(2162147963/5000000000 : ℝ)*X 1 0+(3661363751/10000000000 : ℝ)*X 1 1+(510873631/1000000000 : ℝ)*X 1 2+(2162147963/5000000000 : ℝ)*X 2 0+(3661363751/10000000000 : ℝ)*X 2 1+(510873631/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-85181019/400000000 : ℝ)*X 0 0+(624380361/1250000000 : ℝ)*X 0 1+(1142677709/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5234877507/10000000000 : ℝ)*X 1 0+(-900281311/5000000000 : ℝ)*X 1 1+(5713390109/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2617437753/5000000000 : ℝ)*X 2 0+(5713392313/10000000000 : ℝ)*X 2 1+(-1800562241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4326115867/10000000000 : ℝ)*X 0 0+(5088345837/10000000000 : ℝ)*X 0 1+(920541667/2500000000 : ℝ)*X 0 2+(4326115867/10000000000 : ℝ)*X 1 0+(5088345837/10000000000 : ℝ)*X 1 1+(920541667/2500000000 : ℝ)*X 1 2+(4326115867/10000000000 : ℝ)*X 2 0+(5088345837/10000000000 : ℝ)*X 2 1+(920541667/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3341208638942771820879/1559000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1073099/1562500000000 : ℝ)*(base1) + (461513899/100000000000000 : ℝ)*(base19) + (147671347/25000000000000 : ℝ)*(base23) + (9546937/20000000000000 : ℝ)*(upper3) + (53300723/100000000000000 : ℝ)*(upper5) + (255422712885479/25000000000000 : ℝ)*(major0) + (255422712885479/25000000000000 : ℝ)*(major1) + (255422712885479/25000000000000 : ℝ)*(major2) + (676235033349253/50000000000000 : ℝ)*(sp0) + (1352472189205423/100000000000000 : ℝ)*(sp1) + (676236030016967/50000000000000 : ℝ)*(sp2) + (690907947696927/100000000000000 : ℝ)*(sp3) + (165793697/6250000000000 : ℝ)*(sp4) + (964550099/100000000000000 : ℝ)*(sp7) + (345454490462681/50000000000000 : ℝ)*(f.failure) + (676236325359661/50000000000000 : ℝ)*(f.sum) + (10555825748053/4677000000000000000000000000 : ℝ)*base65 + (33972272261235389/19487500000000000000000000000000 : ℝ)*base68 + (120853976739189611/19487500000000000000000000000000 : ℝ)*base69 + (22696671453302111/19487500000000000000000000000000 : ℝ)*base71 + (2516092696829/935400000000000000000000000 : ℝ)*base73 + (29984766027047889/19487500000000000000000000000000 : ℝ)*base76 + (1128822015027111/19487500000000000000000000000000 : ℝ)*base77 + (61510894563960389/19487500000000000000000000000000 : ℝ)*base80 + (1595070772979/233850000000000000000000000 : ℝ)*base81 + (41296589/5000000000000000000000 : ℝ)*base90 + (41296589/5000000000000000000000 : ℝ)*base92 + (41296589/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (890160773484915542948409/304492187500000000000000000000 : ℝ) := by norm_num
    linear_combination (610172763/25000000000000 : ℝ)*(base19) + (147316327/6250000000000 : ℝ)*(base23) + (42920811/20000000000000 : ℝ)*(upper2) + (386677301/100000000000000 : ℝ)*(upper3) + (128963463/25000000000000 : ℝ)*(upper5) + (131452026398511/12500000000000 : ℝ)*(major0) + (131452026398511/12500000000000 : ℝ)*(major1) + (131452026398511/12500000000000 : ℝ)*(major2) + (1203787491/10000000000000 : ℝ)*(sp1) + (6553174747/50000000000000 : ℝ)*(sp2) + (1392086596550949/100000000000000 : ℝ)*(sp4) + (1392072117984987/100000000000000 : ℝ)*(sp5) + (1392071133140223/100000000000000 : ℝ)*(sp6) + (355572864188823/50000000000000 : ℝ)*(sp7) + (355572864188823/50000000000000 : ℝ)*(f.failure) + (1392086596550949/100000000000000 : ℝ)*(f.sum) + (4004665042813/1559000000000000000000000000 : ℝ)*base66 + (85213602882103201/9743750000000000000000000000000 : ℝ)*base68 + (30903132227859451/9743750000000000000000000000000 : ℝ)*base70 + (60171960149496951/9743750000000000000000000000000 : ℝ)*base72 + (688419973471/779500000000000000000000000 : ℝ)*base74 + (9756343029690549/9743750000000000000000000000000 : ℝ)*base75 + (54524794303340701/9743750000000000000000000000000 : ℝ)*base78 + (59536664161234451/9743750000000000000000000000000 : ℝ)*base80 + (2945917829617/1559000000000000000000000000 : ℝ)*base82 + (36448413/5000000000000000000000 : ℝ)*base89 + (36448413/5000000000000000000000 : ℝ)*base91 + (36448413/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1060_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28133/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2589/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1041/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1060_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1060_s2_0 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-21863563/100000000 : ℝ)*x 0 + (5527157323/10000000000 : ℝ)*x 1 + (5144847597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21863563/100000000 : ℝ)^8253 ≤ (3309265508349/25000000000000 : ℝ)^6205 := by
    have hnat : (21863563 : ℕ)^8253*25000000000000^6205 ≤ 3309265508349^6205*100000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21863563 100000000 3309265508349 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5527157323/10000000000 : ℝ)^8253 ≤ (22723902066181/50000000000000 : ℝ)^6205 := by
    have hnat : (5527157323 : ℕ)^8253*50000000000000^6205 ≤ 22723902066181^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5527157323 10000000000 22723902066181 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5144847597/10000000000 : ℝ)^8253 ≤ (41315133824327/100000000000000 : ℝ)^6205 := by
    have hnat : (5144847597 : ℕ)^8253*100000000000000^6205 ≤ 41315133824327^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144847597 10000000000 41315133824327 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21863563/100000000 : ℝ), (5527157323/10000000000 : ℝ), (5144847597/10000000000 : ℝ)] ![(3309265508349/25000000000000 : ℝ), (22723902066181/50000000000000 : ℝ), (41315133824327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21863563/100000000 : ℝ)|^8253 ≤ (3309265508349/25000000000000 : ℝ)^6205
        have hw : |(-21863563/100000000 : ℝ)|=(21863563/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5527157323/10000000000 : ℝ)|^8253 ≤ (22723902066181/50000000000000 : ℝ)^6205
        have hw : |(5527157323/10000000000 : ℝ)|=(5527157323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5144847597/10000000000 : ℝ)|^8253 ≤ (41315133824327/100000000000000 : ℝ)^6205
        have hw : |(5144847597/10000000000 : ℝ)|=(5144847597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s2_1 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2688737431/5000000000 : ℝ)*x 0 + (-2385785071/10000000000 : ℝ)*x 1 + (5144849/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688737431/5000000000 : ℝ)^8253 ≤ (5477269033171/12500000000000 : ℝ)^6205 := by
    have hnat : (2688737431 : ℕ)^8253*12500000000000^6205 ≤ 5477269033171^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688737431 5000000000 5477269033171 12500000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2385785071/10000000000 : ℝ)^8253 ≤ (2973339781031/20000000000000 : ℝ)^6205 := by
    have hnat : (2385785071 : ℕ)^8253*20000000000000^6205 ≤ 2973339781031^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2385785071 10000000000 2973339781031 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5144849/10000000 : ℝ)^8253 ≤ (41315148809591/100000000000000 : ℝ)^6205 := by
    have hnat : (5144849 : ℕ)^8253*100000000000000^6205 ≤ 41315148809591^6205*10000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144849 10000000 41315148809591 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688737431/5000000000 : ℝ), (-2385785071/10000000000 : ℝ), (5144849/10000000 : ℝ)] ![(5477269033171/12500000000000 : ℝ), (2973339781031/20000000000000 : ℝ), (41315148809591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688737431/5000000000 : ℝ)|^8253 ≤ (5477269033171/12500000000000 : ℝ)^6205
        have hw : |(2688737431/5000000000 : ℝ)|=(2688737431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2385785071/10000000000 : ℝ)|^8253 ≤ (2973339781031/20000000000000 : ℝ)^6205
        have hw : |(-2385785071/10000000000 : ℝ)|=(2385785071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5144849/10000000 : ℝ)|^8253 ≤ (41315148809591/100000000000000 : ℝ)^6205
        have hw : |(5144849/10000000 : ℝ)|=(5144849/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s2_2 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1344368763/2500000000 : ℝ)*x 0 + (5144848711/10000000000 : ℝ)*x 1 + (-596446299/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344368763/2500000000 : ℝ)^8253 ≤ (10954538581143/25000000000000 : ℝ)^6205 := by
    have hnat : (1344368763 : ℕ)^8253*25000000000000^6205 ≤ 10954538581143^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344368763 2500000000 10954538581143 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5144848711/10000000000 : ℝ)^8253 ≤ (20657572861409/50000000000000 : ℝ)^6205 := by
    have hnat : (5144848711 : ℕ)^8253*50000000000000^6205 ≤ 20657572861409^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144848711 10000000000 20657572861409 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (596446299/2500000000 : ℝ)^8253 ≤ (14866699941163/100000000000000 : ℝ)^6205 := by
    have hnat : (596446299 : ℕ)^8253*100000000000000^6205 ≤ 14866699941163^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596446299 2500000000 14866699941163 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344368763/2500000000 : ℝ), (5144848711/10000000000 : ℝ), (-596446299/2500000000 : ℝ)] ![(10954538581143/25000000000000 : ℝ), (20657572861409/50000000000000 : ℝ), (14866699941163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344368763/2500000000 : ℝ)|^8253 ≤ (10954538581143/25000000000000 : ℝ)^6205
        have hw : |(1344368763/2500000000 : ℝ)|=(1344368763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5144848711/10000000000 : ℝ)|^8253 ≤ (20657572861409/50000000000000 : ℝ)^6205
        have hw : |(5144848711/10000000000 : ℝ)|=(5144848711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-596446299/2500000000 : ℝ)|^8253 ≤ (14866699941163/100000000000000 : ℝ)^6205
        have hw : |(-596446299/2500000000 : ℝ)|=(596446299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s2_3 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4363694941/10000000000 : ℝ)*x 0 + (1001426723/2500000000 : ℝ)*x 1 + (1188520201/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363694941/10000000000 : ℝ)^8253 ≤ (16594188463859/50000000000000 : ℝ)^6205 := by
    have hnat : (4363694941 : ℕ)^8253*50000000000000^6205 ≤ 16594188463859^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363694941 10000000000 16594188463859 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001426723/2500000000 : ℝ)^8253 ≤ (29616987473643/100000000000000 : ℝ)^6205 := by
    have hnat : (1001426723 : ℕ)^8253*100000000000000^6205 ≤ 29616987473643^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001426723 2500000000 29616987473643 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1188520201/2500000000 : ℝ)^8253 ≤ (37194635590403/100000000000000 : ℝ)^6205 := by
    have hnat : (1188520201 : ℕ)^8253*100000000000000^6205 ≤ 37194635590403^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1188520201 2500000000 37194635590403 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363694941/10000000000 : ℝ), (1001426723/2500000000 : ℝ), (1188520201/2500000000 : ℝ)] ![(16594188463859/50000000000000 : ℝ), (29616987473643/100000000000000 : ℝ), (37194635590403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363694941/10000000000 : ℝ)|^8253 ≤ (16594188463859/50000000000000 : ℝ)^6205
        have hw : |(4363694941/10000000000 : ℝ)|=(4363694941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1001426723/2500000000 : ℝ)|^8253 ≤ (29616987473643/100000000000000 : ℝ)^6205
        have hw : |(1001426723/2500000000 : ℝ)|=(1001426723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1188520201/2500000000 : ℝ)|^8253 ≤ (37194635590403/100000000000000 : ℝ)^6205
        have hw : |(1188520201/2500000000 : ℝ)|=(1188520201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s2_4 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-273310501/1250000000 : ℝ)*x 0 + (5147641867/10000000000 : ℝ)*x 1 + (5524333867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273310501/1250000000 : ℝ)^8253 ≤ (6619045217819/50000000000000 : ℝ)^6205 := by
    have hnat : (273310501 : ℕ)^8253*50000000000000^6205 ≤ 6619045217819^6205*1250000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273310501 1250000000 6619045217819 50000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5147641867/10000000000 : ℝ)^8253 ≤ (41344981739113/100000000000000 : ℝ)^6205 := by
    have hnat : (5147641867 : ℕ)^8253*100000000000000^6205 ≤ 41344981739113^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5147641867 10000000000 41344981739113 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5524333867/10000000000 : ℝ)^8253 ≤ (5677115976449/12500000000000 : ℝ)^6205 := by
    have hnat : (5524333867 : ℕ)^8253*12500000000000^6205 ≤ 5677115976449^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5524333867 10000000000 5677115976449 12500000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-273310501/1250000000 : ℝ), (5147641867/10000000000 : ℝ), (5524333867/10000000000 : ℝ)] ![(6619045217819/50000000000000 : ℝ), (41344981739113/100000000000000 : ℝ), (5677115976449/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-273310501/1250000000 : ℝ)|^8253 ≤ (6619045217819/50000000000000 : ℝ)^6205
        have hw : |(-273310501/1250000000 : ℝ)|=(273310501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5147641867/10000000000 : ℝ)|^8253 ≤ (41344981739113/100000000000000 : ℝ)^6205
        have hw : |(5147641867/10000000000 : ℝ)|=(5147641867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5524333867/10000000000 : ℝ)|^8253 ≤ (5677115976449/12500000000000 : ℝ)^6205
        have hw : |(5524333867/10000000000 : ℝ)|=(5524333867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s2_5 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2640508427/5000000000 : ℝ)*x 0 + (-2006301157/10000000000 : ℝ)*x 1 + (2762166973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640508427/5000000000 : ℝ)^8253 ≤ (2673490979377/6250000000000 : ℝ)^6205 := by
    have hnat : (2640508427 : ℕ)^8253*6250000000000^6205 ≤ 2673490979377^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640508427 5000000000 2673490979377 6250000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2006301157/10000000000 : ℝ)^8253 ≤ (11807215646837/100000000000000 : ℝ)^6205 := by
    have hnat : (2006301157 : ℕ)^8253*100000000000000^6205 ≤ 11807215646837^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006301157 10000000000 11807215646837 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2762166973/5000000000 : ℝ)^8253 ≤ (9083385735087/20000000000000 : ℝ)^6205 := by
    have hnat : (2762166973 : ℕ)^8253*20000000000000^6205 ≤ 9083385735087^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2762166973 5000000000 9083385735087 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640508427/5000000000 : ℝ), (-2006301157/10000000000 : ℝ), (2762166973/5000000000 : ℝ)] ![(2673490979377/6250000000000 : ℝ), (11807215646837/100000000000000 : ℝ), (9083385735087/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640508427/5000000000 : ℝ)|^8253 ≤ (2673490979377/6250000000000 : ℝ)^6205
        have hw : |(2640508427/5000000000 : ℝ)|=(2640508427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2006301157/10000000000 : ℝ)|^8253 ≤ (11807215646837/100000000000000 : ℝ)^6205
        have hw : |(-2006301157/10000000000 : ℝ)|=(2006301157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2762166973/5000000000 : ℝ)|^8253 ≤ (9083385735087/20000000000000 : ℝ)^6205
        have hw : |(2762166973/5000000000 : ℝ)|=(2762166973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s2_6 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1056203419/2000000000 : ℝ)*x 0 + (5524333781/10000000000 : ℝ)*x 1 + (-1003150527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056203419/2000000000 : ℝ)^8253 ≤ (10693964566603/25000000000000 : ℝ)^6205 := by
    have hnat : (1056203419 : ℕ)^8253*25000000000000^6205 ≤ 10693964566603^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056203419 2000000000 10693964566603 25000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5524333781/10000000000 : ℝ)^8253 ≤ (9083385374241/20000000000000 : ℝ)^6205 := by
    have hnat : (5524333781 : ℕ)^8253*20000000000000^6205 ≤ 9083385374241^6205*10000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5524333781 10000000000 9083385374241 20000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003150527/5000000000 : ℝ)^8253 ≤ (368975463769/3125000000000 : ℝ)^6205 := by
    have hnat : (1003150527 : ℕ)^8253*3125000000000^6205 ≤ 368975463769^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003150527 5000000000 368975463769 3125000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056203419/2000000000 : ℝ), (5524333781/10000000000 : ℝ), (-1003150527/5000000000 : ℝ)] ![(10693964566603/25000000000000 : ℝ), (9083385374241/20000000000000 : ℝ), (368975463769/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056203419/2000000000 : ℝ)|^8253 ≤ (10693964566603/25000000000000 : ℝ)^6205
        have hw : |(1056203419/2000000000 : ℝ)|=(1056203419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5524333781/10000000000 : ℝ)|^8253 ≤ (9083385374241/20000000000000 : ℝ)^6205
        have hw : |(5524333781/10000000000 : ℝ)|=(5524333781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1003150527/5000000000 : ℝ)|^8253 ≤ (368975463769/3125000000000 : ℝ)^6205
        have hw : |(-1003150527/5000000000 : ℝ)|=(1003150527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1060_s2_7 (p : ℝ) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872788811/2000000000 : ℝ)*x 0 + (1187153977/2500000000 : ℝ)*x 1 + (2005615513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872788811/2000000000 : ℝ)^8253 ≤ (33190896947313/100000000000000 : ℝ)^6205 := by
    have hnat : (872788811 : ℕ)^8253*100000000000000^6205 ≤ 33190896947313^6205*2000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872788811 2000000000 33190896947313 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1187153977/2500000000 : ℝ)^8253 ≤ (37137778675087/100000000000000 : ℝ)^6205 := by
    have hnat : (1187153977 : ℕ)^8253*100000000000000^6205 ≤ 37137778675087^6205*2500000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187153977 2500000000 37137778675087 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2005615513/5000000000 : ℝ)^8253 ≤ (29671324363331/100000000000000 : ℝ)^6205 := by
    have hnat : (2005615513 : ℕ)^8253*100000000000000^6205 ≤ 29671324363331^6205*5000000000^8253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005615513 5000000000 29671324363331 100000000000000 8253 6205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8253/2048 : ℝ)) 8253 6205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872788811/2000000000 : ℝ), (1187153977/2500000000 : ℝ), (2005615513/5000000000 : ℝ)] ![(33190896947313/100000000000000 : ℝ), (37137778675087/100000000000000 : ℝ), (29671324363331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872788811/2000000000 : ℝ)|^8253 ≤ (33190896947313/100000000000000 : ℝ)^6205
        have hw : |(872788811/2000000000 : ℝ)|=(872788811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1187153977/2500000000 : ℝ)|^8253 ≤ (37137778675087/100000000000000 : ℝ)^6205
        have hw : |(1187153977/2500000000 : ℝ)|=(1187153977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2005615513/5000000000 : ℝ)|^8253 ≤ (29671324363331/100000000000000 : ℝ)^6205
        have hw : |(2005615513/5000000000 : ℝ)|=(2005615513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1060_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1041/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2589/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4341/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16761/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1041/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2589/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1041/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2589/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1041/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2589/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1041/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2589/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1041/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2589/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1041/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2589/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2589/50000 : ℝ) ^ (2063/512 : ℝ) ≤ (164784803807663/25000000000000000000 : ℝ) := by
    have hpowers : (2589/50000 : ℝ)^2063 ≤ (164784803807663/25000000000000000000 : ℝ)^512 := by
      have hnat : (2589 : ℕ)^2063*25000000000000000000^512 ≤ 164784803807663^512*50000^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2589 50000 164784803807663 25000000000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2589/50000 : ℝ)) (X := (164784803807663/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1041/5000 : ℝ) ^ (2063/512 : ℝ) ≤ (89727696788105551/50000000000000000000 : ℝ) := by
    have hpowers : (1041/5000 : ℝ)^2063 ≤ (89727696788105551/50000000000000000000 : ℝ)^512 := by
      have hnat : (1041 : ℕ)^2063*50000000000000000000^512 ≤ 89727696788105551^512*5000^2063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1041 5000 89727696788105551 50000000000000000000 2063 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1041/5000 : ℝ)) (X := (89727696788105551/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500164784803807663/12500000000000000000 : ℝ) ≤ (1250004089646217/1250000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (12500164784803807663/12500000000000000000 : ℝ)^512 ≤ (1250004089646217/1250000000000000 : ℝ)^2063 := by
      have hnat : (12500164784803807663 : ℕ)^512*1250000000000000^2063 ≤ 1250004089646217^2063*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500164784803807663 12500000000000000000 1250004089646217 1250000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250004089646217/1250000000000000 : ℝ)) (X := (12500164784803807663/12500000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50090057266395720877/50000000000000000000 : ℝ) ≤ (500223354988427/500000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (50090057266395720877/50000000000000000000 : ℝ)^512 ≤ (500223354988427/500000000000000 : ℝ)^2063 := by
      have hnat : (50090057266395720877 : ℕ)^512*500000000000000^2063 ≤ 500223354988427^2063*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50090057266395720877 50000000000000000000 500223354988427 500000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500223354988427/500000000000000 : ℝ)) (X := (50090057266395720877/50000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25089727696788105551/25000000000000000000 : ℝ) ≤ (625556342647959/625000000000000 : ℝ) ^ (2063/512 : ℝ) := by
    have hpowers : (25089727696788105551/25000000000000000000 : ℝ)^512 ≤ (625556342647959/625000000000000 : ℝ)^2063 := by
      have hnat : (25089727696788105551 : ℕ)^512*625000000000000^2063 ≤ 625556342647959^2063*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25089727696788105551 25000000000000000000 625556342647959 625000000000000 512 2063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625556342647959/625000000000000 : ℝ)) (X := (25089727696788105551/25000000000000000000 : ℝ)) (by norm_num) 2063 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(164784803807663/25000000000000000000 : ℝ) ≤ ((814450985915498939/814687500000000000 : ℝ)+2*(1108595649701/391050000000000 : ℝ)*(2589/50000 : ℝ))^(2063/512 : ℝ) := by
    rw [show (814450985915498939/814687500000000000 : ℝ)+2*(1108595649701/391050000000000 : ℝ)*(2589/50000 : ℝ)=(1250004089646217/1250000000000000 : ℝ) by norm_num, show 1+2*(164784803807663/25000000000000000000 : ℝ)=(12500164784803807663/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(89727696788105551/50000000000000000000 : ℝ)+(164784803807663/25000000000000000000 : ℝ) ≤ ((814450985915498939/814687500000000000 : ℝ)+(1108595649701/391050000000000 : ℝ)*((1041/5000 : ℝ)+(2589/50000 : ℝ)))^(2063/512 : ℝ) := by
    rw [show (814450985915498939/814687500000000000 : ℝ)+(1108595649701/391050000000000 : ℝ)*((1041/5000 : ℝ)+(2589/50000 : ℝ))=(500223354988427/500000000000000 : ℝ) by norm_num, show 1+(89727696788105551/50000000000000000000 : ℝ)+(164784803807663/25000000000000000000 : ℝ)=(50090057266395720877/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(89727696788105551/50000000000000000000 : ℝ) ≤ ((814450985915498939/814687500000000000 : ℝ)+2*(1108595649701/391050000000000 : ℝ)*(1041/5000 : ℝ))^(2063/512 : ℝ) := by
    rw [show (814450985915498939/814687500000000000 : ℝ)+2*(1108595649701/391050000000000 : ℝ)*(1041/5000 : ℝ)=(625556342647959/625000000000000 : ℝ) by norm_num, show 1+2*(89727696788105551/50000000000000000000 : ℝ)=(25089727696788105551/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (814450985915498939/814687500000000000 : ℝ)*(X 1 0+X 2 0)+(1108595649701/391050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (2589/50000 : ℝ)) (hi := (1041/5000 : ℝ)) (c := (814450985915498939/814687500000000000 : ℝ)) (alpha := (1108595649701/391050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (814450985915498939/814687500000000000 : ℝ)*(X 0 1+X 2 1)+(1108595649701/391050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (2589/50000 : ℝ)) (hi := (1041/5000 : ℝ)) (c := (814450985915498939/814687500000000000 : ℝ)) (alpha := (1108595649701/391050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (814450985915498939/814687500000000000 : ℝ)*(X 0 2+X 1 2)+(1108595649701/391050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2063/512 : ℝ)) (lo := (2589/50000 : ℝ)) (hi := (1041/5000 : ℝ)) (c := (814450985915498939/814687500000000000 : ℝ)) (alpha := (1108595649701/391050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-21863563/100000000 : ℝ)*X 0 0+(5527157323/10000000000 : ℝ)*X 0 1+(5144847597/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2688737431/5000000000 : ℝ)*X 1 0+(-2385785071/10000000000 : ℝ)*X 1 1+(5144849/10000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1344368763/2500000000 : ℝ)*X 2 0+(5144848711/10000000000 : ℝ)*X 2 1+(-596446299/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4363694941/10000000000 : ℝ)*X 0 0+(1001426723/2500000000 : ℝ)*X 0 1+(1188520201/2500000000 : ℝ)*X 0 2+(4363694941/10000000000 : ℝ)*X 1 0+(1001426723/2500000000 : ℝ)*X 1 1+(1188520201/2500000000 : ℝ)*X 1 2+(4363694941/10000000000 : ℝ)*X 2 0+(1001426723/2500000000 : ℝ)*X 2 1+(1188520201/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-273310501/1250000000 : ℝ)*X 0 0+(5147641867/10000000000 : ℝ)*X 0 1+(5524333867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2640508427/5000000000 : ℝ)*X 1 0+(-2006301157/10000000000 : ℝ)*X 1 1+(2762166973/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1056203419/2000000000 : ℝ)*X 2 0+(5524333781/10000000000 : ℝ)*X 2 1+(-1003150527/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872788811/2000000000 : ℝ)*X 0 0+(1187153977/2500000000 : ℝ)*X 0 1+(2005615513/5000000000 : ℝ)*X 0 2+(872788811/2000000000 : ℝ)*X 1 0+(1187153977/2500000000 : ℝ)*X 1 1+(2005615513/5000000000 : ℝ)*X 1 2+(872788811/2000000000 : ℝ)*X 2 0+(1187153977/2500000000 : ℝ)*X 2 1+(2005615513/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1060_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (407599399418227734822467/148125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4611831/2500000000000 : ℝ)*(base1) + (58132529/2500000000000 : ℝ)*(base19) + (2417721909/100000000000000 : ℝ)*(base23) + (127266767/50000000000000 : ℝ)*(upper3) + (202285129/100000000000000 : ℝ)*(upper5) + (39519885336041/2000000000000 : ℝ)*(major0) + (39519885336041/2000000000000 : ℝ)*(major1) + (39519885336041/2000000000000 : ℝ)*(major2) + (130785529110681/5000000000000 : ℝ)*(sp0) + (261573828473197/10000000000000 : ℝ)*(sp1) + (130786909615561/5000000000000 : ℝ)*(sp2) + (668119349448213/50000000000000 : ℝ)*(sp3) + (30212292749/100000000000000 : ℝ)*(sp4) + (8948477101/100000000000000 : ℝ)*(sp7) + (83515489490423/6250000000000 : ℝ)*(f.failure) + (261574061003313/10000000000000 : ℝ)*(f.sum) + (1013519472601/711000000000000000000000000 : ℝ)*base65 + (9505935718943/6943359375000000000000000000 : ℝ)*base67 + (951090780065551/222187500000000000000000000000 : ℝ)*base69 + (137204656756801/222187500000000000000000000000 : ℝ)*base71 + (143670697151/71100000000000000000000000 : ℝ)*base74 + (11132094335773/444375000000000000000000000000 : ℝ)*base76 + (873323997913051/222187500000000000000000000000 : ℝ)*base77 + (3193942150107977/444375000000000000000000000000 : ℝ)*base79 + (56187279149/71100000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (378013/625000000000000000000 : ℝ)*base89 + (378013/625000000000000000000 : ℝ)*base91 + (378013/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (321336798735864086035749593/40734375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (152972231/10000000000000 : ℝ)*(base19) + (883933083/50000000000000 : ℝ)*(base23) + (205275017/100000000000000 : ℝ)*(upper3) + (40893237/100000000000000 : ℝ)*(lower4) + (21143131/12500000000000 : ℝ)*(upper5) + (2005416405657743/100000000000000 : ℝ)*(major0) + (2005416405657743/100000000000000 : ℝ)*(major1) + (2005416405657743/100000000000000 : ℝ)*(major2) + (13184966789/100000000000000 : ℝ)*(sp1) + (3070198821/20000000000000 : ℝ)*(sp2) + (66367206686621/2500000000000 : ℝ)*(sp4) + (1327336776387871/50000000000000 : ℝ)*(sp5) + (265467114860457/10000000000000 : ℝ)*(sp6) + (678072140448813/50000000000000 : ℝ)*(sp7) + (678072140448813/50000000000000 : ℝ)*(f.failure) + (66367206686621/2500000000000 : ℝ)*(f.sum) + (2337148824451/611015625000000000000000000 : ℝ)*base66 + (712061969742827219/244406250000000000000000000000000 : ℝ)*base68 + (292609487168702219/244406250000000000000000000000000 : ℝ)*base70 + (1909539319289327219/244406250000000000000000000000000 : ℝ)*base72 + (120408901805711/39105000000000000000000000000 : ℝ)*base73 + (3624370799709077219/244406250000000000000000000000000 : ℝ)*base76 + (1045558049992577219/244406250000000000000000000000000 : ℝ)*base78 + (2277574808912983469/244406250000000000000000000000000 : ℝ)*base80 + (84673152882253/19552500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (9745103/5000000000000000000000 : ℝ)*base89 + (9745103/5000000000000000000000 : ℝ)*base91 + (9745103/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1060_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1041/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2589/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4341/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16761/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1060_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1060_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4341/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16761/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1060_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1060_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1060_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2063/512 : ℝ) ≤ p) (hpb : p ≤ (8253/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147876331/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4341/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16761/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1060_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
