-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1077_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:14:55.934223+00:00
-- url     : https://prove2.me/submissions/6c7a07f1-cdec-45fe-991c-d5a24b24820a

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
theorem support_rectangle_w1077_s9_0 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672473333/5000000000 : ℝ)*x 0 + (1316170057/2500000000 : ℝ)*x 1 + (-452808537/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672473333/5000000000 : ℝ)^4135 ≤ (43490528303161/100000000000000 : ℝ)^3111 := by
    have hnat : (2672473333 : ℕ)^4135*100000000000000^3111 ≤ 43490528303161^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672473333 5000000000 43490528303161 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316170057/2500000000 : ℝ)^4135 ≤ (42624598918779/100000000000000 : ℝ)^3111 := by
    have hnat : (1316170057 : ℕ)^4135*100000000000000^3111 ≤ 42624598918779^3111*2500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316170057 2500000000 42624598918779 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452808537/2000000000 : ℝ)^4135 ≤ (6942436382199/50000000000000 : ℝ)^3111 := by
    have hnat : (452808537 : ℕ)^4135*50000000000000^3111 ≤ 6942436382199^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452808537 2000000000 6942436382199 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672473333/5000000000 : ℝ), (1316170057/2500000000 : ℝ), (-452808537/2000000000 : ℝ)] ![(43490528303161/100000000000000 : ℝ), (42624598918779/100000000000000 : ℝ), (6942436382199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672473333/5000000000 : ℝ)|^4135 ≤ (43490528303161/100000000000000 : ℝ)^3111
        have hw : |(2672473333/5000000000 : ℝ)|=(2672473333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316170057/2500000000 : ℝ)|^4135 ≤ (42624598918779/100000000000000 : ℝ)^3111
        have hw : |(1316170057/2500000000 : ℝ)|=(1316170057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-452808537/2000000000 : ℝ)|^4135 ≤ (6942436382199/50000000000000 : ℝ)^3111
        have hw : |(-452808537/2000000000 : ℝ)|=(452808537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s9_1 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4373913993/10000000000 : ℝ)*x 0 + (4248644409/10000000000 : ℝ)*x 1 + (4502917649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373913993/10000000000 : ℝ)^4135 ≤ (16658313305637/50000000000000 : ℝ)^3111 := by
    have hnat : (4373913993 : ℕ)^4135*50000000000000^3111 ≤ 16658313305637^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373913993 10000000000 16658313305637 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4248644409/10000000000 : ℝ)^4135 ≤ (16027186396867/50000000000000 : ℝ)^3111 := by
    have hnat : (4248644409 : ℕ)^4135*50000000000000^3111 ≤ 16027186396867^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248644409 10000000000 16027186396867 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4502917649/10000000000 : ℝ)^4135 ≤ (34629000588961/100000000000000 : ℝ)^3111 := by
    have hnat : (4502917649 : ℕ)^4135*100000000000000^3111 ≤ 34629000588961^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502917649 10000000000 34629000588961 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373913993/10000000000 : ℝ), (4248644409/10000000000 : ℝ), (4502917649/10000000000 : ℝ)] ![(16658313305637/50000000000000 : ℝ), (16027186396867/50000000000000 : ℝ), (34629000588961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373913993/10000000000 : ℝ)|^4135 ≤ (16658313305637/50000000000000 : ℝ)^3111
        have hw : |(4373913993/10000000000 : ℝ)|=(4373913993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4248644409/10000000000 : ℝ)|^4135 ≤ (16027186396867/50000000000000 : ℝ)^3111
        have hw : |(4248644409/10000000000 : ℝ)|=(4248644409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4502917649/10000000000 : ℝ)|^4135 ≤ (34629000588961/100000000000000 : ℝ)^3111
        have hw : |(4502917649/10000000000 : ℝ)|=(4502917649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s9_2 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-87934707/400000000 : ℝ)*x 0 + (5265004671/10000000000 : ℝ)*x 1 + (1078762539/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87934707/400000000 : ℝ)^4135 ≤ (13352101291191/100000000000000 : ℝ)^3111 := by
    have hnat : (87934707 : ℕ)^4135*100000000000000^3111 ≤ 13352101291191^3111*400000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87934707 400000000 13352101291191 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265004671/10000000000 : ℝ)^4135 ≤ (2664255648449/6250000000000 : ℝ)^3111 := by
    have hnat : (5265004671 : ℕ)^4135*6250000000000^3111 ≤ 2664255648449^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265004671 10000000000 2664255648449 6250000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078762539/2000000000 : ℝ)^4135 ≤ (5502476039929/12500000000000 : ℝ)^3111 := by
    have hnat : (1078762539 : ℕ)^4135*12500000000000^3111 ≤ 5502476039929^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078762539 2000000000 5502476039929 12500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87934707/400000000 : ℝ), (5265004671/10000000000 : ℝ), (1078762539/2000000000 : ℝ)] ![(13352101291191/100000000000000 : ℝ), (2664255648449/6250000000000 : ℝ), (5502476039929/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87934707/400000000 : ℝ)|^4135 ≤ (13352101291191/100000000000000 : ℝ)^3111
        have hw : |(-87934707/400000000 : ℝ)|=(87934707/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265004671/10000000000 : ℝ)|^4135 ≤ (2664255648449/6250000000000 : ℝ)^3111
        have hw : |(5265004671/10000000000 : ℝ)|=(5265004671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078762539/2000000000 : ℝ)|^4135 ≤ (5502476039929/12500000000000 : ℝ)^3111
        have hw : |(1078762539/2000000000 : ℝ)|=(1078762539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s9_3 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328077659/2500000000 : ℝ)*x 0 + (-66715969/312500000 : ℝ)*x 1 + (5393811771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328077659/2500000000 : ℝ)^4135 ≤ (21568962290401/50000000000000 : ℝ)^3111 := by
    have hnat : (1328077659 : ℕ)^4135*50000000000000^3111 ≤ 21568962290401^3111*2500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328077659 2500000000 21568962290401 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66715969/312500000 : ℝ)^4135 ≤ (6421138551533/50000000000000 : ℝ)^3111 := by
    have hnat : (66715969 : ℕ)^4135*50000000000000^3111 ≤ 6421138551533^3111*312500000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66715969 312500000 6421138551533 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393811771/10000000000 : ℝ)^4135 ≤ (8803959659277/20000000000000 : ℝ)^3111 := by
    have hnat : (5393811771 : ℕ)^4135*20000000000000^3111 ≤ 8803959659277^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393811771 10000000000 8803959659277 20000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328077659/2500000000 : ℝ), (-66715969/312500000 : ℝ), (5393811771/10000000000 : ℝ)] ![(21568962290401/50000000000000 : ℝ), (6421138551533/50000000000000 : ℝ), (8803959659277/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328077659/2500000000 : ℝ)|^4135 ≤ (21568962290401/50000000000000 : ℝ)^3111
        have hw : |(1328077659/2500000000 : ℝ)|=(1328077659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-66715969/312500000 : ℝ)|^4135 ≤ (6421138551533/50000000000000 : ℝ)^3111
        have hw : |(-66715969/312500000 : ℝ)|=(66715969/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393811771/10000000000 : ℝ)|^4135 ≤ (8803959659277/20000000000000 : ℝ)^3111
        have hw : |(5393811771/10000000000 : ℝ)|=(5393811771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s9_4 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531231011/1000000000 : ℝ)*x 0 + (5393812617/10000000000 : ℝ)*x 1 + (-2134910571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531231011/1000000000 : ℝ)^4135 ≤ (8627583780713/20000000000000 : ℝ)^3111 := by
    have hnat : (531231011 : ℕ)^4135*20000000000000^3111 ≤ 8627583780713^3111*1000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531231011 1000000000 8627583780713 20000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393812617/10000000000 : ℝ)^4135 ≤ (44019807473331/100000000000000 : ℝ)^3111 := by
    have hnat : (5393812617 : ℕ)^4135*100000000000000^3111 ≤ 44019807473331^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393812617 10000000000 44019807473331 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2134910571/10000000000 : ℝ)^4135 ≤ (1605284201137/12500000000000 : ℝ)^3111 := by
    have hnat : (2134910571 : ℕ)^4135*12500000000000^3111 ≤ 1605284201137^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134910571 10000000000 1605284201137 12500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531231011/1000000000 : ℝ), (5393812617/10000000000 : ℝ), (-2134910571/10000000000 : ℝ)] ![(8627583780713/20000000000000 : ℝ), (44019807473331/100000000000000 : ℝ), (1605284201137/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531231011/1000000000 : ℝ)|^4135 ≤ (8627583780713/20000000000000 : ℝ)^3111
        have hw : |(531231011/1000000000 : ℝ)|=(531231011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393812617/10000000000 : ℝ)|^4135 ≤ (44019807473331/100000000000000 : ℝ)^3111
        have hw : |(5393812617/10000000000 : ℝ)|=(5393812617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2134910571/10000000000 : ℝ)|^4135 ≤ (1605284201137/12500000000000 : ℝ)^3111
        have hw : |(-2134910571/10000000000 : ℝ)|=(2134910571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_s9_5 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (437392323/1000000000 : ℝ)*x 0 + (4502281727/10000000000 : ℝ)*x 1 + (2124641629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437392323/1000000000 : ℝ)^4135 ≤ (33316720129741/100000000000000 : ℝ)^3111 := by
    have hnat : (437392323 : ℕ)^4135*100000000000000^3111 ≤ 33316720129741^3111*1000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437392323 1000000000 33316720129741 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502281727/10000000000 : ℝ)^4135 ≤ (86556251403/250000000000 : ℝ)^3111 := by
    have hnat : (4502281727 : ℕ)^4135*250000000000^3111 ≤ 86556251403^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502281727 10000000000 86556251403 250000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124641629/5000000000 : ℝ)^4135 ≤ (16030389650833/50000000000000 : ℝ)^3111 := by
    have hnat : (2124641629 : ℕ)^4135*50000000000000^3111 ≤ 16030389650833^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124641629 5000000000 16030389650833 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437392323/1000000000 : ℝ), (4502281727/10000000000 : ℝ), (2124641629/5000000000 : ℝ)] ![(33316720129741/100000000000000 : ℝ), (86556251403/250000000000 : ℝ), (16030389650833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437392323/1000000000 : ℝ)|^4135 ≤ (33316720129741/100000000000000 : ℝ)^3111
        have hw : |(437392323/1000000000 : ℝ)|=(437392323/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502281727/10000000000 : ℝ)|^4135 ≤ (86556251403/250000000000 : ℝ)^3111
        have hw : |(4502281727/10000000000 : ℝ)|=(4502281727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124641629/5000000000 : ℝ)|^4135 ≤ (16030389650833/50000000000000 : ℝ)^3111
        have hw : |(2124641629/5000000000 : ℝ)|=(2124641629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1077_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11267/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14009/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1401/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11267/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1401/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11267/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1401/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11267/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1401/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11267/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1401/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11267/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1401/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11267/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11267/100000 : ℝ) ^ (8269/2048 : ℝ) ≤ (742255451220681/5000000000000000000 : ℝ) := by
    have hpowers : (11267/100000 : ℝ)^8269 ≤ (742255451220681/5000000000000000000 : ℝ)^2048 := by
      have hnat : (11267 : ℕ)^8269*5000000000000000000^2048 ≤ 742255451220681^2048*100000^8269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11267 100000 742255451220681 5000000000000000000 8269 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11267/100000 : ℝ)) (X := (742255451220681/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1401/10000 : ℝ) ^ (8269/2048 : ℝ) ≤ (286253366258071/800000000000000000 : ℝ) := by
    have hpowers : (1401/10000 : ℝ)^8269 ≤ (286253366258071/800000000000000000 : ℝ)^2048 := by
      have hnat : (1401 : ℕ)^8269*800000000000000000^2048 ≤ 286253366258071^2048*10000^8269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1401 10000 286253366258071 800000000000000000 8269 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1401/10000 : ℝ)) (X := (286253366258071/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500742255451220681/2500000000000000000 : ℝ) ≤ (10000735261539947/10000000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (2500742255451220681/2500000000000000000 : ℝ)^2048 ≤ (10000735261539947/10000000000000000 : ℝ)^8269 := by
      have hnat : (2500742255451220681 : ℕ)^2048*10000000000000000^8269 ≤ 10000735261539947^8269*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500742255451220681 2500000000000000000 10000735261539947 10000000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000735261539947/10000000000000000 : ℝ)) (X := (2500742255451220681/2500000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010125355961334499/20000000000000000000 : ℝ) ≤ (10001253645004203/10000000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (20010125355961334499/20000000000000000000 : ℝ)^2048 ≤ (10001253645004203/10000000000000000 : ℝ)^8269 := by
      have hnat : (20010125355961334499 : ℕ)^2048*10000000000000000^8269 ≤ 10001253645004203^8269*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010125355961334499 20000000000000000000 10001253645004203 10000000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001253645004203/10000000000000000 : ℝ)) (X := (20010125355961334499/20000000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (400286253366258071/400000000000000000 : ℝ) ≤ (10001772028468459/10000000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (400286253366258071/400000000000000000 : ℝ)^2048 ≤ (10001772028468459/10000000000000000 : ℝ)^8269 := by
      have hnat : (400286253366258071 : ℕ)^2048*10000000000000000^8269 ≤ 10001772028468459^8269*400000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400286253366258071 400000000000000000 10001772028468459 10000000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001772028468459/10000000000000000 : ℝ)) (X := (400286253366258071/400000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(742255451220681/5000000000000000000 : ℝ) ≤ ((27420335569420529917/27430000000000000000 : ℝ)+2*(8099741629/4285937500000 : ℝ)*(11267/100000 : ℝ))^(8269/2048 : ℝ) := by
    rw [show (27420335569420529917/27430000000000000000 : ℝ)+2*(8099741629/4285937500000 : ℝ)*(11267/100000 : ℝ)=(10000735261539947/10000000000000000 : ℝ) by norm_num, show 1+2*(742255451220681/5000000000000000000 : ℝ)=(2500742255451220681/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(286253366258071/800000000000000000 : ℝ)+(742255451220681/5000000000000000000 : ℝ) ≤ ((27420335569420529917/27430000000000000000 : ℝ)+(8099741629/4285937500000 : ℝ)*((1401/10000 : ℝ)+(11267/100000 : ℝ)))^(8269/2048 : ℝ) := by
    rw [show (27420335569420529917/27430000000000000000 : ℝ)+(8099741629/4285937500000 : ℝ)*((1401/10000 : ℝ)+(11267/100000 : ℝ))=(10001253645004203/10000000000000000 : ℝ) by norm_num, show 1+(286253366258071/800000000000000000 : ℝ)+(742255451220681/5000000000000000000 : ℝ)=(20010125355961334499/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(286253366258071/800000000000000000 : ℝ) ≤ ((27420335569420529917/27430000000000000000 : ℝ)+2*(8099741629/4285937500000 : ℝ)*(1401/10000 : ℝ))^(8269/2048 : ℝ) := by
    rw [show (27420335569420529917/27430000000000000000 : ℝ)+2*(8099741629/4285937500000 : ℝ)*(1401/10000 : ℝ)=(10001772028468459/10000000000000000 : ℝ) by norm_num, show 1+2*(286253366258071/800000000000000000 : ℝ)=(400286253366258071/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27420335569420529917/27430000000000000000 : ℝ)*(X 1 0+X 2 0)+(8099741629/4285937500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (11267/100000 : ℝ)) (hi := (1401/10000 : ℝ)) (c := (27420335569420529917/27430000000000000000 : ℝ)) (alpha := (8099741629/4285937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27420335569420529917/27430000000000000000 : ℝ)*(X 0 1+X 2 1)+(8099741629/4285937500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (11267/100000 : ℝ)) (hi := (1401/10000 : ℝ)) (c := (27420335569420529917/27430000000000000000 : ℝ)) (alpha := (8099741629/4285937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27420335569420529917/27430000000000000000 : ℝ)*(X 0 2+X 1 2)+(8099741629/4285937500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (11267/100000 : ℝ)) (hi := (1401/10000 : ℝ)) (c := (27420335569420529917/27430000000000000000 : ℝ)) (alpha := (8099741629/4285937500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2672473333/5000000000 : ℝ)*X 2 0+(1316170057/2500000000 : ℝ)*X 2 1+(-452808537/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s9_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((4373913993/10000000000 : ℝ)*X 0 0+(4248644409/10000000000 : ℝ)*X 0 1+(4502917649/10000000000 : ℝ)*X 0 2+(4373913993/10000000000 : ℝ)*X 1 0+(4248644409/10000000000 : ℝ)*X 1 1+(4502917649/10000000000 : ℝ)*X 1 2+(4373913993/10000000000 : ℝ)*X 2 0+(4248644409/10000000000 : ℝ)*X 2 1+(4502917649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s9_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-87934707/400000000 : ℝ)*X 0 0+(5265004671/10000000000 : ℝ)*X 0 1+(1078762539/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s9_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1328077659/2500000000 : ℝ)*X 1 0+(-66715969/312500000 : ℝ)*X 1 1+(5393811771/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s9_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((531231011/1000000000 : ℝ)*X 2 0+(5393812617/10000000000 : ℝ)*X 2 1+(-2134910571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s9_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((437392323/1000000000 : ℝ)*X 0 0+(4502281727/10000000000 : ℝ)*X 0 1+(2124641629/5000000000 : ℝ)*X 0 2+(437392323/1000000000 : ℝ)*X 1 0+(4502281727/10000000000 : ℝ)*X 1 1+(2124641629/5000000000 : ℝ)*X 1 2+(437392323/1000000000 : ℝ)*X 2 0+(4502281727/10000000000 : ℝ)*X 2 1+(2124641629/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1350120630502440204687973773/274300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (334272309/100000000000000 : ℝ)*(base8) + (118168529/25000000000000 : ℝ)*(upper1) + (147676503/100000000000000 : ℝ)*(upper2) + (16093671/25000000000000 : ℝ)*(lower3) + (3668397/2500000000000 : ℝ)*(lower4) + (1171614427165477/20000000000000 : ℝ)*(major0) + (1171614427165477/20000000000000 : ℝ)*(major1) + (1171614427165477/20000000000000 : ℝ)*(major2) + (8728604701/25000000000000 : ℝ)*(sp0) + (5423050769/50000000000000 : ℝ)*(sp1) + (7763517210189293/100000000000000 : ℝ)*(sp2) + (3881758772230801/50000000000000 : ℝ)*(sp3) + (7763482630042799/100000000000000 : ℝ)*(sp4) + (3952615717023007/100000000000000 : ℝ)*(sp5) + (790525312624909/20000000000000 : ℝ)*(f.failure) + (3881758772230801/50000000000000 : ℝ)*(f.sum) + (736354141831/548600000000000000000000000 : ℝ)*base66 + (10021574183326875409/548600000000000000000000000000000 : ℝ)*base67 + (11579074890793475409/548600000000000000000000000000000 : ℝ)*base69 + (773387649398324591/548600000000000000000000000000000 : ℝ)*base72 + (8139445370933/2743000000000000000000000000 : ℝ)*base74 + (4563225611453275409/548600000000000000000000000000000 : ℝ)*base75 + (3928275374576475409/548600000000000000000000000000000 : ℝ)*base77 + (4015571796704324591/548600000000000000000000000000000 : ℝ)*base80 + (28660916171/548600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (9781357/2000000000000000000000 : ℝ)*base89 + (9781357/2000000000000000000000 : ℝ)*base91 + (9781357/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1077_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1077_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1077_box_0 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2069286831/10000000000 : ℝ)*x 0 + (1344304047/2500000000 : ℝ)*x 1 + (2688608059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2069286831/10000000000 : ℝ)^4135 ≤ (12320261315357/100000000000000 : ℝ)^3111 := by
    have hnat : (2069286831 : ℕ)^4135*100000000000000^3111 ≤ 12320261315357^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069286831 10000000000 12320261315357 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344304047/2500000000 : ℝ)^4135 ≤ (43839869714239/100000000000000 : ℝ)^3111 := by
    have hnat : (1344304047 : ℕ)^4135*100000000000000^3111 ≤ 43839869714239^3111*2500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344304047 2500000000 43839869714239 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688608059/5000000000 : ℝ)^4135 ≤ (43839868955687/100000000000000 : ℝ)^3111 := by
    have hnat : (2688608059 : ℕ)^4135*100000000000000^3111 ≤ 43839868955687^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688608059 5000000000 43839868955687 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2069286831/10000000000 : ℝ), (1344304047/2500000000 : ℝ), (2688608059/5000000000 : ℝ)] ![(12320261315357/100000000000000 : ℝ), (43839869714239/100000000000000 : ℝ), (43839868955687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2069286831/10000000000 : ℝ)|^4135 ≤ (12320261315357/100000000000000 : ℝ)^3111
        have hw : |(-2069286831/10000000000 : ℝ)|=(2069286831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344304047/2500000000 : ℝ)|^4135 ≤ (43839869714239/100000000000000 : ℝ)^3111
        have hw : |(1344304047/2500000000 : ℝ)|=(1344304047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688608059/5000000000 : ℝ)|^4135 ≤ (43839868955687/100000000000000 : ℝ)^3111
        have hw : |(2688608059/5000000000 : ℝ)|=(2688608059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_box_1 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647663051/5000000000 : ℝ)*x 0 + (-2180173983/10000000000 : ℝ)*x 1 + (672152019/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647663051/5000000000 : ℝ)^4135 ≤ (42954703188491/100000000000000 : ℝ)^3111 := by
    have hnat : (2647663051 : ℕ)^4135*100000000000000^3111 ≤ 42954703188491^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647663051 5000000000 42954703188491 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2180173983/10000000000 : ℝ)^4135 ≤ (6602713736203/50000000000000 : ℝ)^3111 := by
    have hnat : (2180173983 : ℕ)^4135*50000000000000^3111 ≤ 6602713736203^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180173983 10000000000 6602713736203 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672152019/1250000000 : ℝ)^4135 ≤ (21919934662063/50000000000000 : ℝ)^3111 := by
    have hnat : (672152019 : ℕ)^4135*50000000000000^3111 ≤ 21919934662063^3111*1250000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672152019 1250000000 21919934662063 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647663051/5000000000 : ℝ), (-2180173983/10000000000 : ℝ), (672152019/1250000000 : ℝ)] ![(42954703188491/100000000000000 : ℝ), (6602713736203/50000000000000 : ℝ), (21919934662063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647663051/5000000000 : ℝ)|^4135 ≤ (42954703188491/100000000000000 : ℝ)^3111
        have hw : |(2647663051/5000000000 : ℝ)|=(2647663051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2180173983/10000000000 : ℝ)|^4135 ≤ (6602713736203/50000000000000 : ℝ)^3111
        have hw : |(-2180173983/10000000000 : ℝ)|=(2180173983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672152019/1250000000 : ℝ)|^4135 ≤ (21919934662063/50000000000000 : ℝ)^3111
        have hw : |(672152019/1250000000 : ℝ)|=(672152019/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_box_2 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647662929/5000000000 : ℝ)*x 0 + (5377216153/10000000000 : ℝ)*x 1 + (-545043577/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647662929/5000000000 : ℝ)^4135 ≤ (21477350278859/50000000000000 : ℝ)^3111 := by
    have hnat : (2647662929 : ℕ)^4135*50000000000000^3111 ≤ 21477350278859^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647662929 5000000000 21477350278859 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377216153/10000000000 : ℝ)^4135 ≤ (43839869334963/100000000000000 : ℝ)^3111 := by
    have hnat : (5377216153 : ℕ)^4135*100000000000000^3111 ≤ 43839869334963^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377216153 10000000000 43839869334963 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545043577/2500000000 : ℝ)^4135 ≤ (6602715044451/50000000000000 : ℝ)^3111 := by
    have hnat : (545043577 : ℕ)^4135*50000000000000^3111 ≤ 6602715044451^3111*2500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545043577 2500000000 6602715044451 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647662929/5000000000 : ℝ), (5377216153/10000000000 : ℝ), (-545043577/2500000000 : ℝ)] ![(21477350278859/50000000000000 : ℝ), (43839869334963/100000000000000 : ℝ), (6602715044451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647662929/5000000000 : ℝ)|^4135 ≤ (21477350278859/50000000000000 : ℝ)^3111
        have hw : |(2647662929/5000000000 : ℝ)|=(2647662929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377216153/10000000000 : ℝ)|^4135 ≤ (43839869334963/100000000000000 : ℝ)^3111
        have hw : |(5377216153/10000000000 : ℝ)|=(5377216153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-545043577/2500000000 : ℝ)|^4135 ≤ (6602715044451/50000000000000 : ℝ)^3111
        have hw : |(-545043577/2500000000 : ℝ)|=(545043577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_box_3 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1120543287/2500000000 : ℝ)*x 0 + (4321938821/10000000000 : ℝ)*x 1 + (270121129/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1120543287/2500000000 : ℝ)^4135 ≤ (6883423655201/20000000000000 : ℝ)^3111 := by
    have hnat : (1120543287 : ℕ)^4135*20000000000000^3111 ≤ 6883423655201^3111*2500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120543287 2500000000 6883423655201 20000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4321938821/10000000000 : ℝ)^4135 ≤ (32791444675557/100000000000000 : ℝ)^3111 := by
    have hnat : (4321938821 : ℕ)^4135*100000000000000^3111 ≤ 32791444675557^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321938821 10000000000 32791444675557 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270121129/625000000 : ℝ)^4135 ≤ (32791437041537/100000000000000 : ℝ)^3111 := by
    have hnat : (270121129 : ℕ)^4135*100000000000000^3111 ≤ 32791437041537^3111*625000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270121129 625000000 32791437041537 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1120543287/2500000000 : ℝ), (4321938821/10000000000 : ℝ), (270121129/625000000 : ℝ)] ![(6883423655201/20000000000000 : ℝ), (32791444675557/100000000000000 : ℝ), (32791437041537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1120543287/2500000000 : ℝ)|^4135 ≤ (6883423655201/20000000000000 : ℝ)^3111
        have hw : |(1120543287/2500000000 : ℝ)|=(1120543287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4321938821/10000000000 : ℝ)|^4135 ≤ (32791444675557/100000000000000 : ℝ)^3111
        have hw : |(4321938821/10000000000 : ℝ)|=(4321938821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270121129/625000000 : ℝ)|^4135 ≤ (32791437041537/100000000000000 : ℝ)^3111
        have hw : |(270121129/625000000 : ℝ)|=(270121129/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_box_4 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-145552043/625000000 : ℝ)*x 0 + (2640126559/5000000000 : ℝ)*x 1 + (330015799/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (145552043/625000000 : ℝ)^4135 ≤ (14415474318909/100000000000000 : ℝ)^3111 := by
    have hnat : (145552043 : ℕ)^4135*100000000000000^3111 ≤ 14415474318909^3111*625000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145552043 625000000 14415474318909 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640126559/5000000000 : ℝ)^4135 ≤ (1337258269719/3125000000000 : ℝ)^3111 := by
    have hnat : (2640126559 : ℕ)^4135*3125000000000^3111 ≤ 1337258269719^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640126559 5000000000 1337258269719 3125000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (330015799/625000000 : ℝ)^4135 ≤ (8558452206649/20000000000000 : ℝ)^3111 := by
    have hnat : (330015799 : ℕ)^4135*20000000000000^3111 ≤ 8558452206649^3111*625000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330015799 625000000 8558452206649 20000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-145552043/625000000 : ℝ), (2640126559/5000000000 : ℝ), (330015799/625000000 : ℝ)] ![(14415474318909/100000000000000 : ℝ), (1337258269719/3125000000000 : ℝ), (8558452206649/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-145552043/625000000 : ℝ)|^4135 ≤ (14415474318909/100000000000000 : ℝ)^3111
        have hw : |(-145552043/625000000 : ℝ)|=(145552043/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640126559/5000000000 : ℝ)|^4135 ≤ (1337258269719/3125000000000 : ℝ)^3111
        have hw : |(2640126559/5000000000 : ℝ)|=(2640126559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(330015799/625000000 : ℝ)|^4135 ≤ (8558452206649/20000000000000 : ℝ)^3111
        have hw : |(330015799/625000000 : ℝ)|=(330015799/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_box_5 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268196587/500000000 : ℝ)*x 0 + (-44362341/200000000 : ℝ)*x 1 + (5280252551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268196587/500000000 : ℝ)^4135 ≤ (5461996493171/12500000000000 : ℝ)^3111 := by
    have hnat : (268196587 : ℕ)^4135*12500000000000^3111 ≤ 5461996493171^3111*500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268196587 500000000 5461996493171 12500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44362341/200000000 : ℝ)^4135 ≤ (13511769516147/100000000000000 : ℝ)^3111 := by
    have hnat : (44362341 : ℕ)^4135*100000000000000^3111 ≤ 13511769516147^3111*200000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44362341 200000000 13511769516147 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280252551/10000000000 : ℝ)^4135 ≤ (42792258523429/100000000000000 : ℝ)^3111 := by
    have hnat : (5280252551 : ℕ)^4135*100000000000000^3111 ≤ 42792258523429^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280252551 10000000000 42792258523429 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268196587/500000000 : ℝ), (-44362341/200000000 : ℝ), (5280252551/10000000000 : ℝ)] ![(5461996493171/12500000000000 : ℝ), (13511769516147/100000000000000 : ℝ), (42792258523429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268196587/500000000 : ℝ)|^4135 ≤ (5461996493171/12500000000000 : ℝ)^3111
        have hw : |(268196587/500000000 : ℝ)|=(268196587/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44362341/200000000 : ℝ)|^4135 ≤ (13511769516147/100000000000000 : ℝ)^3111
        have hw : |(-44362341/200000000 : ℝ)|=(44362341/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280252551/10000000000 : ℝ)|^4135 ≤ (42792258523429/100000000000000 : ℝ)^3111
        have hw : |(5280252551/10000000000 : ℝ)|=(5280252551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_box_6 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363931057/10000000000 : ℝ)*x 0 + (528025333/1000000000 : ℝ)*x 1 + (-1109058463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363931057/10000000000 : ℝ)^4135 ≤ (10923991137523/25000000000000 : ℝ)^3111 := by
    have hnat : (5363931057 : ℕ)^4135*25000000000000^3111 ≤ 10923991137523^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363931057 10000000000 10923991137523 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528025333/1000000000 : ℝ)^4135 ≤ (21396133457309/50000000000000 : ℝ)^3111 := by
    have hnat : (528025333 : ℕ)^4135*50000000000000^3111 ≤ 21396133457309^3111*1000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528025333 1000000000 21396133457309 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1109058463/5000000000 : ℝ)^4135 ≤ (13511768512167/100000000000000 : ℝ)^3111 := by
    have hnat : (1109058463 : ℕ)^4135*100000000000000^3111 ≤ 13511768512167^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109058463 5000000000 13511768512167 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363931057/10000000000 : ℝ), (528025333/1000000000 : ℝ), (-1109058463/5000000000 : ℝ)] ![(10923991137523/25000000000000 : ℝ), (21396133457309/50000000000000 : ℝ), (13511768512167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363931057/10000000000 : ℝ)|^4135 ≤ (10923991137523/25000000000000 : ℝ)^3111
        have hw : |(5363931057/10000000000 : ℝ)|=(5363931057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528025333/1000000000 : ℝ)|^4135 ≤ (21396133457309/50000000000000 : ℝ)^3111
        have hw : |(528025333/1000000000 : ℝ)|=(528025333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1109058463/5000000000 : ℝ)|^4135 ≤ (13511768512167/100000000000000 : ℝ)^3111
        have hw : |(-1109058463/5000000000 : ℝ)|=(1109058463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_box_7 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21326609/50000000 : ℝ)*x 0 + (4430342797/10000000000 : ℝ)*x 1 + (886068543/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21326609/50000000 : ℝ)^4135 ≤ (32221720876273/100000000000000 : ℝ)^3111 := by
    have hnat : (21326609 : ℕ)^4135*100000000000000^3111 ≤ 32221720876273^3111*50000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21326609 50000000 32221720876273 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4430342797/10000000000 : ℝ)^4135 ≤ (33889139973729/100000000000000 : ℝ)^3111 := by
    have hnat : (4430342797 : ℕ)^4135*100000000000000^3111 ≤ 33889139973729^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4430342797 10000000000 33889139973729 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (886068543/2000000000 : ℝ)^4135 ≤ (4236142392503/12500000000000 : ℝ)^3111 := by
    have hnat : (886068543 : ℕ)^4135*12500000000000^3111 ≤ 4236142392503^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886068543 2000000000 4236142392503 12500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21326609/50000000 : ℝ), (4430342797/10000000000 : ℝ), (886068543/2000000000 : ℝ)] ![(32221720876273/100000000000000 : ℝ), (33889139973729/100000000000000 : ℝ), (4236142392503/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21326609/50000000 : ℝ)|^4135 ≤ (32221720876273/100000000000000 : ℝ)^3111
        have hw : |(21326609/50000000 : ℝ)|=(21326609/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4430342797/10000000000 : ℝ)|^4135 ≤ (33889139973729/100000000000000 : ℝ)^3111
        have hw : |(4430342797/10000000000 : ℝ)|=(4430342797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(886068543/2000000000 : ℝ)|^4135 ≤ (4236142392503/12500000000000 : ℝ)^3111
        have hw : |(886068543/2000000000 : ℝ)|=(886068543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_box_8 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1137318061/5000000000 : ℝ)*x 0 + (5214435941/10000000000 : ℝ)*x 1 + (2693409099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1137318061/5000000000 : ℝ)^4135 ≤ (1746411331299/12500000000000 : ℝ)^3111 := by
    have hnat : (1137318061 : ℕ)^4135*12500000000000^3111 ≤ 1746411331299^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137318061 5000000000 1746411331299 12500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214435941/10000000000 : ℝ)^4135 ≤ (8416951459477/20000000000000 : ℝ)^3111 := by
    have hnat : (5214435941 : ℕ)^4135*20000000000000^3111 ≤ 8416951459477^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214435941 10000000000 8416951459477 20000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693409099/5000000000 : ℝ)^4135 ≤ (8788790407431/20000000000000 : ℝ)^3111 := by
    have hnat : (2693409099 : ℕ)^4135*20000000000000^3111 ≤ 8788790407431^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693409099 5000000000 8788790407431 20000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1137318061/5000000000 : ℝ), (5214435941/10000000000 : ℝ), (2693409099/5000000000 : ℝ)] ![(1746411331299/12500000000000 : ℝ), (8416951459477/20000000000000 : ℝ), (8788790407431/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1137318061/5000000000 : ℝ)|^4135 ≤ (1746411331299/12500000000000 : ℝ)^3111
        have hw : |(-1137318061/5000000000 : ℝ)|=(1137318061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214435941/10000000000 : ℝ)|^4135 ≤ (8416951459477/20000000000000 : ℝ)^3111
        have hw : |(5214435941/10000000000 : ℝ)|=(5214435941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693409099/5000000000 : ℝ)|^4135 ≤ (8788790407431/20000000000000 : ℝ)^3111
        have hw : |(2693409099/5000000000 : ℝ)|=(2693409099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_box_9 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288528383/10000000000 : ℝ)*x 0 + (-2176346607/10000000000 : ℝ)*x 1 + (5386818031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288528383/10000000000 : ℝ)^4135 ≤ (42881426652139/100000000000000 : ℝ)^3111 := by
    have hnat : (5288528383 : ℕ)^4135*100000000000000^3111 ≤ 42881426652139^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288528383 10000000000 42881426652139 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2176346607/10000000000 : ℝ)^4135 ≤ (2634924619517/20000000000000 : ℝ)^3111 := by
    have hnat : (2176346607 : ℕ)^4135*20000000000000^3111 ≤ 2634924619517^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176346607 10000000000 2634924619517 20000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386818031/10000000000 : ℝ)^4135 ≤ (10985987556601/25000000000000 : ℝ)^3111 := by
    have hnat : (5386818031 : ℕ)^4135*25000000000000^3111 ≤ 10985987556601^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386818031 10000000000 10985987556601 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288528383/10000000000 : ℝ), (-2176346607/10000000000 : ℝ), (5386818031/10000000000 : ℝ)] ![(42881426652139/100000000000000 : ℝ), (2634924619517/20000000000000 : ℝ), (10985987556601/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288528383/10000000000 : ℝ)|^4135 ≤ (42881426652139/100000000000000 : ℝ)^3111
        have hw : |(5288528383/10000000000 : ℝ)|=(5288528383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2176346607/10000000000 : ℝ)|^4135 ≤ (2634924619517/20000000000000 : ℝ)^3111
        have hw : |(-2176346607/10000000000 : ℝ)|=(2176346607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386818031/10000000000 : ℝ)|^4135 ≤ (10985987556601/25000000000000 : ℝ)^3111
        have hw : |(5386818031/10000000000 : ℝ)|=(5386818031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_box_10 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288528443/10000000000 : ℝ)*x 0 + (5386818169/10000000000 : ℝ)*x 1 + (-1088173171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288528443/10000000000 : ℝ)^4135 ≤ (42881427298777/100000000000000 : ℝ)^3111 := by
    have hnat : (5288528443 : ℕ)^4135*100000000000000^3111 ≤ 42881427298777^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288528443 10000000000 42881427298777 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386818169/10000000000 : ℝ)^4135 ≤ (43943951722713/100000000000000 : ℝ)^3111 := by
    have hnat : (5386818169 : ℕ)^4135*100000000000000^3111 ≤ 43943951722713^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386818169 10000000000 43943951722713 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088173171/5000000000 : ℝ)^4135 ≤ (13174620965367/100000000000000 : ℝ)^3111 := by
    have hnat : (1088173171 : ℕ)^4135*100000000000000^3111 ≤ 13174620965367^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088173171 5000000000 13174620965367 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288528443/10000000000 : ℝ), (5386818169/10000000000 : ℝ), (-1088173171/5000000000 : ℝ)] ![(42881427298777/100000000000000 : ℝ), (43943951722713/100000000000000 : ℝ), (13174620965367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288528443/10000000000 : ℝ)|^4135 ≤ (42881427298777/100000000000000 : ℝ)^3111
        have hw : |(5288528443/10000000000 : ℝ)|=(5288528443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386818169/10000000000 : ℝ)|^4135 ≤ (43943951722713/100000000000000 : ℝ)^3111
        have hw : |(5386818169/10000000000 : ℝ)|=(5386818169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1088173171/5000000000 : ℝ)|^4135 ≤ (13174620965367/100000000000000 : ℝ)^3111
        have hw : |(-1088173171/5000000000 : ℝ)|=(1088173171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_box_11 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2251686761/5000000000 : ℝ)*x 0 + (862239513/2000000000 : ℝ)*x 1 + (4311197907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2251686761/5000000000 : ℝ)^4135 ≤ (8658415111419/25000000000000 : ℝ)^3111 := by
    have hnat : (2251686761 : ℕ)^4135*25000000000000^3111 ≤ 8658415111419^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251686761 5000000000 8658415111419 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (862239513/2000000000 : ℝ)^4135 ≤ (8170792011117/25000000000000 : ℝ)^3111 := by
    have hnat : (862239513 : ℕ)^4135*25000000000000^3111 ≤ 8170792011117^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862239513 2000000000 8170792011117 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4311197907/10000000000 : ℝ)^4135 ≤ (4085396436321/12500000000000 : ℝ)^3111 := by
    have hnat : (4311197907 : ℕ)^4135*12500000000000^3111 ≤ 4085396436321^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311197907 10000000000 4085396436321 12500000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2251686761/5000000000 : ℝ), (862239513/2000000000 : ℝ), (4311197907/10000000000 : ℝ)] ![(8658415111419/25000000000000 : ℝ), (8170792011117/25000000000000 : ℝ), (4085396436321/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2251686761/5000000000 : ℝ)|^4135 ≤ (8658415111419/25000000000000 : ℝ)^3111
        have hw : |(2251686761/5000000000 : ℝ)|=(2251686761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(862239513/2000000000 : ℝ)|^4135 ≤ (8170792011117/25000000000000 : ℝ)^3111
        have hw : |(862239513/2000000000 : ℝ)|=(862239513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4311197907/10000000000 : ℝ)|^4135 ≤ (4085396436321/12500000000000 : ℝ)^3111
        have hw : |(4311197907/10000000000 : ℝ)|=(4311197907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_box_12 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2123844139/10000000000 : ℝ)*x 0 + (1088341297/2000000000 : ℝ)*x 1 + (5272246339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123844139/10000000000 : ℝ)^4135 ≤ (510154765199/4000000000000 : ℝ)^3111 := by
    have hnat : (2123844139 : ℕ)^4135*4000000000000^3111 ≤ 510154765199^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123844139 10000000000 510154765199 4000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088341297/2000000000 : ℝ)^4135 ≤ (8908018334941/20000000000000 : ℝ)^3111 := by
    have hnat : (1088341297 : ℕ)^4135*20000000000000^3111 ≤ 8908018334941^3111*2000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088341297 2000000000 8908018334941 20000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272246339/10000000000 : ℝ)^4135 ≤ (42706039186723/100000000000000 : ℝ)^3111 := by
    have hnat : (5272246339 : ℕ)^4135*100000000000000^3111 ≤ 42706039186723^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272246339 10000000000 42706039186723 100000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2123844139/10000000000 : ℝ), (1088341297/2000000000 : ℝ), (5272246339/10000000000 : ℝ)] ![(510154765199/4000000000000 : ℝ), (8908018334941/20000000000000 : ℝ), (42706039186723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2123844139/10000000000 : ℝ)|^4135 ≤ (510154765199/4000000000000 : ℝ)^3111
        have hw : |(-2123844139/10000000000 : ℝ)|=(2123844139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088341297/2000000000 : ℝ)|^4135 ≤ (8908018334941/20000000000000 : ℝ)^3111
        have hw : |(1088341297/2000000000 : ℝ)|=(1088341297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272246339/10000000000 : ℝ)|^4135 ≤ (42706039186723/100000000000000 : ℝ)^3111
        have hw : |(5272246339/10000000000 : ℝ)|=(5272246339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_box_13 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369593953/10000000000 : ℝ)*x 0 + (-2221191773/10000000000 : ℝ)*x 1 + (5272246319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369593953/10000000000 : ℝ)^4135 ≤ (21878645488807/50000000000000 : ℝ)^3111 := by
    have hnat : (5369593953 : ℕ)^4135*50000000000000^3111 ≤ 21878645488807^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369593953 10000000000 21878645488807 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2221191773/10000000000 : ℝ)^4135 ≤ (270733400593/2000000000000 : ℝ)^3111 := by
    have hnat : (2221191773 : ℕ)^4135*2000000000000^3111 ≤ 270733400593^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221191773 10000000000 270733400593 2000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272246319/10000000000 : ℝ)^4135 ≤ (8541207794279/20000000000000 : ℝ)^3111 := by
    have hnat : (5272246319 : ℕ)^4135*20000000000000^3111 ≤ 8541207794279^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272246319 10000000000 8541207794279 20000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369593953/10000000000 : ℝ), (-2221191773/10000000000 : ℝ), (5272246319/10000000000 : ℝ)] ![(21878645488807/50000000000000 : ℝ), (270733400593/2000000000000 : ℝ), (8541207794279/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369593953/10000000000 : ℝ)|^4135 ≤ (21878645488807/50000000000000 : ℝ)^3111
        have hw : |(5369593953/10000000000 : ℝ)|=(5369593953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2221191773/10000000000 : ℝ)|^4135 ≤ (270733400593/2000000000000 : ℝ)^3111
        have hw : |(-2221191773/10000000000 : ℝ)|=(2221191773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272246319/10000000000 : ℝ)|^4135 ≤ (8541207794279/20000000000000 : ℝ)^3111
        have hw : |(5272246319/10000000000 : ℝ)|=(5272246319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_box_14 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684796959/5000000000 : ℝ)*x 0 + (5272246459/10000000000 : ℝ)*x 1 + (-1110595817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684796959/5000000000 : ℝ)^4135 ≤ (8751458119703/20000000000000 : ℝ)^3111 := by
    have hnat : (2684796959 : ℕ)^4135*20000000000000^3111 ≤ 8751458119703^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684796959 5000000000 8751458119703 20000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5272246459/10000000000 : ℝ)^4135 ≤ (21353020239343/50000000000000 : ℝ)^3111 := by
    have hnat : (5272246459 : ℕ)^4135*50000000000000^3111 ≤ 21353020239343^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272246459 10000000000 21353020239343 50000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1110595817/5000000000 : ℝ)^4135 ≤ (3384167225927/25000000000000 : ℝ)^3111 := by
    have hnat : (1110595817 : ℕ)^4135*25000000000000^3111 ≤ 3384167225927^3111*5000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110595817 5000000000 3384167225927 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684796959/5000000000 : ℝ), (5272246459/10000000000 : ℝ), (-1110595817/5000000000 : ℝ)] ![(8751458119703/20000000000000 : ℝ), (21353020239343/50000000000000 : ℝ), (3384167225927/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684796959/5000000000 : ℝ)|^4135 ≤ (8751458119703/20000000000000 : ℝ)^3111
        have hw : |(2684796959/5000000000 : ℝ)|=(2684796959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5272246459/10000000000 : ℝ)|^4135 ≤ (21353020239343/50000000000000 : ℝ)^3111
        have hw : |(5272246459/10000000000 : ℝ)|=(5272246459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1110595817/5000000000 : ℝ)|^4135 ≤ (3384167225927/25000000000000 : ℝ)^3111
        have hw : |(-1110595817/5000000000 : ℝ)|=(1110595817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1077_box_15 (p : ℝ) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061796189/2500000000 : ℝ)*x 0 + (4439289611/10000000000 : ℝ)*x 1 + (17757157/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061796189/2500000000 : ℝ)^4135 ≤ (8009934071489/25000000000000 : ℝ)^3111 := by
    have hnat : (1061796189 : ℕ)^4135*25000000000000^3111 ≤ 8009934071489^3111*2500000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061796189 2500000000 8009934071489 25000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4439289611/10000000000 : ℝ)^4135 ≤ (6796026737/20000000000 : ℝ)^3111 := by
    have hnat : (4439289611 : ℕ)^4135*20000000000^3111 ≤ 6796026737^3111*10000000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4439289611 10000000000 6796026737 20000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17757157/40000000 : ℝ)^4135 ≤ (1359205200489/4000000000000 : ℝ)^3111 := by
    have hnat : (17757157 : ℕ)^4135*4000000000000^3111 ≤ 1359205200489^3111*40000000^4135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17757157 40000000 1359205200489 4000000000000 4135 3111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4135/1024 : ℝ)) 4135 3111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061796189/2500000000 : ℝ), (4439289611/10000000000 : ℝ), (17757157/40000000 : ℝ)] ![(8009934071489/25000000000000 : ℝ), (6796026737/20000000000 : ℝ), (1359205200489/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061796189/2500000000 : ℝ)|^4135 ≤ (8009934071489/25000000000000 : ℝ)^3111
        have hw : |(1061796189/2500000000 : ℝ)|=(1061796189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4439289611/10000000000 : ℝ)|^4135 ≤ (6796026737/20000000000 : ℝ)^3111
        have hw : |(4439289611/10000000000 : ℝ)|=(4439289611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17757157/40000000 : ℝ)|^4135 ≤ (1359205200489/4000000000000 : ℝ)^3111
        have hw : |(17757157/40000000 : ℝ)|=(17757157/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1077_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2489/4000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59249/100000 : ℝ) ∧ (79607/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41489/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14009/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11267/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14009/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11267/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14009/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11267/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14009/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11267/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14009/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11267/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14009/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11267/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11267/100000 : ℝ) ^ (8269/2048 : ℝ) ≤ (742255451220681/5000000000000000000 : ℝ) := by
    have hpowers : (11267/100000 : ℝ)^8269 ≤ (742255451220681/5000000000000000000 : ℝ)^2048 := by
      have hnat : (11267 : ℕ)^8269*5000000000000000000^2048 ≤ 742255451220681^2048*100000^8269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11267 100000 742255451220681 5000000000000000000 8269 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11267/100000 : ℝ)) (X := (742255451220681/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14009/100000 : ℝ) ^ (8269/2048 : ℝ) ≤ (35771359838012009/100000000000000000000 : ℝ) := by
    have hpowers : (14009/100000 : ℝ)^8269 ≤ (35771359838012009/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14009 : ℕ)^8269*100000000000000000000^2048 ≤ 35771359838012009^2048*100000^8269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14009 100000 35771359838012009 100000000000000000000 8269 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14009/100000 : ℝ)) (X := (35771359838012009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500742255451220681/2500000000000000000 : ℝ) ≤ (10000735261539947/10000000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (2500742255451220681/2500000000000000000 : ℝ)^2048 ≤ (10000735261539947/10000000000000000 : ℝ)^8269 := by
      have hnat : (2500742255451220681 : ℕ)^2048*10000000000000000^8269 ≤ 10000735261539947^8269*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500742255451220681 2500000000000000000 10000735261539947 10000000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000735261539947/10000000000000000 : ℝ)) (X := (2500742255451220681/2500000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050616468862425629/100000000000000000000 : ℝ) ≤ (10001253389728169/10000000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (100050616468862425629/100000000000000000000 : ℝ)^2048 ≤ (10001253389728169/10000000000000000 : ℝ)^8269 := by
      have hnat : (100050616468862425629 : ℕ)^2048*10000000000000000^8269 ≤ 10001253389728169^8269*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050616468862425629 100000000000000000000 10001253389728169 10000000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001253389728169/10000000000000000 : ℝ)) (X := (100050616468862425629/100000000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035771359838012009/50000000000000000000 : ℝ) ≤ (10001771517916391/10000000000000000 : ℝ) ^ (8269/2048 : ℝ) := by
    have hpowers : (50035771359838012009/50000000000000000000 : ℝ)^2048 ≤ (10001771517916391/10000000000000000 : ℝ)^8269 := by
      have hnat : (50035771359838012009 : ℕ)^2048*10000000000000000^8269 ≤ 10001771517916391^8269*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035771359838012009 50000000000000000000 10001771517916391 10000000000000000 2048 8269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001771517916391/10000000000000000 : ℝ)) (X := (50035771359838012009/50000000000000000000 : ℝ)) (by norm_num) 8269 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(742255451220681/5000000000000000000 : ℝ) ≤ ((4568390097758190021/4570000000000000000 : ℝ)+2*(86354698037/45700000000000 : ℝ)*(11267/100000 : ℝ))^(8269/2048 : ℝ) := by
    rw [show (4568390097758190021/4570000000000000000 : ℝ)+2*(86354698037/45700000000000 : ℝ)*(11267/100000 : ℝ)=(10000735261539947/10000000000000000 : ℝ) by norm_num, show 1+2*(742255451220681/5000000000000000000 : ℝ)=(2500742255451220681/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35771359838012009/100000000000000000000 : ℝ)+(742255451220681/5000000000000000000 : ℝ) ≤ ((4568390097758190021/4570000000000000000 : ℝ)+(86354698037/45700000000000 : ℝ)*((14009/100000 : ℝ)+(11267/100000 : ℝ)))^(8269/2048 : ℝ) := by
    rw [show (4568390097758190021/4570000000000000000 : ℝ)+(86354698037/45700000000000 : ℝ)*((14009/100000 : ℝ)+(11267/100000 : ℝ))=(10001253389728169/10000000000000000 : ℝ) by norm_num, show 1+(35771359838012009/100000000000000000000 : ℝ)+(742255451220681/5000000000000000000 : ℝ)=(100050616468862425629/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35771359838012009/100000000000000000000 : ℝ) ≤ ((4568390097758190021/4570000000000000000 : ℝ)+2*(86354698037/45700000000000 : ℝ)*(14009/100000 : ℝ))^(8269/2048 : ℝ) := by
    rw [show (4568390097758190021/4570000000000000000 : ℝ)+2*(86354698037/45700000000000 : ℝ)*(14009/100000 : ℝ)=(10001771517916391/10000000000000000 : ℝ) by norm_num, show 1+2*(35771359838012009/100000000000000000000 : ℝ)=(50035771359838012009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4568390097758190021/4570000000000000000 : ℝ)*(X 1 0+X 2 0)+(86354698037/45700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (11267/100000 : ℝ)) (hi := (14009/100000 : ℝ)) (c := (4568390097758190021/4570000000000000000 : ℝ)) (alpha := (86354698037/45700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4568390097758190021/4570000000000000000 : ℝ)*(X 0 1+X 2 1)+(86354698037/45700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (11267/100000 : ℝ)) (hi := (14009/100000 : ℝ)) (c := (4568390097758190021/4570000000000000000 : ℝ)) (alpha := (86354698037/45700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4568390097758190021/4570000000000000000 : ℝ)*(X 0 2+X 1 2)+(86354698037/45700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8269/2048 : ℝ)) (lo := (11267/100000 : ℝ)) (hi := (14009/100000 : ℝ)) (c := (4568390097758190021/4570000000000000000 : ℝ)) (alpha := (86354698037/45700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2069286831/10000000000 : ℝ)*X 0 0+(1344304047/2500000000 : ℝ)*X 0 1+(2688608059/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647663051/5000000000 : ℝ)*X 1 0+(-2180173983/10000000000 : ℝ)*X 1 1+(672152019/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647662929/5000000000 : ℝ)*X 2 0+(5377216153/10000000000 : ℝ)*X 2 1+(-545043577/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1120543287/2500000000 : ℝ)*X 0 0+(4321938821/10000000000 : ℝ)*X 0 1+(270121129/625000000 : ℝ)*X 0 2+(1120543287/2500000000 : ℝ)*X 1 0+(4321938821/10000000000 : ℝ)*X 1 1+(270121129/625000000 : ℝ)*X 1 2+(1120543287/2500000000 : ℝ)*X 2 0+(4321938821/10000000000 : ℝ)*X 2 1+(270121129/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-145552043/625000000 : ℝ)*X 0 0+(2640126559/5000000000 : ℝ)*X 0 1+(330015799/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((268196587/500000000 : ℝ)*X 1 0+(-44362341/200000000 : ℝ)*X 1 1+(5280252551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363931057/10000000000 : ℝ)*X 2 0+(528025333/1000000000 : ℝ)*X 2 1+(-1109058463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((21326609/50000000 : ℝ)*X 0 0+(4430342797/10000000000 : ℝ)*X 0 1+(886068543/2000000000 : ℝ)*X 0 2+(21326609/50000000 : ℝ)*X 1 0+(4430342797/10000000000 : ℝ)*X 1 1+(886068543/2000000000 : ℝ)*X 1 2+(21326609/50000000 : ℝ)*X 2 0+(4430342797/10000000000 : ℝ)*X 2 1+(886068543/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1137318061/5000000000 : ℝ)*X 0 0+(5214435941/10000000000 : ℝ)*X 0 1+(2693409099/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288528383/10000000000 : ℝ)*X 1 0+(-2176346607/10000000000 : ℝ)*X 1 1+(5386818031/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288528443/10000000000 : ℝ)*X 2 0+(5386818169/10000000000 : ℝ)*X 2 1+(-1088173171/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2251686761/5000000000 : ℝ)*X 0 0+(862239513/2000000000 : ℝ)*X 0 1+(4311197907/10000000000 : ℝ)*X 0 2+(2251686761/5000000000 : ℝ)*X 1 0+(862239513/2000000000 : ℝ)*X 1 1+(4311197907/10000000000 : ℝ)*X 1 2+(2251686761/5000000000 : ℝ)*X 2 0+(862239513/2000000000 : ℝ)*X 2 1+(4311197907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2123844139/10000000000 : ℝ)*X 0 0+(1088341297/2000000000 : ℝ)*X 0 1+(5272246339/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369593953/10000000000 : ℝ)*X 1 0+(-2221191773/10000000000 : ℝ)*X 1 1+(5272246319/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684796959/5000000000 : ℝ)*X 2 0+(5272246459/10000000000 : ℝ)*X 2 1+(-1110595817/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1061796189/2500000000 : ℝ)*X 0 0+(4439289611/10000000000 : ℝ)*X 0 1+(17757157/40000000 : ℝ)*X 0 2+(1061796189/2500000000 : ℝ)*X 1 0+(4439289611/10000000000 : ℝ)*X 1 1+(17757157/40000000 : ℝ)*X 1 2+(1061796189/2500000000 : ℝ)*X 2 0+(4439289611/10000000000 : ℝ)*X 2 1+(17757157/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1077_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2489/4000 : ℝ) ≤ (-17772350225899155273963320912949/28562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34309521/50000000000000 : ℝ)*(lower0) + (10253583/50000000000000 : ℝ)*(upper3) + (56119803/50000000000000 : ℝ)*(lower4) + (966492965421977/25000000000000 : ℝ)*(major0) + (966492965421977/25000000000000 : ℝ)*(major1) + (966492965421977/25000000000000 : ℝ)*(major2) + (48994509/200000000000 : ℝ)*(sp1) + (1286045499535293/25000000000000 : ℝ)*(sp4) + (5144166618983969/100000000000000 : ℝ)*(sp5) + (2572032830401041/50000000000000 : ℝ)*(sp6) + (130423697438909/5000000000000 : ℝ)*(sp7) + (9118097297/100000000000000 : ℝ)*(sp8) + (125455436387/100000000000000 : ℝ)*(sp14) + (97742421/500000000000 : ℝ)*(sp15) + (130424674863119/5000000000000 : ℝ)*(f.failure) + (1286047779059617/25000000000000 : ℝ)*(f.sum) + (1059331106477/1142500000000000000000000000 : ℝ)*base66 + (314341792789858483/114250000000000000000000000000000 : ℝ)*base68 + (102636326985891517/114250000000000000000000000000000 : ℝ)*base69 + (880207513274608483/114250000000000000000000000000000 : ℝ)*base72 + (60612837082123/1142500000000000000000000000 : ℝ)*base73 + (754559174540358483/114250000000000000000000000000000 : ℝ)*base76 + (855520359564608483/114250000000000000000000000000000 : ℝ)*base78 + (3164080790399858483/114250000000000000000000000000000 : ℝ)*base80 + (2109055285127/1142500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2640687/500000000000000000000 : ℝ)*base89 + (2640687/500000000000000000000 : ℝ)*base91 + (2640687/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59249/100000 : ℝ) ≤ (13538971484269256727360595284231/22850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (170211817/100000000000000 : ℝ)*(lower0) + (16843179/12500000000000 : ℝ)*(upper2) + (64072827/100000000000000 : ℝ)*(upper3) + (130381029/100000000000000 : ℝ)*(lower5) + (785813788271337/20000000000000 : ℝ)*(major0) + (785813788271337/20000000000000 : ℝ)*(major1) + (785813788271337/20000000000000 : ℝ)*(major2) + (5187320284565973/100000000000000 : ℝ)*(sp0) + (2593635961630811/50000000000000 : ℝ)*(sp1) + (5187259894737243/100000000000000 : ℝ)*(sp2) + (20711382575199/781250000000 : ℝ)*(sp3) + (5061537203/50000000000000 : ℝ)*(sp7) + (48361304351/100000000000000 : ℝ)*(sp9) + (6038982873/10000000000000 : ℝ)*(sp10) + (1325533546349939/50000000000000 : ℝ)*(f.failure) + (5187320284565973/100000000000000 : ℝ)*(f.sum) + (37860825813/7140625000000000000000000 : ℝ)*base66 + (665900843744571923/91400000000000000000000000000000 : ℝ)*base68 + (395326432183828077/91400000000000000000000000000000 : ℝ)*base69 + (625543677815571923/91400000000000000000000000000000 : ℝ)*base72 + (1105284675879/228500000000000000000000000 : ℝ)*base74 + (732158248861571923/91400000000000000000000000000000 : ℝ)*base76 + (658515771455371923/91400000000000000000000000000000 : ℝ)*base78 + (1739202874869571923/91400000000000000000000000000000 : ℝ)*base80 + (812160951789/457000000000000000000000000 : ℝ)*base82 + (42918547/5000000000000000000000 : ℝ)*base89 + (42918547/5000000000000000000000 : ℝ)*base91 + (42918547/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79607/100000 : ℝ) ≤ (181907320495933068845705947728447/228500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1274171/1250000000000 : ℝ)*(upper0) + (109980347/100000000000000 : ℝ)*(lower3) + (27913221/25000000000000 : ℝ)*(upper4) + (4397300025049231/100000000000000 : ℝ)*(major0) + (4397300025049231/100000000000000 : ℝ)*(major1) + (4397300025049231/100000000000000 : ℝ)*(major2) + (46969736079/100000000000000 : ℝ)*(sp1) + (40006088169/25000000000000 : ℝ)*(sp2) + (26602954293/50000000000000 : ℝ)*(sp3) + (3002590547/100000000000000 : ℝ)*(sp4) + (5801063188766577/100000000000000 : ℝ)*(sp8) + (1160203844324209/20000000000000 : ℝ)*(sp9) + (181278317718889/3125000000000 : ℝ)*(sp10) + (1483472104644241/50000000000000 : ℝ)*(sp11) + (741749353799267/25000000000000 : ℝ)*(f.failure) + (1450266547839281/25000000000000 : ℝ)*(f.sum) + (1707605488977/2285000000000000000000000000 : ℝ)*base65 + (4663982313190376149/457000000000000000000000000000000 : ℝ)*base68 + (1154750612128623851/457000000000000000000000000000000 : ℝ)*base69 + (199912027692376149/457000000000000000000000000000000 : ℝ)*base72 + (62380838010693/2285000000000000000000000000 : ℝ)*base74 + (1947915557915623851/457000000000000000000000000000000 : ℝ)*base75 + (93776198504623851/457000000000000000000000000000000 : ℝ)*base77 + (1229594048700623851/457000000000000000000000000000000 : ℝ)*base79 + (212524915843/2285000000000000000000000000 : ℝ)*base82 + (16615491/2500000000000000000000 : ℝ)*base89 + (16615491/2500000000000000000000 : ℝ)*base91 + (16615491/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-41489/50000 : ℝ) ≤ (-47399496687420561134187283203879/57125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (95054077/100000000000000 : ℝ)*(lower0) + (27015377/50000000000000 : ℝ)*(lower2) + (2357773/5000000000000 : ℝ)*(upper3) + (1893213/2500000000000 : ℝ)*(upper5) + (1107969920813789/25000000000000 : ℝ)*(major0) + (1107969920813789/25000000000000 : ℝ)*(major1) + (1107969920813789/25000000000000 : ℝ)*(major2) + (555451853/12500000000000 : ℝ)*(sp0) + (65949976881/50000000000000 : ℝ)*(sp5) + (5937569647/50000000000000 : ℝ)*(sp7) + (2950541934087099/50000000000000 : ℝ)*(sp12) + (295047820591763/5000000000000 : ℝ)*(sp13) + (2950544155894511/50000000000000 : ℝ)*(sp14) + (1495158764608621/50000000000000 : ℝ)*(sp15) + (373791175544567/12500000000000 : ℝ)*(f.failure) + (2950544155894511/50000000000000 : ℝ)*(f.sum) + (1398536825369/1142500000000000000000000000 : ℝ)*base66 + (1763321605450200431/114250000000000000000000000000000 : ℝ)*base68 + (907109591573700431/114250000000000000000000000000000 : ℝ)*base70 + (1149453806532700431/114250000000000000000000000000000 : ℝ)*base72 + (3296466893767/142812500000000000000000000 : ℝ)*base73 + (716958797757700431/114250000000000000000000000000000 : ℝ)*base76 + (1375437968520700431/114250000000000000000000000000000 : ℝ)*base78 + (2446391297273200431/114250000000000000000000000000000 : ℝ)*base80 + (1238026561301/1142500000000000000000000000 : ℝ)*base81 + (6122391/1250000000000000000000 : ℝ)*base89 + (6122391/1250000000000000000000 : ℝ)*base91 + (6122391/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1077_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59249/100000 : ℝ) else (79607/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41489/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1077_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1077_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59249/100000 : ℝ) else (79607/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41489/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1077_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1077_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8269/2048 : ℝ) ≤ p) (hpb : p ≤ (4135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148207073/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59249/100000 : ℝ) else (79607/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41489/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1077_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
