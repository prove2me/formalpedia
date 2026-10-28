-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1240_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:18:43.392218+00:00
-- url     : https://prove2.me/submissions/d95f1ecd-bf54-4529-9dbb-b45b99a2998d

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
theorem support_rectangle_w1240_s0_0 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1861177371/10000000000 : ℝ)*x 0 + (3015978067/5000000000 : ℝ)*x 1 + (4792740111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1861177371/10000000000 : ℝ)^8433 ≤ (1356690909833/12500000000000 : ℝ)^6385 := by
    have hnat : (1861177371 : ℕ)^8433*12500000000000^6385 ≤ 1356690909833^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1861177371 10000000000 1356690909833 12500000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3015978067/5000000000 : ℝ)^8433 ≤ (25645416196619/50000000000000 : ℝ)^6385 := by
    have hnat : (3015978067 : ℕ)^8433*50000000000000^6385 ≤ 25645416196619^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3015978067 5000000000 25645416196619 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4792740111/10000000000 : ℝ)^8433 ≤ (37855640305523/100000000000000 : ℝ)^6385 := by
    have hnat : (4792740111 : ℕ)^8433*100000000000000^6385 ≤ 37855640305523^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4792740111 10000000000 37855640305523 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1861177371/10000000000 : ℝ), (3015978067/5000000000 : ℝ), (4792740111/10000000000 : ℝ)] ![(1356690909833/12500000000000 : ℝ), (25645416196619/50000000000000 : ℝ), (37855640305523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1861177371/10000000000 : ℝ)|^8433 ≤ (1356690909833/12500000000000 : ℝ)^6385
        have hw : |(-1861177371/10000000000 : ℝ)|=(1861177371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3015978067/5000000000 : ℝ)|^8433 ≤ (25645416196619/50000000000000 : ℝ)^6385
        have hw : |(3015978067/5000000000 : ℝ)|=(3015978067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4792740111/10000000000 : ℝ)|^8433 ≤ (37855640305523/100000000000000 : ℝ)^6385
        have hw : |(4792740111/10000000000 : ℝ)|=(4792740111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s0_1 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1377818041/2500000000 : ℝ)*x 0 + (-40150951/156250000 : ℝ)*x 1 + (239637003/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1377818041/2500000000 : ℝ)^8433 ≤ (22762918340059/50000000000000 : ℝ)^6385 := by
    have hnat : (1377818041 : ℕ)^8433*50000000000000^6385 ≤ 22762918340059^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377818041 2500000000 22762918340059 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40150951/156250000 : ℝ)^8433 ≤ (16618523540969/100000000000000 : ℝ)^6385 := by
    have hnat : (40150951 : ℕ)^8433*100000000000000^6385 ≤ 16618523540969^6385*156250000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40150951 156250000 16618523540969 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (239637003/500000000 : ℝ)^8433 ≤ (3785563977349/10000000000000 : ℝ)^6385 := by
    have hnat : (239637003 : ℕ)^8433*10000000000000^6385 ≤ 3785563977349^6385*500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239637003 500000000 3785563977349 10000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1377818041/2500000000 : ℝ), (-40150951/156250000 : ℝ), (239637003/500000000 : ℝ)] ![(22762918340059/50000000000000 : ℝ), (16618523540969/100000000000000 : ℝ), (3785563977349/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1377818041/2500000000 : ℝ)|^8433 ≤ (22762918340059/50000000000000 : ℝ)^6385
        have hw : |(1377818041/2500000000 : ℝ)|=(1377818041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40150951/156250000 : ℝ)|^8433 ≤ (16618523540969/100000000000000 : ℝ)^6385
        have hw : |(-40150951/156250000 : ℝ)|=(40150951/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(239637003/500000000 : ℝ)|^8433 ≤ (3785563977349/10000000000000 : ℝ)^6385
        have hw : |(239637003/500000000 : ℝ)|=(239637003/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s0_2 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (551127209/1000000000 : ℝ)*x 0 + (2396370067/5000000000 : ℝ)*x 1 + (-1284830433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551127209/1000000000 : ℝ)^8433 ≤ (45525835872773/100000000000000 : ℝ)^6385 := by
    have hnat : (551127209 : ℕ)^8433*100000000000000^6385 ≤ 45525835872773^6385*1000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551127209 1000000000 45525835872773 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2396370067/5000000000 : ℝ)^8433 ≤ (37855640545459/100000000000000 : ℝ)^6385 := by
    have hnat : (2396370067 : ℕ)^8433*100000000000000^6385 ≤ 37855640545459^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2396370067 5000000000 37855640545459 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1284830433/5000000000 : ℝ)^8433 ≤ (4154630889513/25000000000000 : ℝ)^6385 := by
    have hnat : (1284830433 : ℕ)^8433*25000000000000^6385 ≤ 4154630889513^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284830433 5000000000 4154630889513 25000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(551127209/1000000000 : ℝ), (2396370067/5000000000 : ℝ), (-1284830433/5000000000 : ℝ)] ![(45525835872773/100000000000000 : ℝ), (37855640545459/100000000000000 : ℝ), (4154630889513/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(551127209/1000000000 : ℝ)|^8433 ≤ (45525835872773/100000000000000 : ℝ)^6385
        have hw : |(551127209/1000000000 : ℝ)|=(551127209/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2396370067/5000000000 : ℝ)|^8433 ≤ (37855640545459/100000000000000 : ℝ)^6385
        have hw : |(2396370067/5000000000 : ℝ)|=(2396370067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1284830433/5000000000 : ℝ)|^8433 ≤ (4154630889513/25000000000000 : ℝ)^6385
        have hw : |(-1284830433/5000000000 : ℝ)|=(1284830433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s0_3 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4193178673/10000000000 : ℝ)*x 0 + (3116966137/10000000000 : ℝ)*x 1 + (703729047/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4193178673/10000000000 : ℝ)^8433 ≤ (3966281201461/12500000000000 : ℝ)^6385 := by
    have hnat : (4193178673 : ℕ)^8433*12500000000000^6385 ≤ 3966281201461^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4193178673 10000000000 3966281201461 12500000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3116966137/10000000000 : ℝ)^8433 ≤ (21445973155991/100000000000000 : ℝ)^6385 := by
    have hnat : (3116966137 : ℕ)^8433*100000000000000^6385 ≤ 21445973155991^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3116966137 10000000000 21445973155991 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (703729047/1250000000 : ℝ)^8433 ≤ (46823777219293/100000000000000 : ℝ)^6385 := by
    have hnat : (703729047 : ℕ)^8433*100000000000000^6385 ≤ 46823777219293^6385*1250000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      703729047 1250000000 46823777219293 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4193178673/10000000000 : ℝ), (3116966137/10000000000 : ℝ), (703729047/1250000000 : ℝ)] ![(3966281201461/12500000000000 : ℝ), (21445973155991/100000000000000 : ℝ), (46823777219293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4193178673/10000000000 : ℝ)|^8433 ≤ (3966281201461/12500000000000 : ℝ)^6385
        have hw : |(4193178673/10000000000 : ℝ)|=(4193178673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3116966137/10000000000 : ℝ)|^8433 ≤ (21445973155991/100000000000000 : ℝ)^6385
        have hw : |(3116966137/10000000000 : ℝ)|=(3116966137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(703729047/1250000000 : ℝ)|^8433 ≤ (46823777219293/100000000000000 : ℝ)^6385
        have hw : |(703729047/1250000000 : ℝ)|=(703729047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s0_4 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-373208113/2000000000 : ℝ)*x 0 + (2412326967/5000000000 : ℝ)*x 1 + (1199782873/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (373208113/2000000000 : ℝ)^8433 ≤ (10890999356913/100000000000000 : ℝ)^6385 := by
    have hnat : (373208113 : ℕ)^8433*100000000000000^6385 ≤ 10890999356913^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373208113 2000000000 10890999356913 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2412326967/5000000000 : ℝ)^8433 ≤ (19094460282271/50000000000000 : ℝ)^6385 := by
    have hnat : (2412326967 : ℕ)^8433*50000000000000^6385 ≤ 19094460282271^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2412326967 5000000000 19094460282271 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1199782873/2000000000 : ℝ)^8433 ≤ (25460040031273/50000000000000 : ℝ)^6385 := by
    have hnat : (1199782873 : ℕ)^8433*50000000000000^6385 ≤ 25460040031273^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199782873 2000000000 25460040031273 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-373208113/2000000000 : ℝ), (2412326967/5000000000 : ℝ), (1199782873/2000000000 : ℝ)] ![(10890999356913/100000000000000 : ℝ), (19094460282271/50000000000000 : ℝ), (25460040031273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-373208113/2000000000 : ℝ)|^8433 ≤ (10890999356913/100000000000000 : ℝ)^6385
        have hw : |(-373208113/2000000000 : ℝ)|=(373208113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2412326967/5000000000 : ℝ)|^8433 ≤ (19094460282271/50000000000000 : ℝ)^6385
        have hw : |(2412326967/5000000000 : ℝ)|=(2412326967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1199782873/2000000000 : ℝ)|^8433 ≤ (25460040031273/50000000000000 : ℝ)^6385
        have hw : |(1199782873/2000000000 : ℝ)|=(1199782873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s0_5 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2587053703/5000000000 : ℝ)*x 0 + (-1363484401/10000000000 : ℝ)*x 1 + (47991333/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587053703/5000000000 : ℝ)^8433 ≤ (10470987990177/25000000000000 : ℝ)^6385 := by
    have hnat : (2587053703 : ℕ)^8433*25000000000000^6385 ≤ 10470987990177^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587053703 5000000000 10470987990177 25000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363484401/10000000000 : ℝ)^8433 ≤ (719594263033/10000000000000 : ℝ)^6385 := by
    have hnat : (1363484401 : ℕ)^8433*10000000000000^6385 ≤ 719594263033^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363484401 10000000000 719594263033 10000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47991333/80000000 : ℝ)^8433 ≤ (10184021079803/20000000000000 : ℝ)^6385 := by
    have hnat : (47991333 : ℕ)^8433*20000000000000^6385 ≤ 10184021079803^6385*80000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47991333 80000000 10184021079803 20000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587053703/5000000000 : ℝ), (-1363484401/10000000000 : ℝ), (47991333/80000000 : ℝ)] ![(10470987990177/25000000000000 : ℝ), (719594263033/10000000000000 : ℝ), (10184021079803/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587053703/5000000000 : ℝ)|^8433 ≤ (10470987990177/25000000000000 : ℝ)^6385
        have hw : |(2587053703/5000000000 : ℝ)|=(2587053703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1363484401/10000000000 : ℝ)|^8433 ≤ (719594263033/10000000000000 : ℝ)^6385
        have hw : |(-1363484401/10000000000 : ℝ)|=(1363484401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(47991333/80000000 : ℝ)|^8433 ≤ (10184021079803/20000000000000 : ℝ)^6385
        have hw : |(47991333/80000000 : ℝ)|=(47991333/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s0_6 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1293527073/2500000000 : ℝ)*x 0 + (5998914829/10000000000 : ℝ)*x 1 + (-136348593/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1293527073/2500000000 : ℝ)^8433 ≤ (41883961433263/100000000000000 : ℝ)^6385 := by
    have hnat : (1293527073 : ℕ)^8433*100000000000000^6385 ≤ 41883961433263^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293527073 2500000000 41883961433263 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5998914829/10000000000 : ℝ)^8433 ≤ (50920085264369/100000000000000 : ℝ)^6385 := by
    have hnat : (5998914829 : ℕ)^8433*100000000000000^6385 ≤ 50920085264369^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5998914829 10000000000 50920085264369 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136348593/1000000000 : ℝ)^8433 ≤ (3597976644049/50000000000000 : ℝ)^6385 := by
    have hnat : (136348593 : ℕ)^8433*50000000000000^6385 ≤ 3597976644049^6385*1000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136348593 1000000000 3597976644049 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1293527073/2500000000 : ℝ), (5998914829/10000000000 : ℝ), (-136348593/1000000000 : ℝ)] ![(41883961433263/100000000000000 : ℝ), (50920085264369/100000000000000 : ℝ), (3597976644049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1293527073/2500000000 : ℝ)|^8433 ≤ (41883961433263/100000000000000 : ℝ)^6385
        have hw : |(1293527073/2500000000 : ℝ)|=(1293527073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5998914829/10000000000 : ℝ)|^8433 ≤ (50920085264369/100000000000000 : ℝ)^6385
        have hw : |(5998914829/10000000000 : ℝ)|=(5998914829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-136348593/1000000000 : ℝ)|^8433 ≤ (3597976644049/50000000000000 : ℝ)^6385
        have hw : |(-136348593/1000000000 : ℝ)|=(136348593/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s0_7 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (525380131/1250000000 : ℝ)*x 0 + (1113024621/2000000000 : ℝ)*x 1 + (127358481/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525380131/1250000000 : ℝ)^8433 ≤ (1273154162611/4000000000000 : ℝ)^6385 := by
    have hnat : (525380131 : ℕ)^8433*4000000000000^6385 ≤ 1273154162611^6385*1250000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525380131 1250000000 1273154162611 4000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1113024621/2000000000 : ℝ)^8433 ≤ (46114272498667/100000000000000 : ℝ)^6385 := by
    have hnat : (1113024621 : ℕ)^8433*100000000000000^6385 ≤ 46114272498667^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113024621 2000000000 46114272498667 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127358481/400000000 : ℝ)^8433 ≤ (11028436708829/50000000000000 : ℝ)^6385 := by
    have hnat : (127358481 : ℕ)^8433*50000000000000^6385 ≤ 11028436708829^6385*400000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127358481 400000000 11028436708829 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525380131/1250000000 : ℝ), (1113024621/2000000000 : ℝ), (127358481/400000000 : ℝ)] ![(1273154162611/4000000000000 : ℝ), (46114272498667/100000000000000 : ℝ), (11028436708829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525380131/1250000000 : ℝ)|^8433 ≤ (1273154162611/4000000000000 : ℝ)^6385
        have hw : |(525380131/1250000000 : ℝ)|=(525380131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1113024621/2000000000 : ℝ)|^8433 ≤ (46114272498667/100000000000000 : ℝ)^6385
        have hw : |(1113024621/2000000000 : ℝ)|=(1113024621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(127358481/400000000 : ℝ)|^8433 ≤ (11028436708829/50000000000000 : ℝ)^6385
        have hw : |(127358481/400000000 : ℝ)|=(127358481/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1240_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (81/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6861/25000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (527/128 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^527 ≤ (0 : ℝ)^128 := by
      have hnat : (0 : ℕ)^527*1^128 ≤ 0^128*1^527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 527 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (527/128 : ℝ) ≤ (229935681540278977/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^527 ≤ (229935681540278977/10000000000000000000 : ℝ)^128 := by
      have hnat : (2 : ℕ)^527*10000000000000000000^128 ≤ 229935681540278977^128*5^527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 229935681540278977 10000000000000000000 527 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (229935681540278977/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (1 : ℝ)^128 ≤ (1 : ℝ)^527 := by
      have hnat : (1 : ℕ)^128*1^527 ≤ 1^527*1^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (10229935681540278977/10000000000000000000 : ℝ) ≤ (1256921009935391/1250000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (10229935681540278977/10000000000000000000 : ℝ)^128 ≤ (1256921009935391/1250000000000000 : ℝ)^527 := by
      have hnat : (10229935681540278977 : ℕ)^128*1250000000000000^527 ≤ 1256921009935391^527*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10229935681540278977 10000000000000000000 1256921009935391 1250000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1256921009935391/1250000000000000 : ℝ)) (X := (10229935681540278977/10000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (5229935681540278977/5000000000000000000 : ℝ) ≤ (631921009935391/625000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (5229935681540278977/5000000000000000000 : ℝ)^128 ≤ (631921009935391/625000000000000 : ℝ)^527 := by
      have hnat : (5229935681540278977 : ℕ)^128*625000000000000^527 ≤ 631921009935391^527*5000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5229935681540278977 5000000000000000000 631921009935391 625000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (631921009935391/625000000000000 : ℝ)) (X := (5229935681540278977/5000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(6921009935391/500000000000000 : ℝ)*(0 : ℝ))^(527/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(6921009935391/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(229935681540278977/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(6921009935391/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(527/128 : ℝ) := by
    rw [show (1 : ℝ)+(6921009935391/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1256921009935391/1250000000000000 : ℝ) by norm_num, show 1+(229935681540278977/10000000000000000000 : ℝ)+(0 : ℝ)=(10229935681540278977/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(229935681540278977/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(6921009935391/500000000000000 : ℝ)*(2/5 : ℝ))^(527/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(6921009935391/500000000000000 : ℝ)*(2/5 : ℝ)=(631921009935391/625000000000000 : ℝ) by norm_num, show 1+2*(229935681540278977/10000000000000000000 : ℝ)=(5229935681540278977/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(6921009935391/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6921009935391/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(6921009935391/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6921009935391/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(6921009935391/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6921009935391/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1861177371/10000000000 : ℝ)*X 0 0+(3015978067/5000000000 : ℝ)*X 0 1+(4792740111/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1377818041/2500000000 : ℝ)*X 1 0+(-40150951/156250000 : ℝ)*X 1 1+(239637003/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((551127209/1000000000 : ℝ)*X 2 0+(2396370067/5000000000 : ℝ)*X 2 1+(-1284830433/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4193178673/10000000000 : ℝ)*X 0 0+(3116966137/10000000000 : ℝ)*X 0 1+(703729047/1250000000 : ℝ)*X 0 2+(4193178673/10000000000 : ℝ)*X 1 0+(3116966137/10000000000 : ℝ)*X 1 1+(703729047/1250000000 : ℝ)*X 1 2+(4193178673/10000000000 : ℝ)*X 2 0+(3116966137/10000000000 : ℝ)*X 2 1+(703729047/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-373208113/2000000000 : ℝ)*X 0 0+(2412326967/5000000000 : ℝ)*X 0 1+(1199782873/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2587053703/5000000000 : ℝ)*X 1 0+(-1363484401/10000000000 : ℝ)*X 1 1+(47991333/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1293527073/2500000000 : ℝ)*X 2 0+(5998914829/10000000000 : ℝ)*X 2 1+(-136348593/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((525380131/1250000000 : ℝ)*X 0 0+(1113024621/2000000000 : ℝ)*X 0 1+(127358481/400000000 : ℝ)*X 0 2+(525380131/1250000000 : ℝ)*X 1 0+(1113024621/2000000000 : ℝ)*X 1 1+(127358481/400000000 : ℝ)*X 1 2+(525380131/1250000000 : ℝ)*X 2 0+(1113024621/2000000000 : ℝ)*X 2 1+(127358481/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35270783326620899369289/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69581693/100000000000000 : ℝ)*(base1) + (1376442573/100000000000000 : ℝ)*(base19) + (637040761/50000000000000 : ℝ)*(base23) + (9152587/10000000000000 : ℝ)*(base24) + (154723337/50000000000000 : ℝ)*(upper3) + (150615681445831/25000000000000 : ℝ)*(major0) + (150615681445831/25000000000000 : ℝ)*(major1) + (150615681445831/25000000000000 : ℝ)*(major2) + (1613932945463/200000000000 : ℝ)*(sp0) + (3152219112963/390625000000 : ℝ)*(sp1) + (80696810375371/10000000000000 : ℝ)*(sp2) + (397953343141567/100000000000000 : ℝ)*(sp3) + (1533105647/50000000000000 : ℝ)*(sp4) + (2381371439/100000000000000 : ℝ)*(sp7) + (397955794094699/100000000000000 : ℝ)*(f.failure) + (806969469361101/100000000000000 : ℝ)*(f.sum) + (7703230276329/6250000000000000000000000000 : ℝ)*base66 + (11934053320079/12500000000000000000000000000 : ℝ)*base68 + (44360873407579/12500000000000000000000000000 : ℝ)*base70 + (56531764382579/12500000000000000000000000000 : ℝ)*base72 + (1253389832579/6250000000000000000000000000 : ℝ)*base74 + (5929165717421/12500000000000000000000000000 : ℝ)*base75 + (22415505732579/12500000000000000000000000000 : ℝ)*base78 + (71134622620079/12500000000000000000000000000 : ℝ)*base80 + (5032624386171/6250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (66907941/10000000000000000000000 : ℝ)*base89 + (66907941/10000000000000000000000 : ℝ)*base91 + (66907941/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47934770908639626392649/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74241111/50000000000000 : ℝ)*(base1) + (1879296521/100000000000000 : ℝ)*(base19) + (80755581/4000000000000 : ℝ)*(base23) + (377961497/100000000000000 : ℝ)*(upper3) + (34646707/50000000000000 : ℝ)*(upper5) + (317890566583771/50000000000000 : ℝ)*(major0) + (317890566583771/50000000000000 : ℝ)*(major1) + (317890566583771/50000000000000 : ℝ)*(major2) + (123672969/3125000000000 : ℝ)*(sp1) + (386191127/10000000000000 : ℝ)*(sp2) + (851597944132383/100000000000000 : ℝ)*(sp4) + (851591958818633/100000000000000 : ℝ)*(sp5) + (425795957424683/50000000000000 : ℝ)*(sp6) + (209982033275291/50000000000000 : ℝ)*(sp7) + (419964215032803/100000000000000 : ℝ)*(f.failure) + (851597795650161/100000000000000 : ℝ)*(f.sum) + (15514870123039/12500000000000000000000000000 : ℝ)*base66 + (331616246660539/25000000000000000000000000000 : ℝ)*base68 + (138438459485539/25000000000000000000000000000 : ℝ)*base70 + (236095282010539/25000000000000000000000000000 : ℝ)*base72 + (60290530423039/12500000000000000000000000000 : ℝ)*base74 + (256366267235539/25000000000000000000000000000 : ℝ)*base76 + (118519878560539/25000000000000000000000000000 : ℝ)*base78 + (352036593460539/25000000000000000000000000000 : ℝ)*base80 + (5886055235539/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (10143277/10000000000000000000000 : ℝ)*base89 + (10143277/10000000000000000000000 : ℝ)*base91 + (10143277/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1240_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (81/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6861/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1240_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1240_s1_0 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-514682583/2500000000 : ℝ)*x 0 + (1135223269/2000000000 : ℝ)*x 1 + (2511061909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (514682583/2500000000 : ℝ)^8433 ≤ (12400388212317/100000000000000 : ℝ)^6385 := by
    have hnat : (514682583 : ℕ)^8433*100000000000000^6385 ≤ 12400388212317^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514682583 2500000000 12400388212317 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1135223269/2000000000 : ℝ)^8433 ≤ (11833216622677/25000000000000 : ℝ)^6385 := by
    have hnat : (1135223269 : ℕ)^8433*25000000000000^6385 ≤ 11833216622677^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135223269 2000000000 11833216622677 25000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2511061909/5000000000 : ℝ)^8433 ≤ (20133372639451/50000000000000 : ℝ)^6385 := by
    have hnat : (2511061909 : ℕ)^8433*50000000000000^6385 ≤ 20133372639451^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2511061909 5000000000 20133372639451 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-514682583/2500000000 : ℝ), (1135223269/2000000000 : ℝ), (2511061909/5000000000 : ℝ)] ![(12400388212317/100000000000000 : ℝ), (11833216622677/25000000000000 : ℝ), (20133372639451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-514682583/2500000000 : ℝ)|^8433 ≤ (12400388212317/100000000000000 : ℝ)^6385
        have hw : |(-514682583/2500000000 : ℝ)|=(514682583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1135223269/2000000000 : ℝ)|^8433 ≤ (11833216622677/25000000000000 : ℝ)^6385
        have hw : |(1135223269/2000000000 : ℝ)|=(1135223269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2511061909/5000000000 : ℝ)|^8433 ≤ (20133372639451/50000000000000 : ℝ)^6385
        have hw : |(2511061909/5000000000 : ℝ)|=(2511061909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s1_1 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (338360573/625000000 : ℝ)*x 0 + (-2409951669/10000000000 : ℝ)*x 1 + (5022123963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338360573/625000000 : ℝ)^8433 ≤ (44465103204141/100000000000000 : ℝ)^6385 := by
    have hnat : (338360573 : ℕ)^8433*100000000000000^6385 ≤ 44465103204141^6385*625000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338360573 625000000 44465103204141 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2409951669/10000000000 : ℝ)^8433 ≤ (7634074981779/50000000000000 : ℝ)^6385 := by
    have hnat : (2409951669 : ℕ)^8433*50000000000000^6385 ≤ 7634074981779^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2409951669 10000000000 7634074981779 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5022123963/10000000000 : ℝ)^8433 ≤ (10066686703599/25000000000000 : ℝ)^6385 := by
    have hnat : (5022123963 : ℕ)^8433*25000000000000^6385 ≤ 10066686703599^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5022123963 10000000000 10066686703599 25000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(338360573/625000000 : ℝ), (-2409951669/10000000000 : ℝ), (5022123963/10000000000 : ℝ)] ![(44465103204141/100000000000000 : ℝ), (7634074981779/50000000000000 : ℝ), (10066686703599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(338360573/625000000 : ℝ)|^8433 ≤ (44465103204141/100000000000000 : ℝ)^6385
        have hw : |(338360573/625000000 : ℝ)|=(338360573/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2409951669/10000000000 : ℝ)|^8433 ≤ (7634074981779/50000000000000 : ℝ)^6385
        have hw : |(-2409951669/10000000000 : ℝ)|=(2409951669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5022123963/10000000000 : ℝ)|^8433 ≤ (10066686703599/25000000000000 : ℝ)^6385
        have hw : |(5022123963/10000000000 : ℝ)|=(5022123963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s1_2 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5413769303/10000000000 : ℝ)*x 0 + (502212387/1000000000 : ℝ)*x 1 + (-602487903/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5413769303/10000000000 : ℝ)^8433 ≤ (44465104668591/100000000000000 : ℝ)^6385 := by
    have hnat : (5413769303 : ℕ)^8433*100000000000000^6385 ≤ 44465104668591^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413769303 10000000000 44465104668591 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502212387/1000000000 : ℝ)^8433 ≤ (20133372914781/50000000000000 : ℝ)^6385 := by
    have hnat : (502212387 : ℕ)^8433*50000000000000^6385 ≤ 20133372914781^6385*1000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502212387 1000000000 20133372914781 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (602487903/2500000000 : ℝ)^8433 ≤ (7634074743303/50000000000000 : ℝ)^6385 := by
    have hnat : (602487903 : ℕ)^8433*50000000000000^6385 ≤ 7634074743303^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602487903 2500000000 7634074743303 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5413769303/10000000000 : ℝ), (502212387/1000000000 : ℝ), (-602487903/2500000000 : ℝ)] ![(44465104668591/100000000000000 : ℝ), (20133372914781/50000000000000 : ℝ), (7634074743303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5413769303/10000000000 : ℝ)|^8433 ≤ (44465104668591/100000000000000 : ℝ)^6385
        have hw : |(5413769303/10000000000 : ℝ)|=(5413769303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(502212387/1000000000 : ℝ)|^8433 ≤ (20133372914781/50000000000000 : ℝ)^6385
        have hw : |(502212387/1000000000 : ℝ)|=(502212387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-602487903/2500000000 : ℝ)|^8433 ≤ (7634074743303/50000000000000 : ℝ)^6385
        have hw : |(-602487903/2500000000 : ℝ)|=(602487903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s1_3 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2154513607/5000000000 : ℝ)*x 0 + (3695071351/10000000000 : ℝ)*x 1 + (1255307371/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154513607/5000000000 : ℝ)^8433 ≤ (32893170255469/100000000000000 : ℝ)^6385 := by
    have hnat : (2154513607 : ℕ)^8433*100000000000000^6385 ≤ 32893170255469^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154513607 5000000000 32893170255469 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3695071351/10000000000 : ℝ)^8433 ≤ (5369910966969/20000000000000 : ℝ)^6385 := by
    have hnat : (3695071351 : ℕ)^8433*20000000000000^6385 ≤ 5369910966969^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3695071351 10000000000 5369910966969 20000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1255307371/2500000000 : ℝ)^8433 ≤ (40257274893611/100000000000000 : ℝ)^6385 := by
    have hnat : (1255307371 : ℕ)^8433*100000000000000^6385 ≤ 40257274893611^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255307371 2500000000 40257274893611 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154513607/5000000000 : ℝ), (3695071351/10000000000 : ℝ), (1255307371/2500000000 : ℝ)] ![(32893170255469/100000000000000 : ℝ), (5369910966969/20000000000000 : ℝ), (40257274893611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154513607/5000000000 : ℝ)|^8433 ≤ (32893170255469/100000000000000 : ℝ)^6385
        have hw : |(2154513607/5000000000 : ℝ)|=(2154513607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3695071351/10000000000 : ℝ)|^8433 ≤ (5369910966969/20000000000000 : ℝ)^6385
        have hw : |(3695071351/10000000000 : ℝ)|=(3695071351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1255307371/2500000000 : ℝ)|^8433 ≤ (40257274893611/100000000000000 : ℝ)^6385
        have hw : |(1255307371/2500000000 : ℝ)|=(1255307371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s1_4 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2059409681/10000000000 : ℝ)*x 0 + (5030721799/10000000000 : ℝ)*x 1 + (5667354253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2059409681/10000000000 : ℝ)^8433 ≤ (775362058067/6250000000000 : ℝ)^6385 := by
    have hnat : (2059409681 : ℕ)^8433*6250000000000^6385 ≤ 775362058067^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059409681 10000000000 775362058067 6250000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5030721799/10000000000 : ℝ)^8433 ≤ (40357819606123/100000000000000 : ℝ)^6385 := by
    have hnat : (5030721799 : ℕ)^8433*100000000000000^6385 ≤ 40357819606123^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5030721799 10000000000 40357819606123 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5667354253/10000000000 : ℝ)^8433 ≤ (4723638745447/10000000000000 : ℝ)^6385 := by
    have hnat : (5667354253 : ℕ)^8433*10000000000000^6385 ≤ 4723638745447^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5667354253 10000000000 4723638745447 10000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2059409681/10000000000 : ℝ), (5030721799/10000000000 : ℝ), (5667354253/10000000000 : ℝ)] ![(775362058067/6250000000000 : ℝ), (40357819606123/100000000000000 : ℝ), (4723638745447/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2059409681/10000000000 : ℝ)|^8433 ≤ (775362058067/6250000000000 : ℝ)^6385
        have hw : |(-2059409681/10000000000 : ℝ)|=(2059409681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5030721799/10000000000 : ℝ)|^8433 ≤ (40357819606123/100000000000000 : ℝ)^6385
        have hw : |(5030721799/10000000000 : ℝ)|=(5030721799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5667354253/10000000000 : ℝ)|^8433 ≤ (4723638745447/10000000000000 : ℝ)^6385
        have hw : |(5667354253/10000000000 : ℝ)|=(5667354253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s1_5 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2622648693/5000000000 : ℝ)*x 0 + (-110295051/625000000 : ℝ)*x 1 + (1416838597/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2622648693/5000000000 : ℝ)^8433 ≤ (4264674474647/10000000000000 : ℝ)^6385 := by
    have hnat : (2622648693 : ℕ)^8433*10000000000000^6385 ≤ 4264674474647^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622648693 5000000000 4264674474647 10000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110295051/625000000 : ℝ)^8433 ≤ (404674652301/4000000000000 : ℝ)^6385 := by
    have hnat : (110295051 : ℕ)^8433*4000000000000^6385 ≤ 404674652301^6385*625000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110295051 625000000 404674652301 4000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1416838597/2500000000 : ℝ)^8433 ≤ (47236388940581/100000000000000 : ℝ)^6385 := by
    have hnat : (1416838597 : ℕ)^8433*100000000000000^6385 ≤ 47236388940581^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1416838597 2500000000 47236388940581 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2622648693/5000000000 : ℝ), (-110295051/625000000 : ℝ), (1416838597/2500000000 : ℝ)] ![(4264674474647/10000000000000 : ℝ), (404674652301/4000000000000 : ℝ), (47236388940581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2622648693/5000000000 : ℝ)|^8433 ≤ (4264674474647/10000000000000 : ℝ)^6385
        have hw : |(2622648693/5000000000 : ℝ)|=(2622648693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-110295051/625000000 : ℝ)|^8433 ≤ (404674652301/4000000000000 : ℝ)^6385
        have hw : |(-110295051/625000000 : ℝ)|=(110295051/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1416838597/2500000000 : ℝ)|^8433 ≤ (47236388940581/100000000000000 : ℝ)^6385
        have hw : |(1416838597/2500000000 : ℝ)|=(1416838597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s1_6 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1311324437/2500000000 : ℝ)*x 0 + (5667355159/10000000000 : ℝ)*x 1 + (-88235959/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311324437/2500000000 : ℝ)^8433 ≤ (42646748633747/100000000000000 : ℝ)^6385 := by
    have hnat : (1311324437 : ℕ)^8433*100000000000000^6385 ≤ 42646748633747^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311324437 2500000000 42646748633747 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5667355159/10000000000 : ℝ)^8433 ≤ (47236397427927/100000000000000 : ℝ)^6385 := by
    have hnat : (5667355159 : ℕ)^8433*100000000000000^6385 ≤ 47236397427927^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5667355159 10000000000 47236397427927 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88235959/500000000 : ℝ)^8433 ≤ (316151685009/3125000000000 : ℝ)^6385 := by
    have hnat : (88235959 : ℕ)^8433*3125000000000^6385 ≤ 316151685009^6385*500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88235959 500000000 316151685009 3125000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1311324437/2500000000 : ℝ), (5667355159/10000000000 : ℝ), (-88235959/500000000 : ℝ)] ![(42646748633747/100000000000000 : ℝ), (47236397427927/100000000000000 : ℝ), (316151685009/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1311324437/2500000000 : ℝ)|^8433 ≤ (42646748633747/100000000000000 : ℝ)^6385
        have hw : |(1311324437/2500000000 : ℝ)|=(1311324437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5667355159/10000000000 : ℝ)|^8433 ≤ (47236397427927/100000000000000 : ℝ)^6385
        have hw : |(5667355159/10000000000 : ℝ)|=(5667355159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-88235959/500000000 : ℝ)|^8433 ≤ (316151685009/3125000000000 : ℝ)^6385
        have hw : |(-88235959/500000000 : ℝ)|=(88235959/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s1_7 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2155201587/5000000000 : ℝ)*x 0 + (1250948841/2500000000 : ℝ)*x 1 + (464104701/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155201587/5000000000 : ℝ)^8433 ≤ (25708627677/78125000000 : ℝ)^6385 := by
    have hnat : (2155201587 : ℕ)^8433*78125000000^6385 ≤ 25708627677^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155201587 5000000000 25708627677 78125000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1250948841/2500000000 : ℝ)^8433 ≤ (40072767640633/100000000000000 : ℝ)^6385 := by
    have hnat : (1250948841 : ℕ)^8433*100000000000000^6385 ≤ 40072767640633^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250948841 2500000000 40072767640633 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (464104701/1250000000 : ℝ)^8433 ≤ (3377523615201/12500000000000 : ℝ)^6385 := by
    have hnat : (464104701 : ℕ)^8433*12500000000000^6385 ≤ 3377523615201^6385*1250000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464104701 1250000000 3377523615201 12500000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155201587/5000000000 : ℝ), (1250948841/2500000000 : ℝ), (464104701/1250000000 : ℝ)] ![(25708627677/78125000000 : ℝ), (40072767640633/100000000000000 : ℝ), (3377523615201/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155201587/5000000000 : ℝ)|^8433 ≤ (25708627677/78125000000 : ℝ)^6385
        have hw : |(2155201587/5000000000 : ℝ)|=(2155201587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1250948841/2500000000 : ℝ)|^8433 ≤ (40072767640633/100000000000000 : ℝ)^6385
        have hw : |(1250948841/2500000000 : ℝ)|=(1250948841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(464104701/1250000000 : ℝ)|^8433 ≤ (3377523615201/12500000000000 : ℝ)^6385
        have hw : |(464104701/1250000000 : ℝ)|=(464104701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1240_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6861/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (81/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (309/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20007/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6861/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (81/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6861/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (81/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6861/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (81/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6861/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (81/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6861/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (81/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6861/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (81/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (81/10000 : ℝ) ^ (527/128 : ℝ) ≤ (122408244047/50000000000000000000 : ℝ) := by
    have hpowers : (81/10000 : ℝ)^527 ≤ (122408244047/50000000000000000000 : ℝ)^128 := by
      have hnat : (81 : ℕ)^527*50000000000000000000^128 ≤ 122408244047^128*10000^527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81 10000 122408244047 50000000000000000000 527 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (81/10000 : ℝ)) (X := (122408244047/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hpowhi : (6861/25000 : ℝ) ^ (527/128 : ℝ) ≤ (487509068304581961/100000000000000000000 : ℝ) := by
    have hpowers : (6861/25000 : ℝ)^527 ≤ (487509068304581961/100000000000000000000 : ℝ)^128 := by
      have hnat : (6861 : ℕ)^527*100000000000000000000^128 ≤ 487509068304581961^128*25000^527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6861 25000 487509068304581961 100000000000000000000 527 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6861/25000 : ℝ)) (X := (487509068304581961/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000122408244047/25000000000000000000 : ℝ) ≤ (5000000005946207/5000000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (25000000122408244047/25000000000000000000 : ℝ)^128 ≤ (5000000005946207/5000000000000000 : ℝ)^527 := by
      have hnat : (25000000122408244047 : ℕ)^128*5000000000000000^527 ≤ 5000000005946207^527*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000122408244047 25000000000000000000 5000000005946207 5000000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000005946207/5000000000000000 : ℝ)) (X := (25000000122408244047/25000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (20097501862624214011/20000000000000000000 : ℝ) ≤ (5005909521641569/5000000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (20097501862624214011/20000000000000000000 : ℝ)^128 ≤ (5005909521641569/5000000000000000 : ℝ)^527 := by
      have hnat : (20097501862624214011 : ℕ)^128*5000000000000000^527 ≤ 5005909521641569^527*20000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20097501862624214011 20000000000000000000 5005909521641569 5000000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005909521641569/5000000000000000 : ℝ)) (X := (20097501862624214011/20000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50487509068304581961/50000000000000000000 : ℝ) ≤ (5011819037336931/5000000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (50487509068304581961/50000000000000000000 : ℝ)^128 ≤ (5011819037336931/5000000000000000 : ℝ)^527 := by
      have hnat : (50487509068304581961 : ℕ)^128*5000000000000000^527 ≤ 5011819037336931^527*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50487509068304581961 50000000000000000000 5011819037336931 5000000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011819037336931/5000000000000000 : ℝ)) (X := (50487509068304581961/50000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(122408244047/50000000000000000000 : ℝ) ≤ ((22193404457157465133/22195000000000000000 : ℝ)+2*(2954757847681/665850000000000 : ℝ)*(81/10000 : ℝ))^(527/128 : ℝ) := by
    rw [show (22193404457157465133/22195000000000000000 : ℝ)+2*(2954757847681/665850000000000 : ℝ)*(81/10000 : ℝ)=(5000000005946207/5000000000000000 : ℝ) by norm_num, show 1+2*(122408244047/50000000000000000000 : ℝ)=(25000000122408244047/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(487509068304581961/100000000000000000000 : ℝ)+(122408244047/50000000000000000000 : ℝ) ≤ ((22193404457157465133/22195000000000000000 : ℝ)+(2954757847681/665850000000000 : ℝ)*((6861/25000 : ℝ)+(81/10000 : ℝ)))^(527/128 : ℝ) := by
    rw [show (22193404457157465133/22195000000000000000 : ℝ)+(2954757847681/665850000000000 : ℝ)*((6861/25000 : ℝ)+(81/10000 : ℝ))=(5005909521641569/5000000000000000 : ℝ) by norm_num, show 1+(487509068304581961/100000000000000000000 : ℝ)+(122408244047/50000000000000000000 : ℝ)=(20097501862624214011/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(487509068304581961/100000000000000000000 : ℝ) ≤ ((22193404457157465133/22195000000000000000 : ℝ)+2*(2954757847681/665850000000000 : ℝ)*(6861/25000 : ℝ))^(527/128 : ℝ) := by
    rw [show (22193404457157465133/22195000000000000000 : ℝ)+2*(2954757847681/665850000000000 : ℝ)*(6861/25000 : ℝ)=(5011819037336931/5000000000000000 : ℝ) by norm_num, show 1+2*(487509068304581961/100000000000000000000 : ℝ)=(50487509068304581961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22193404457157465133/22195000000000000000 : ℝ)*(X 1 0+X 2 0)+(2954757847681/665850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (81/10000 : ℝ)) (hi := (6861/25000 : ℝ)) (c := (22193404457157465133/22195000000000000000 : ℝ)) (alpha := (2954757847681/665850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22193404457157465133/22195000000000000000 : ℝ)*(X 0 1+X 2 1)+(2954757847681/665850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (81/10000 : ℝ)) (hi := (6861/25000 : ℝ)) (c := (22193404457157465133/22195000000000000000 : ℝ)) (alpha := (2954757847681/665850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22193404457157465133/22195000000000000000 : ℝ)*(X 0 2+X 1 2)+(2954757847681/665850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (81/10000 : ℝ)) (hi := (6861/25000 : ℝ)) (c := (22193404457157465133/22195000000000000000 : ℝ)) (alpha := (2954757847681/665850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-514682583/2500000000 : ℝ)*X 0 0+(1135223269/2000000000 : ℝ)*X 0 1+(2511061909/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((338360573/625000000 : ℝ)*X 1 0+(-2409951669/10000000000 : ℝ)*X 1 1+(5022123963/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5413769303/10000000000 : ℝ)*X 2 0+(502212387/1000000000 : ℝ)*X 2 1+(-602487903/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2154513607/5000000000 : ℝ)*X 0 0+(3695071351/10000000000 : ℝ)*X 0 1+(1255307371/2500000000 : ℝ)*X 0 2+(2154513607/5000000000 : ℝ)*X 1 0+(3695071351/10000000000 : ℝ)*X 1 1+(1255307371/2500000000 : ℝ)*X 1 2+(2154513607/5000000000 : ℝ)*X 2 0+(3695071351/10000000000 : ℝ)*X 2 1+(1255307371/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2059409681/10000000000 : ℝ)*X 0 0+(5030721799/10000000000 : ℝ)*X 0 1+(5667354253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2622648693/5000000000 : ℝ)*X 1 0+(-110295051/625000000 : ℝ)*X 1 1+(1416838597/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1311324437/2500000000 : ℝ)*X 2 0+(5667355159/10000000000 : ℝ)*X 2 1+(-88235959/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2155201587/5000000000 : ℝ)*X 0 0+(1250948841/2500000000 : ℝ)*X 0 1+(464104701/1250000000 : ℝ)*X 0 2+(2155201587/5000000000 : ℝ)*X 1 0+(1250948841/2500000000 : ℝ)*X 1 1+(464104701/1250000000 : ℝ)*X 1 2+(2155201587/5000000000 : ℝ)*X 2 0+(1250948841/2500000000 : ℝ)*X 2 1+(464104701/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (587233617688648234216813753/69359375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44399831/50000000000000 : ℝ)*(base1) + (369468941/20000000000000 : ℝ)*(base19) + (188547469/10000000000000 : ℝ)*(base23) + (49937409/25000000000000 : ℝ)*(upper3) + (46197531/20000000000000 : ℝ)*(upper5) + (142697446801297/12500000000000 : ℝ)*(major0) + (142697446801297/12500000000000 : ℝ)*(major1) + (142697446801297/12500000000000 : ℝ)*(major2) + (1529079576775621/100000000000000 : ℝ)*(sp0) + (1529088449346097/100000000000000 : ℝ)*(sp1) + (1529088411216113/100000000000000 : ℝ)*(sp2) + (754063163909803/100000000000000 : ℝ)*(sp3) + (10808714843/100000000000000 : ℝ)*(sp4) + (83081291/1562500000000 : ℝ)*(sp7) + (94258571239011/12500000000000 : ℝ)*(f.failure) + (1529090296690803/100000000000000 : ℝ)*(f.sum) + (151471659437243/66585000000000000000000000000 : ℝ)*base66 + (5235085079163454997/832312500000000000000000000000000 : ℝ)*base68 + (2324035913142829997/832312500000000000000000000000000 : ℝ)*base70 + (3198805849825392497/832312500000000000000000000000000 : ℝ)*base72 + (24791164658881/8323125000000000000000000000 : ℝ)*base74 + (2155383273181045003/832312500000000000000000000000000 : ℝ)*base75 + (6327170522008579997/832312500000000000000000000000000 : ℝ)*base78 + (7078931520290704997/832312500000000000000000000000000 : ℝ)*base80 + (5394852550171/8323125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (11083949/1250000000000000000000 : ℝ)*base89 + (11083949/1250000000000000000000 : ℝ)*base91 + (11083949/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (731577089252049326823/22195000000000000000000000000 : ℝ) := by norm_num
    linear_combination (130739847/20000000000000 : ℝ)*(base19) + (11947439/1000000000000 : ℝ)*(base23) + (126484953/100000000000000 : ℝ)*(upper2) + (36348077/25000000000000 : ℝ)*(upper3) + (6439027/50000000000000 : ℝ)*(upper5) + (293172859617817/25000000000000 : ℝ)*(major0) + (293172859617817/25000000000000 : ℝ)*(major1) + (293172859617817/25000000000000 : ℝ)*(major2) + (2464820369/100000000000000 : ℝ)*(sp1) + (8427104483/100000000000000 : ℝ)*(sp2) + (157076341367193/10000000000000 : ℝ)*(sp4) + (1570760295152327/100000000000000 : ℝ)*(sp5) + (785376895911773/50000000000000 : ℝ)*(sp6) + (48413716385743/6250000000000 : ℝ)*(sp7) + (48413716385743/6250000000000 : ℝ)*(f.failure) + (157076341367193/10000000000000 : ℝ)*(f.sum) + (85450740394727/33292500000000000000000000000 : ℝ)*base66 + (3248540629454826017/1664625000000000000000000000000000 : ℝ)*base68 + (6374901375199673983/1664625000000000000000000000000000 : ℝ)*base69 + (7013495276630826017/1664625000000000000000000000000000 : ℝ)*base72 + (209003039600299/66585000000000000000000000000 : ℝ)*base74 + (17537511546395451017/1664625000000000000000000000000000 : ℝ)*base76 + (5886084119102798983/1664625000000000000000000000000000 : ℝ)*base77 + (10711535712492923983/1664625000000000000000000000000000 : ℝ)*base79 + (17054469720091/16646250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (4508737/625000000000000000000 : ℝ)*base89 + (4508737/625000000000000000000 : ℝ)*base91 + (4508737/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1240_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6861/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (81/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (309/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20007/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1240_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1240_s2_0 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-526719859/2500000000 : ℝ)*x 0 + (1098626357/2000000000 : ℝ)*x 1 + (5053128/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526719859/2500000000 : ℝ)^8433 ≤ (6392429184843/50000000000000 : ℝ)^6385 := by
    have hnat : (526719859 : ℕ)^8433*50000000000000^6385 ≤ 6392429184843^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526719859 2500000000 6392429184843 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098626357/2000000000 : ℝ)^8433 ≤ (22664014272953/50000000000000 : ℝ)^6385 := by
    have hnat : (1098626357 : ℕ)^8433*50000000000000^6385 ≤ 22664014272953^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098626357 2000000000 22664014272953 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5053128/9765625 : ℝ)^8433 ≤ (2094355653233/5000000000000 : ℝ)^6385 := by
    have hnat : (5053128 : ℕ)^8433*5000000000000^6385 ≤ 2094355653233^6385*9765625^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5053128 9765625 2094355653233 5000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-526719859/2500000000 : ℝ), (1098626357/2000000000 : ℝ), (5053128/9765625 : ℝ)] ![(6392429184843/50000000000000 : ℝ), (22664014272953/50000000000000 : ℝ), (2094355653233/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-526719859/2500000000 : ℝ)|^8433 ≤ (6392429184843/50000000000000 : ℝ)^6385
        have hw : |(-526719859/2500000000 : ℝ)|=(526719859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1098626357/2000000000 : ℝ)|^8433 ≤ (22664014272953/50000000000000 : ℝ)^6385
        have hw : |(1098626357/2000000000 : ℝ)|=(1098626357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5053128/9765625 : ℝ)|^8433 ≤ (2094355653233/5000000000000 : ℝ)^6385
        have hw : |(5053128/9765625 : ℝ)|=(5053128/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s2_1 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369766897/10000000000 : ℝ)*x 0 + (-1135995103/5000000000 : ℝ)*x 1 + (5174403067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369766897/10000000000 : ℝ)^8433 ≤ (43988399707911/100000000000000 : ℝ)^6385 := by
    have hnat : (5369766897 : ℕ)^8433*100000000000000^6385 ≤ 43988399707911^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369766897 10000000000 43988399707911 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1135995103/5000000000 : ℝ)^8433 ≤ (3531121815829/25000000000000 : ℝ)^6385 := by
    have hnat : (1135995103 : ℕ)^8433*25000000000000^6385 ≤ 3531121815829^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135995103 5000000000 3531121815829 25000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5174403067/10000000000 : ℝ)^8433 ≤ (20943556505601/50000000000000 : ℝ)^6385 := by
    have hnat : (5174403067 : ℕ)^8433*50000000000000^6385 ≤ 20943556505601^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174403067 10000000000 20943556505601 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369766897/10000000000 : ℝ), (-1135995103/5000000000 : ℝ), (5174403067/10000000000 : ℝ)] ![(43988399707911/100000000000000 : ℝ), (3531121815829/25000000000000 : ℝ), (20943556505601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369766897/10000000000 : ℝ)|^8433 ≤ (43988399707911/100000000000000 : ℝ)^6385
        have hw : |(5369766897/10000000000 : ℝ)|=(5369766897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1135995103/5000000000 : ℝ)|^8433 ≤ (3531121815829/25000000000000 : ℝ)^6385
        have hw : |(-1135995103/5000000000 : ℝ)|=(1135995103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5174403067/10000000000 : ℝ)|^8433 ≤ (20943556505601/50000000000000 : ℝ)^6385
        have hw : |(5174403067/10000000000 : ℝ)|=(5174403067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s2_2 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (268488337/500000000 : ℝ)*x 0 + (1034880639/2000000000 : ℝ)*x 1 + (-1135995123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268488337/500000000 : ℝ)^8433 ≤ (21994199004631/50000000000000 : ℝ)^6385 := by
    have hnat : (268488337 : ℕ)^8433*50000000000000^6385 ≤ 21994199004631^6385*500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268488337 500000000 21994199004631 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034880639/2000000000 : ℝ)^8433 ≤ (20943557189861/50000000000000 : ℝ)^6385 := by
    have hnat : (1034880639 : ℕ)^8433*50000000000000^6385 ≤ 20943557189861^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034880639 2000000000 20943557189861 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135995123/5000000000 : ℝ)^8433 ≤ (14124487591749/100000000000000 : ℝ)^6385 := by
    have hnat : (1135995123 : ℕ)^8433*100000000000000^6385 ≤ 14124487591749^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135995123 5000000000 14124487591749 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268488337/500000000 : ℝ), (1034880639/2000000000 : ℝ), (-1135995123/5000000000 : ℝ)] ![(21994199004631/50000000000000 : ℝ), (20943557189861/50000000000000 : ℝ), (14124487591749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268488337/500000000 : ℝ)|^8433 ≤ (21994199004631/50000000000000 : ℝ)^6385
        have hw : |(268488337/500000000 : ℝ)|=(268488337/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1034880639/2000000000 : ℝ)|^8433 ≤ (20943557189861/50000000000000 : ℝ)^6385
        have hw : |(1034880639/2000000000 : ℝ)|=(1034880639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1135995123/5000000000 : ℝ)|^8433 ≤ (14124487591749/100000000000000 : ℝ)^6385
        have hw : |(-1135995123/5000000000 : ℝ)|=(1135995123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s2_3 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (868455841/2000000000 : ℝ)*x 0 + (2015387303/5000000000 : ℝ)*x 1 + (292318039/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868455841/2000000000 : ℝ)^8433 ≤ (16614415889393/50000000000000 : ℝ)^6385 := by
    have hnat : (868455841 : ℕ)^8433*50000000000000^6385 ≤ 16614415889393^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868455841 2000000000 16614415889393 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015387303/5000000000 : ℝ)^8433 ≤ (7529327589349/25000000000000 : ℝ)^6385 := by
    have hnat : (2015387303 : ℕ)^8433*25000000000000^6385 ≤ 7529327589349^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015387303 5000000000 7529327589349 25000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (292318039/625000000 : ℝ)^8433 ≤ (2290866115377/6250000000000 : ℝ)^6385 := by
    have hnat : (292318039 : ℕ)^8433*6250000000000^6385 ≤ 2290866115377^6385*625000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292318039 625000000 2290866115377 6250000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(868455841/2000000000 : ℝ), (2015387303/5000000000 : ℝ), (292318039/625000000 : ℝ)] ![(16614415889393/50000000000000 : ℝ), (7529327589349/25000000000000 : ℝ), (2290866115377/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(868455841/2000000000 : ℝ)|^8433 ≤ (16614415889393/50000000000000 : ℝ)^6385
        have hw : |(868455841/2000000000 : ℝ)|=(868455841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2015387303/5000000000 : ℝ)|^8433 ≤ (7529327589349/25000000000000 : ℝ)^6385
        have hw : |(2015387303/5000000000 : ℝ)|=(2015387303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(292318039/625000000 : ℝ)|^8433 ≤ (2290866115377/6250000000000 : ℝ)^6385
        have hw : |(292318039/625000000 : ℝ)|=(292318039/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s2_4 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-526739569/2500000000 : ℝ)*x 0 + (1035290979/2000000000 : ℝ)*x 1 + (686382587/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526739569/2500000000 : ℝ)^8433 ≤ (12785490238117/100000000000000 : ℝ)^6385 := by
    have hnat : (526739569 : ℕ)^8433*100000000000000^6385 ≤ 12785490238117^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526739569 2500000000 12785490238117 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035290979/2000000000 : ℝ)^8433 ≤ (41909051663191/100000000000000 : ℝ)^6385 := by
    have hnat : (1035290979 : ℕ)^8433*100000000000000^6385 ≤ 41909051663191^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035290979 2000000000 41909051663191 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (686382587/1250000000 : ℝ)^8433 ≤ (22652729040371/50000000000000 : ℝ)^6385 := by
    have hnat : (686382587 : ℕ)^8433*50000000000000^6385 ≤ 22652729040371^6385*1250000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686382587 1250000000 22652729040371 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-526739569/2500000000 : ℝ), (1035290979/2000000000 : ℝ), (686382587/1250000000 : ℝ)] ![(12785490238117/100000000000000 : ℝ), (41909051663191/100000000000000 : ℝ), (22652729040371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-526739569/2500000000 : ℝ)|^8433 ≤ (12785490238117/100000000000000 : ℝ)^6385
        have hw : |(-526739569/2500000000 : ℝ)|=(526739569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035290979/2000000000 : ℝ)|^8433 ≤ (41909051663191/100000000000000 : ℝ)^6385
        have hw : |(1035290979/2000000000 : ℝ)|=(1035290979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(686382587/1250000000 : ℝ)|^8433 ≤ (22652729040371/50000000000000 : ℝ)^6385
        have hw : |(686382587/1250000000 : ℝ)|=(686382587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s2_5 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322095577/2500000000 : ℝ)*x 0 + (-1955332363/10000000000 : ℝ)*x 1 + (5491060739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322095577/2500000000 : ℝ)^8433 ≤ (4311001344131/10000000000000 : ℝ)^6385 := by
    have hnat : (1322095577 : ℕ)^8433*10000000000000^6385 ≤ 4311001344131^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322095577 2500000000 4311001344131 10000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1955332363/10000000000 : ℝ)^8433 ≤ (11584527992453/100000000000000 : ℝ)^6385 := by
    have hnat : (1955332363 : ℕ)^8433*100000000000000^6385 ≤ 11584527992453^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955332363 10000000000 11584527992453 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5491060739/10000000000 : ℝ)^8433 ≤ (45305458549323/100000000000000 : ℝ)^6385 := by
    have hnat : (5491060739 : ℕ)^8433*100000000000000^6385 ≤ 45305458549323^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491060739 10000000000 45305458549323 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322095577/2500000000 : ℝ), (-1955332363/10000000000 : ℝ), (5491060739/10000000000 : ℝ)] ![(4311001344131/10000000000000 : ℝ), (11584527992453/100000000000000 : ℝ), (45305458549323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322095577/2500000000 : ℝ)|^8433 ≤ (4311001344131/10000000000000 : ℝ)^6385
        have hw : |(1322095577/2500000000 : ℝ)|=(1322095577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1955332363/10000000000 : ℝ)|^8433 ≤ (11584527992453/100000000000000 : ℝ)^6385
        have hw : |(-1955332363/10000000000 : ℝ)|=(1955332363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5491060739/10000000000 : ℝ)|^8433 ≤ (45305458549323/100000000000000 : ℝ)^6385
        have hw : |(5491060739/10000000000 : ℝ)|=(5491060739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s2_6 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322095619/2500000000 : ℝ)*x 0 + (2745530409/5000000000 : ℝ)*x 1 + (-977666011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322095619/2500000000 : ℝ)^8433 ≤ (43110015250091/100000000000000 : ℝ)^6385 := by
    have hnat : (1322095619 : ℕ)^8433*100000000000000^6385 ≤ 43110015250091^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322095619 2500000000 43110015250091 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2745530409/5000000000 : ℝ)^8433 ≤ (22652729705101/50000000000000 : ℝ)^6385 := by
    have hnat : (2745530409 : ℕ)^8433*50000000000000^6385 ≤ 22652729705101^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745530409 5000000000 22652729705101 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (977666011/5000000000 : ℝ)^8433 ≤ (11584525324161/100000000000000 : ℝ)^6385 := by
    have hnat : (977666011 : ℕ)^8433*100000000000000^6385 ≤ 11584525324161^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977666011 5000000000 11584525324161 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322095619/2500000000 : ℝ), (2745530409/5000000000 : ℝ), (-977666011/5000000000 : ℝ)] ![(43110015250091/100000000000000 : ℝ), (22652729705101/50000000000000 : ℝ), (11584525324161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322095619/2500000000 : ℝ)|^8433 ≤ (43110015250091/100000000000000 : ℝ)^6385
        have hw : |(1322095619/2500000000 : ℝ)|=(1322095619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2745530409/5000000000 : ℝ)|^8433 ≤ (22652729705101/50000000000000 : ℝ)^6385
        have hw : |(2745530409/5000000000 : ℝ)|=(2745530409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-977666011/5000000000 : ℝ)|^8433 ≤ (11584525324161/100000000000000 : ℝ)^6385
        have hw : |(-977666011/5000000000 : ℝ)|=(977666011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s2_7 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4342438537/10000000000 : ℝ)*x 0 + (934585641/2000000000 : ℝ)*x 1 + (806994757/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342438537/10000000000 : ℝ)^8433 ≤ (33230442142923/100000000000000 : ℝ)^6385 := by
    have hnat : (4342438537 : ℕ)^8433*100000000000000^6385 ≤ 33230442142923^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342438537 10000000000 33230442142923 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (934585641/2000000000 : ℝ)^8433 ≤ (9152700295243/25000000000000 : ℝ)^6385 := by
    have hnat : (934585641 : ℕ)^8433*25000000000000^6385 ≤ 9152700295243^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934585641 2000000000 9152700295243 25000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806994757/2000000000 : ℝ)^8433 ≤ (1206350266403/4000000000000 : ℝ)^6385 := by
    have hnat : (806994757 : ℕ)^8433*4000000000000^6385 ≤ 1206350266403^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806994757 2000000000 1206350266403 4000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342438537/10000000000 : ℝ), (934585641/2000000000 : ℝ), (806994757/2000000000 : ℝ)] ![(33230442142923/100000000000000 : ℝ), (9152700295243/25000000000000 : ℝ), (1206350266403/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342438537/10000000000 : ℝ)|^8433 ≤ (33230442142923/100000000000000 : ℝ)^6385
        have hw : |(4342438537/10000000000 : ℝ)|=(4342438537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(934585641/2000000000 : ℝ)|^8433 ≤ (9152700295243/25000000000000 : ℝ)^6385
        have hw : |(934585641/2000000000 : ℝ)|=(934585641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(806994757/2000000000 : ℝ)|^8433 ≤ (1206350266403/4000000000000 : ℝ)^6385
        have hw : |(806994757/2000000000 : ℝ)|=(806994757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1240_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (309/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (9491/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4057/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (309/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (309/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (309/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (309/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (309/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (309/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (309/5000 : ℝ) ^ (527/128 : ℝ) ≤ (105262301716753/10000000000000000000 : ℝ) := by
    have hpowers : (309/5000 : ℝ)^527 ≤ (105262301716753/10000000000000000000 : ℝ)^128 := by
      have hnat : (309 : ℕ)^527*10000000000000000000^128 ≤ 105262301716753^128*5000^527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        309 5000 105262301716753 10000000000000000000 527 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (309/5000 : ℝ)) (X := (105262301716753/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hpowhi : (20007/100000 : ℝ) ^ (527/128 : ℝ) ≤ (132689070221631733/100000000000000000000 : ℝ) := by
    have hpowers : (20007/100000 : ℝ)^527 ≤ (132689070221631733/100000000000000000000 : ℝ)^128 := by
      have hnat : (20007 : ℕ)^527*100000000000000000000^128 ≤ 132689070221631733^128*100000^527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007 100000 132689070221631733 100000000000000000000 527 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20007/100000 : ℝ)) (X := (132689070221631733/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000105262301716753/5000000000000000000 : ℝ) ≤ (312501597896969/312500000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (5000105262301716753/5000000000000000000 : ℝ)^128 ≤ (312501597896969/312500000000000 : ℝ)^527 := by
      have hnat : (5000105262301716753 : ℕ)^128*312500000000000^527 ≤ 312501597896969^527*5000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000105262301716753 5000000000000000000 312501597896969 312500000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312501597896969/312500000000000 : ℝ)) (X := (5000105262301716753/5000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100133741693238799263/100000000000000000000 : ℝ) ≤ (2500811682940039/2500000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (100133741693238799263/100000000000000000000 : ℝ)^128 ≤ (2500811682940039/2500000000000000 : ℝ)^527 := by
      have hnat : (100133741693238799263 : ℕ)^128*2500000000000000^527 ≤ 2500811682940039^527*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100133741693238799263 100000000000000000000 2500811682940039 2500000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500811682940039/2500000000000000 : ℝ)) (X := (100133741693238799263/100000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50132689070221631733/50000000000000000000 : ℝ) ≤ (1250805291352163/1250000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (50132689070221631733/50000000000000000000 : ℝ)^128 ≤ (1250805291352163/1250000000000000 : ℝ)^527 := by
      have hnat : (50132689070221631733 : ℕ)^128*1250000000000000^527 ≤ 1250805291352163^527*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50132689070221631733 50000000000000000000 1250805291352163 1250000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250805291352163/1250000000000000 : ℝ)) (X := (50132689070221631733/50000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(105262301716753/10000000000000000000 : ℝ) ≤ ((359977107832130579/360078125000000000 : ℝ)+2*(266299921429/115225000000000 : ℝ)*(309/5000 : ℝ))^(527/128 : ℝ) := by
    rw [show (359977107832130579/360078125000000000 : ℝ)+2*(266299921429/115225000000000 : ℝ)*(309/5000 : ℝ)=(312501597896969/312500000000000 : ℝ) by norm_num, show 1+2*(105262301716753/10000000000000000000 : ℝ)=(5000105262301716753/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(132689070221631733/100000000000000000000 : ℝ)+(105262301716753/10000000000000000000 : ℝ) ≤ ((359977107832130579/360078125000000000 : ℝ)+(266299921429/115225000000000 : ℝ)*((20007/100000 : ℝ)+(309/5000 : ℝ)))^(527/128 : ℝ) := by
    rw [show (359977107832130579/360078125000000000 : ℝ)+(266299921429/115225000000000 : ℝ)*((20007/100000 : ℝ)+(309/5000 : ℝ))=(2500811682940039/2500000000000000 : ℝ) by norm_num, show 1+(132689070221631733/100000000000000000000 : ℝ)+(105262301716753/10000000000000000000 : ℝ)=(100133741693238799263/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(132689070221631733/100000000000000000000 : ℝ) ≤ ((359977107832130579/360078125000000000 : ℝ)+2*(266299921429/115225000000000 : ℝ)*(20007/100000 : ℝ))^(527/128 : ℝ) := by
    rw [show (359977107832130579/360078125000000000 : ℝ)+2*(266299921429/115225000000000 : ℝ)*(20007/100000 : ℝ)=(1250805291352163/1250000000000000 : ℝ) by norm_num, show 1+2*(132689070221631733/100000000000000000000 : ℝ)=(50132689070221631733/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (359977107832130579/360078125000000000 : ℝ)*(X 1 0+X 2 0)+(266299921429/115225000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (309/5000 : ℝ)) (hi := (20007/100000 : ℝ)) (c := (359977107832130579/360078125000000000 : ℝ)) (alpha := (266299921429/115225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (359977107832130579/360078125000000000 : ℝ)*(X 0 1+X 2 1)+(266299921429/115225000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (309/5000 : ℝ)) (hi := (20007/100000 : ℝ)) (c := (359977107832130579/360078125000000000 : ℝ)) (alpha := (266299921429/115225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (359977107832130579/360078125000000000 : ℝ)*(X 0 2+X 1 2)+(266299921429/115225000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (309/5000 : ℝ)) (hi := (20007/100000 : ℝ)) (c := (359977107832130579/360078125000000000 : ℝ)) (alpha := (266299921429/115225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-526719859/2500000000 : ℝ)*X 0 0+(1098626357/2000000000 : ℝ)*X 0 1+(5053128/9765625 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5369766897/10000000000 : ℝ)*X 1 0+(-1135995103/5000000000 : ℝ)*X 1 1+(5174403067/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((268488337/500000000 : ℝ)*X 2 0+(1034880639/2000000000 : ℝ)*X 2 1+(-1135995123/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((868455841/2000000000 : ℝ)*X 0 0+(2015387303/5000000000 : ℝ)*X 0 1+(292318039/625000000 : ℝ)*X 0 2+(868455841/2000000000 : ℝ)*X 1 0+(2015387303/5000000000 : ℝ)*X 1 1+(292318039/625000000 : ℝ)*X 1 2+(868455841/2000000000 : ℝ)*X 2 0+(2015387303/5000000000 : ℝ)*X 2 1+(292318039/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-526739569/2500000000 : ℝ)*X 0 0+(1035290979/2000000000 : ℝ)*X 0 1+(686382587/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322095577/2500000000 : ℝ)*X 1 0+(-1955332363/10000000000 : ℝ)*X 1 1+(5491060739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322095619/2500000000 : ℝ)*X 2 0+(2745530409/5000000000 : ℝ)*X 2 1+(-977666011/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4342438537/10000000000 : ℝ)*X 0 0+(934585641/2000000000 : ℝ)*X 0 1+(806994757/2000000000 : ℝ)*X 0 2+(4342438537/10000000000 : ℝ)*X 1 0+(934585641/2000000000 : ℝ)*X 1 1+(806994757/2000000000 : ℝ)*X 1 2+(4342438537/10000000000 : ℝ)*X 2 0+(934585641/2000000000 : ℝ)*X 2 1+(806994757/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42574716548391211589127/5761250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1425141051/100000000000000 : ℝ)*(base19) + (617547469/50000000000000 : ℝ)*(base23) + (5279167/10000000000000 : ℝ)*(lower2) + (4560461/2000000000000 : ℝ)*(upper3) + (48996831/50000000000000 : ℝ)*(upper5) + (1171186739584051/50000000000000 : ℝ)*(major0) + (1171186739584051/50000000000000 : ℝ)*(major1) + (1171186739584051/50000000000000 : ℝ)*(major2) + (313748117309037/10000000000000 : ℝ)*(sp0) + (1568747107715403/50000000000000 : ℝ)*(sp1) + (1568747202738459/50000000000000 : ℝ)*(sp2) + (309448532419879/20000000000000 : ℝ)*(sp3) + (14467481487/100000000000000 : ℝ)*(sp4) + (4204668471/50000000000000 : ℝ)*(sp7) + (1547251071436337/100000000000000 : ℝ)*(f.failure) + (196093477535741/6250000000000 : ℝ)*(f.sum) + (166963973119333/23045000000000000000000000000 : ℝ)*base66 + (88773045747872741/72015625000000000000000000000000 : ℝ)*base67 + (214824636234837067/36007812500000000000000000000000 : ℝ)*base70 + (154372733966877259/72015625000000000000000000000000 : ℝ)*base72 + (2884123667737/5761250000000000000000000000 : ℝ)*base74 + (1693327248291851/4500976562500000000000000000000 : ℝ)*base75 + (115576356776908509/72015625000000000000000000000000 : ℝ)*base78 + (398324822715694183/36007812500000000000000000000000 : ℝ)*base79 + (46191247675229/11522500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (67737983/10000000000000000000000 : ℝ)*base89 + (67737983/10000000000000000000000 : ℝ)*base91 + (67737983/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85298337795684137749478631/36007812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (855837549/100000000000000 : ℝ)*(base19) + (236538687/20000000000000 : ℝ)*(base23) + (66926319/100000000000000 : ℝ)*(upper2) + (140303359/100000000000000 : ℝ)*(upper3) + (4359291/10000000000000 : ℝ)*(upper5) + (296630629277131/12500000000000 : ℝ)*(major0) + (296630629277131/12500000000000 : ℝ)*(major1) + (296630629277131/12500000000000 : ℝ)*(major2) + (1637455877/20000000000000 : ℝ)*(sp1) + (14641565291/100000000000000 : ℝ)*(sp2) + (635715774238359/20000000000000 : ℝ)*(sp4) + (3178569828074861/100000000000000 : ℝ)*(sp5) + (317856304693307/10000000000000 : ℝ)*(sp6) + (24492361223117/1562500000000 : ℝ)*(sp7) + (24492361223117/1562500000000 : ℝ)*(f.failure) + (635715774238359/20000000000000 : ℝ)*(f.sum) + (20149853026313/5761250000000000000000000000 : ℝ)*base66 + (532181623141681541/72015625000000000000000000000000 : ℝ)*base68 + (67092218973794177/9001953125000000000000000000000 : ℝ)*base70 + (29380125635681541/72015625000000000000000000000000 : ℝ)*base72 + (56935551328047/23045000000000000000000000000 : ℝ)*base74 + (164582360810692333/36007812500000000000000000000000 : ℝ)*base76 + (176719032230572729/18003906250000000000000000000000 : ℝ)*base78 + (934415497099806541/72015625000000000000000000000000 : ℝ)*base80 + (6055058644281/11522500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1112003/156250000000000000000 : ℝ)*base89 + (1112003/156250000000000000000 : ℝ)*base91 + (1112003/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1240_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (309/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9491/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4057/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1240_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1240_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9491/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4057/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1240_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1240_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1240_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9491/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4057/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1240_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
