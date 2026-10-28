-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1296_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:27:40.82453+00:00
-- url     : https://prove2.me/submissions/13aa8c75-8809-4370-99e0-132a3fb9edba

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
theorem support_rectangle_w1296_s0_0 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1836655403/10000000000 : ℝ)*x 0 + (300851109/500000000 : ℝ)*x 1 + (4799815971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1836655403/10000000000 : ℝ)^133 ≤ (5368072051489/50000000000000 : ℝ)^101 := by
    have hnat : (1836655403 : ℕ)^133*50000000000000^101 ≤ 5368072051489^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1836655403 10000000000 5368072051489 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300851109/500000000 : ℝ)^133 ≤ (51225088490667/100000000000000 : ℝ)^101 := by
    have hnat : (300851109 : ℕ)^133*100000000000000^101 ≤ 51225088490667^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300851109 500000000 51225088490667 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4799815971/10000000000 : ℝ)^133 ≤ (1901938369779/5000000000000 : ℝ)^101 := by
    have hnat : (4799815971 : ℕ)^133*5000000000000^101 ≤ 1901938369779^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4799815971 10000000000 1901938369779 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1836655403/10000000000 : ℝ), (300851109/500000000 : ℝ), (4799815971/10000000000 : ℝ)] ![(5368072051489/50000000000000 : ℝ), (51225088490667/100000000000000 : ℝ), (1901938369779/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1836655403/10000000000 : ℝ)|^133 ≤ (5368072051489/50000000000000 : ℝ)^101
        have hw : |(-1836655403/10000000000 : ℝ)|=(1836655403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(300851109/500000000 : ℝ)|^133 ≤ (51225088490667/100000000000000 : ℝ)^101
        have hw : |(300851109/500000000 : ℝ)|=(300851109/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4799815971/10000000000 : ℝ)|^133 ≤ (1901938369779/5000000000000 : ℝ)^101
        have hw : |(4799815971/10000000000 : ℝ)|=(4799815971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s0_1 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5506969603/10000000000 : ℝ)*x 0 + (-2530856879/10000000000 : ℝ)*x 1 + (4799815939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5506969603/10000000000 : ℝ)^133 ≤ (2849086433431/6250000000000 : ℝ)^101 := by
    have hnat : (5506969603 : ℕ)^133*6250000000000^101 ≤ 2849086433431^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506969603 10000000000 2849086433431 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2530856879/10000000000 : ℝ)^133 ≤ (16375849988101/100000000000000 : ℝ)^101 := by
    have hnat : (2530856879 : ℕ)^133*100000000000000^101 ≤ 16375849988101^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2530856879 10000000000 16375849988101 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4799815939/10000000000 : ℝ)^133 ≤ (38038767061629/100000000000000 : ℝ)^101 := by
    have hnat : (4799815939 : ℕ)^133*100000000000000^101 ≤ 38038767061629^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4799815939 10000000000 38038767061629 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5506969603/10000000000 : ℝ), (-2530856879/10000000000 : ℝ), (4799815939/10000000000 : ℝ)] ![(2849086433431/6250000000000 : ℝ), (16375849988101/100000000000000 : ℝ), (38038767061629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5506969603/10000000000 : ℝ)|^133 ≤ (2849086433431/6250000000000 : ℝ)^101
        have hw : |(5506969603/10000000000 : ℝ)|=(5506969603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2530856879/10000000000 : ℝ)|^133 ≤ (16375849988101/100000000000000 : ℝ)^101
        have hw : |(-2530856879/10000000000 : ℝ)|=(2530856879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4799815939/10000000000 : ℝ)|^133 ≤ (38038767061629/100000000000000 : ℝ)^101
        have hw : |(4799815939/10000000000 : ℝ)|=(4799815939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s0_2 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (344185599/625000000 : ℝ)*x 0 + (4799815979/10000000000 : ℝ)*x 1 + (-1265428427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344185599/625000000 : ℝ)^133 ≤ (11396345681947/25000000000000 : ℝ)^101 := by
    have hnat : (344185599 : ℕ)^133*25000000000000^101 ≤ 11396345681947^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344185599 625000000 11396345681947 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4799815979/10000000000 : ℝ)^133 ≤ (38038767479067/100000000000000 : ℝ)^101 := by
    have hnat : (4799815979 : ℕ)^133*100000000000000^101 ≤ 38038767479067^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4799815979 10000000000 38038767479067 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1265428427/5000000000 : ℝ)^133 ≤ (1023490610943/6250000000000 : ℝ)^101 := by
    have hnat : (1265428427 : ℕ)^133*6250000000000^101 ≤ 1023490610943^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1265428427 5000000000 1023490610943 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(344185599/625000000 : ℝ), (4799815979/10000000000 : ℝ), (-1265428427/5000000000 : ℝ)] ![(11396345681947/25000000000000 : ℝ), (38038767479067/100000000000000 : ℝ), (1023490610943/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(344185599/625000000 : ℝ)|^133 ≤ (11396345681947/25000000000000 : ℝ)^101
        have hw : |(344185599/625000000 : ℝ)|=(344185599/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4799815979/10000000000 : ℝ)|^133 ≤ (38038767479067/100000000000000 : ℝ)^101
        have hw : |(4799815979/10000000000 : ℝ)|=(4799815979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1265428427/5000000000 : ℝ)|^133 ≤ (1023490610943/6250000000000 : ℝ)^101
        have hw : |(-1265428427/5000000000 : ℝ)|=(1265428427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s0_3 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2092858599/5000000000 : ℝ)*x 0 + (3109175263/10000000000 : ℝ)*x 1 + (5614646557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092858599/5000000000 : ℝ)^133 ≤ (31763956877747/100000000000000 : ℝ)^101 := by
    have hnat : (2092858599 : ℕ)^133*100000000000000^101 ≤ 31763956877747^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092858599 5000000000 31763956877747 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3109175263/10000000000 : ℝ)^133 ≤ (21473316716089/100000000000000 : ℝ)^101 := by
    have hnat : (3109175263 : ℕ)^133*100000000000000^101 ≤ 21473316716089^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3109175263 10000000000 21473316716089 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5614646557/10000000000 : ℝ)^133 ≤ (23381363195307/50000000000000 : ℝ)^101 := by
    have hnat : (5614646557 : ℕ)^133*50000000000000^101 ≤ 23381363195307^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5614646557 10000000000 23381363195307 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2092858599/5000000000 : ℝ), (3109175263/10000000000 : ℝ), (5614646557/10000000000 : ℝ)] ![(31763956877747/100000000000000 : ℝ), (21473316716089/100000000000000 : ℝ), (23381363195307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2092858599/5000000000 : ℝ)|^133 ≤ (31763956877747/100000000000000 : ℝ)^101
        have hw : |(2092858599/5000000000 : ℝ)|=(2092858599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3109175263/10000000000 : ℝ)|^133 ≤ (21473316716089/100000000000000 : ℝ)^101
        have hw : |(3109175263/10000000000 : ℝ)|=(3109175263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5614646557/10000000000 : ℝ)|^133 ≤ (23381363195307/50000000000000 : ℝ)^101
        have hw : |(5614646557/10000000000 : ℝ)|=(5614646557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s0_4 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-460339199/2500000000 : ℝ)*x 0 + (4831225651/10000000000 : ℝ)*x 1 + (1196899101/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (460339199/2500000000 : ℝ)^133 ≤ (10772347843683/100000000000000 : ℝ)^101 := by
    have hnat : (460339199 : ℕ)^133*100000000000000^101 ≤ 10772347843683^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460339199 2500000000 10772347843683 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4831225651/10000000000 : ℝ)^133 ≤ (7673379328773/20000000000000 : ℝ)^101 := by
    have hnat : (4831225651 : ℕ)^133*20000000000000^101 ≤ 7673379328773^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4831225651 10000000000 7673379328773 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1196899101/2000000000 : ℝ)^133 ≤ (50860755489613/100000000000000 : ℝ)^101 := by
    have hnat : (1196899101 : ℕ)^133*100000000000000^101 ≤ 50860755489613^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196899101 2000000000 50860755489613 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-460339199/2500000000 : ℝ), (4831225651/10000000000 : ℝ), (1196899101/2000000000 : ℝ)] ![(10772347843683/100000000000000 : ℝ), (7673379328773/20000000000000 : ℝ), (50860755489613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-460339199/2500000000 : ℝ)|^133 ≤ (10772347843683/100000000000000 : ℝ)^101
        have hw : |(-460339199/2500000000 : ℝ)|=(460339199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4831225651/10000000000 : ℝ)|^133 ≤ (7673379328773/20000000000000 : ℝ)^101
        have hw : |(4831225651/10000000000 : ℝ)|=(4831225651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1196899101/2000000000 : ℝ)|^133 ≤ (50860755489613/100000000000000 : ℝ)^101
        have hw : |(1196899101/2000000000 : ℝ)|=(1196899101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s0_5 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5175563619/10000000000 : ℝ)*x 0 + (-1346174639/10000000000 : ℝ)*x 1 + (2992249079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5175563619/10000000000 : ℝ)^133 ≤ (42007842077529/100000000000000 : ℝ)^101 := by
    have hnat : (5175563619 : ℕ)^133*100000000000000^101 ≤ 42007842077529^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175563619 10000000000 42007842077529 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346174639/10000000000 : ℝ)^133 ≤ (3565686370149/50000000000000 : ℝ)^101 := by
    have hnat : (1346174639 : ℕ)^133*50000000000000^101 ≤ 3565686370149^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346174639 10000000000 3565686370149 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2992249079/5000000000 : ℝ)^133 ≤ (2034431407219/4000000000000 : ℝ)^101 := by
    have hnat : (2992249079 : ℕ)^133*4000000000000^101 ≤ 2034431407219^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2992249079 5000000000 2034431407219 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5175563619/10000000000 : ℝ), (-1346174639/10000000000 : ℝ), (2992249079/5000000000 : ℝ)] ![(42007842077529/100000000000000 : ℝ), (3565686370149/50000000000000 : ℝ), (2034431407219/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5175563619/10000000000 : ℝ)|^133 ≤ (42007842077529/100000000000000 : ℝ)^101
        have hw : |(5175563619/10000000000 : ℝ)|=(5175563619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1346174639/10000000000 : ℝ)|^133 ≤ (3565686370149/50000000000000 : ℝ)^101
        have hw : |(-1346174639/10000000000 : ℝ)|=(1346174639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2992249079/5000000000 : ℝ)|^133 ≤ (2034431407219/4000000000000 : ℝ)^101
        have hw : |(2992249079/5000000000 : ℝ)|=(2992249079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s0_6 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5175564929/10000000000 : ℝ)*x 0 + (2992247937/5000000000 : ℝ)*x 1 + (-1346176293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5175564929/10000000000 : ℝ)^133 ≤ (42007856079021/100000000000000 : ℝ)^101 := by
    have hnat : (5175564929 : ℕ)^133*100000000000000^101 ≤ 42007856079021^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175564929 10000000000 42007856079021 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2992247937/5000000000 : ℝ)^133 ≤ (203443038477/400000000000 : ℝ)^101 := by
    have hnat : (2992247937 : ℕ)^133*400000000000^101 ≤ 203443038477^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2992247937 5000000000 203443038477 400000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346176293/10000000000 : ℝ)^133 ≤ (3565692139243/50000000000000 : ℝ)^101 := by
    have hnat : (1346176293 : ℕ)^133*50000000000000^101 ≤ 3565692139243^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346176293 10000000000 3565692139243 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5175564929/10000000000 : ℝ), (2992247937/5000000000 : ℝ), (-1346176293/10000000000 : ℝ)] ![(42007856079021/100000000000000 : ℝ), (203443038477/400000000000 : ℝ), (3565692139243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5175564929/10000000000 : ℝ)|^133 ≤ (42007856079021/100000000000000 : ℝ)^101
        have hw : |(5175564929/10000000000 : ℝ)|=(5175564929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2992247937/5000000000 : ℝ)|^133 ≤ (203443038477/400000000000 : ℝ)^101
        have hw : |(2992247937/5000000000 : ℝ)|=(2992247937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1346176293/10000000000 : ℝ)|^133 ≤ (3565692139243/50000000000000 : ℝ)^101
        have hw : |(-1346176293/10000000000 : ℝ)|=(1346176293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s0_7 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4195400207/10000000000 : ℝ)*x 0 + (693750173/1250000000 : ℝ)*x 1 + (3176119871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4195400207/10000000000 : ℝ)^133 ≤ (31860754426851/100000000000000 : ℝ)^101 := by
    have hnat : (4195400207 : ℕ)^133*100000000000000^101 ≤ 31860754426851^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4195400207 10000000000 31860754426851 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (693750173/1250000000 : ℝ)^133 ≤ (46055026992849/100000000000000 : ℝ)^101 := by
    have hnat : (693750173 : ℕ)^133*100000000000000^101 ≤ 46055026992849^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693750173 1250000000 46055026992849 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3176119871/10000000000 : ℝ)^133 ≤ (22084218561027/100000000000000 : ℝ)^101 := by
    have hnat : (3176119871 : ℕ)^133*100000000000000^101 ≤ 22084218561027^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3176119871 10000000000 22084218561027 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4195400207/10000000000 : ℝ), (693750173/1250000000 : ℝ), (3176119871/10000000000 : ℝ)] ![(31860754426851/100000000000000 : ℝ), (46055026992849/100000000000000 : ℝ), (22084218561027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4195400207/10000000000 : ℝ)|^133 ≤ (31860754426851/100000000000000 : ℝ)^101
        have hw : |(4195400207/10000000000 : ℝ)|=(4195400207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(693750173/1250000000 : ℝ)|^133 ≤ (46055026992849/100000000000000 : ℝ)^101
        have hw : |(693750173/1250000000 : ℝ)|=(693750173/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3176119871/10000000000 : ℝ)|^133 ≤ (22084218561027/100000000000000 : ℝ)^101
        have hw : |(3176119871/10000000000 : ℝ)|=(3176119871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1296_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1063/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13603/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4255/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4255 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4255*1^1024 ≤ 0^1024*1^4255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4255/1024 : ℝ) ≤ (1110249168482970831/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4255 ≤ (1110249168482970831/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4255*50000000000000000000^1024 ≤ 1110249168482970831^1024*5^4255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1110249168482970831 50000000000000000000 4255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1110249168482970831/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4255 := by
      have hnat : (1 : ℕ)^1024*1^4255 ≤ 1^4255*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (51110249168482970831/50000000000000000000 : ℝ) ≤ (5026496671825899/5000000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (51110249168482970831/50000000000000000000 : ℝ)^1024 ≤ (5026496671825899/5000000000000000 : ℝ)^4255 := by
      have hnat : (51110249168482970831 : ℕ)^1024*5000000000000000^4255 ≤ 5026496671825899^4255*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51110249168482970831 50000000000000000000 5026496671825899 5000000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5026496671825899/5000000000000000 : ℝ)) (X := (51110249168482970831/50000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (26110249168482970831/25000000000000000000 : ℝ) ≤ (2526496671825899/2500000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (26110249168482970831/25000000000000000000 : ℝ)^1024 ≤ (2526496671825899/2500000000000000 : ℝ)^4255 := by
      have hnat : (26110249168482970831 : ℕ)^1024*2500000000000000^4255 ≤ 2526496671825899^4255*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26110249168482970831 25000000000000000000 2526496671825899 2500000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2526496671825899/2500000000000000 : ℝ)) (X := (26110249168482970831/25000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(26496671825899/2000000000000000 : ℝ)*(0 : ℝ))^(4255/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(26496671825899/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1110249168482970831/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(26496671825899/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4255/1024 : ℝ) := by
    rw [show (1 : ℝ)+(26496671825899/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5026496671825899/5000000000000000 : ℝ) by norm_num, show 1+(1110249168482970831/50000000000000000000 : ℝ)+(0 : ℝ)=(51110249168482970831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1110249168482970831/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(26496671825899/2000000000000000 : ℝ)*(2/5 : ℝ))^(4255/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(26496671825899/2000000000000000 : ℝ)*(2/5 : ℝ)=(2526496671825899/2500000000000000 : ℝ) by norm_num, show 1+2*(1110249168482970831/50000000000000000000 : ℝ)=(26110249168482970831/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(26496671825899/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26496671825899/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(26496671825899/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26496671825899/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(26496671825899/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26496671825899/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1836655403/10000000000 : ℝ)*X 0 0+(300851109/500000000 : ℝ)*X 0 1+(4799815971/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5506969603/10000000000 : ℝ)*X 1 0+(-2530856879/10000000000 : ℝ)*X 1 1+(4799815939/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((344185599/625000000 : ℝ)*X 2 0+(4799815979/10000000000 : ℝ)*X 2 1+(-1265428427/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2092858599/5000000000 : ℝ)*X 0 0+(3109175263/10000000000 : ℝ)*X 0 1+(5614646557/10000000000 : ℝ)*X 0 2+(2092858599/5000000000 : ℝ)*X 1 0+(3109175263/10000000000 : ℝ)*X 1 1+(5614646557/10000000000 : ℝ)*X 1 2+(2092858599/5000000000 : ℝ)*X 2 0+(3109175263/10000000000 : ℝ)*X 2 1+(5614646557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-460339199/2500000000 : ℝ)*X 0 0+(4831225651/10000000000 : ℝ)*X 0 1+(1196899101/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5175563619/10000000000 : ℝ)*X 1 0+(-1346174639/10000000000 : ℝ)*X 1 1+(2992249079/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5175564929/10000000000 : ℝ)*X 2 0+(2992247937/5000000000 : ℝ)*X 2 1+(-1346176293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4195400207/10000000000 : ℝ)*X 0 0+(693750173/1250000000 : ℝ)*X 0 1+(3176119871/10000000000 : ℝ)*X 0 2+(4195400207/10000000000 : ℝ)*X 1 0+(693750173/1250000000 : ℝ)*X 1 1+(3176119871/10000000000 : ℝ)*X 1 2+(4195400207/10000000000 : ℝ)*X 2 0+(693750173/1250000000 : ℝ)*X 2 1+(3176119871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (709292467404630662800167/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41312731/50000000000000 : ℝ)*(base1) + (53680491/3125000000000 : ℝ)*(base19) + (1714941179/100000000000000 : ℝ)*(base23) + (19860107/10000000000000 : ℝ)*(upper3) + (101924507/50000000000000 : ℝ)*(upper5) + (610348031601511/100000000000000 : ℝ)*(major0) + (610348031601511/100000000000000 : ℝ)*(major1) + (610348031601511/100000000000000 : ℝ)*(major2) + (821558671934463/100000000000000 : ℝ)*(sp0) + (410781189195707/50000000000000 : ℝ)*(sp1) + (410781190612973/50000000000000 : ℝ)*(sp2) + (399129014961223/100000000000000 : ℝ)*(sp3) + (1376714531/25000000000000 : ℝ)*(sp4) + (1316509191/50000000000000 : ℝ)*(sp7) + (399131730605067/100000000000000 : ℝ)*(f.failure) + (410782048083563/50000000000000 : ℝ)*(f.sum) + (143553856166611/100000000000000000000000000000 : ℝ)*base66 + (1045582457133389/200000000000000000000000000000 : ℝ)*base67 + (272452287866611/200000000000000000000000000000 : ℝ)*base70 + (576179836666611/200000000000000000000000000000 : ℝ)*base72 + (211338494233389/100000000000000000000000000000 : ℝ)*base73 + (947353598466611/200000000000000000000000000000 : ℝ)*base76 + (159932598933389/200000000000000000000000000000 : ℝ)*base77 + (494329843133389/200000000000000000000000000000 : ℝ)*base79 + (293697867566611/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (8541137/2000000000000000000000 : ℝ)*base90 + (8541137/2000000000000000000000 : ℝ)*base92 + (8541137/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61998628160625470988951/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (475455111/100000000000000 : ℝ)*(base1) + (1112093403/100000000000000 : ℝ)*(base19) + (259595203/20000000000000 : ℝ)*(base23) + (195844271/100000000000000 : ℝ)*(upper3) + (322087831213383/50000000000000 : ℝ)*(major0) + (322087831213383/50000000000000 : ℝ)*(major1) + (322087831213383/50000000000000 : ℝ)*(major2) + (165632831/10000000000000 : ℝ)*(sp1) + (1131751079/100000000000000 : ℝ)*(sp2) + (453735153/100000000000000 : ℝ)*(sp3) + (173419716238327/20000000000000 : ℝ)*(sp4) + (86709533731481/10000000000000 : ℝ)*(sp5) + (86709567600943/10000000000000 : ℝ)*(sp6) + (84250416652929/20000000000000 : ℝ)*(sp7) + (421253012454909/100000000000000 : ℝ)*(f.failure) + (867098105736523/100000000000000 : ℝ)*(f.sum) + (3762772643683/50000000000000000000000000000 : ℝ)*base66 + (22942535593683/100000000000000000000000000000 : ℝ)*base68 + (174008674293683/100000000000000000000000000000 : ℝ)*base70 + (8370818093683/100000000000000000000000000000 : ℝ)*base72 + (33257747143683/50000000000000000000000000000 : ℝ)*base74 + (379496086206317/100000000000000000000000000000 : ℝ)*base75 + (183291146693683/100000000000000000000000000000 : ℝ)*base78 + (492557913193683/100000000000000000000000000000 : ℝ)*base80 + (7045233193683/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (11129799/2000000000000000000000 : ℝ)*base90 + (11129799/2000000000000000000000 : ℝ)*base92 + (11129799/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1296_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1063/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13603/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1296_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1296_s1_0 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1014060051/5000000000 : ℝ)*x 0 + (2831704197/5000000000 : ℝ)*x 1 + (5030849631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1014060051/5000000000 : ℝ)^133 ≤ (6116866399777/50000000000000 : ℝ)^101 := by
    have hnat : (1014060051 : ℕ)^133*50000000000000^101 ≤ 6116866399777^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014060051 5000000000 6116866399777 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2831704197/5000000000 : ℝ)^133 ≤ (47298256192431/100000000000000 : ℝ)^101 := by
    have hnat : (2831704197 : ℕ)^133*100000000000000^101 ≤ 47298256192431^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2831704197 5000000000 47298256192431 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5030849631/10000000000 : ℝ)^133 ≤ (8093602197761/20000000000000 : ℝ)^101 := by
    have hnat : (5030849631 : ℕ)^133*20000000000000^101 ≤ 8093602197761^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5030849631 10000000000 8093602197761 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1014060051/5000000000 : ℝ), (2831704197/5000000000 : ℝ), (5030849631/10000000000 : ℝ)] ![(6116866399777/50000000000000 : ℝ), (47298256192431/100000000000000 : ℝ), (8093602197761/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1014060051/5000000000 : ℝ)|^133 ≤ (6116866399777/50000000000000 : ℝ)^101
        have hw : |(-1014060051/5000000000 : ℝ)|=(1014060051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2831704197/5000000000 : ℝ)|^133 ≤ (47298256192431/100000000000000 : ℝ)^101
        have hw : |(2831704197/5000000000 : ℝ)|=(2831704197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5030849631/10000000000 : ℝ)|^133 ≤ (8093602197761/20000000000000 : ℝ)^101
        have hw : |(5030849631/10000000000 : ℝ)|=(5030849631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s1_1 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (676320217/1250000000 : ℝ)*x 0 + (-473407811/2000000000 : ℝ)*x 1 + (5030849721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676320217/1250000000 : ℝ)^133 ≤ (44537422920071/100000000000000 : ℝ)^101 := by
    have hnat : (676320217 : ℕ)^133*100000000000000^101 ≤ 44537422920071^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676320217 1250000000 44537422920071 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (473407811/2000000000 : ℝ)^133 ≤ (93716032009/625000000000 : ℝ)^101 := by
    have hnat : (473407811 : ℕ)^133*625000000000^101 ≤ 93716032009^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473407811 2000000000 93716032009 625000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5030849721/10000000000 : ℝ)^133 ≤ (8093602388427/20000000000000 : ℝ)^101 := by
    have hnat : (5030849721 : ℕ)^133*20000000000000^101 ≤ 8093602388427^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5030849721 10000000000 8093602388427 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676320217/1250000000 : ℝ), (-473407811/2000000000 : ℝ), (5030849721/10000000000 : ℝ)] ![(44537422920071/100000000000000 : ℝ), (93716032009/625000000000 : ℝ), (8093602388427/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676320217/1250000000 : ℝ)|^133 ≤ (44537422920071/100000000000000 : ℝ)^101
        have hw : |(676320217/1250000000 : ℝ)|=(676320217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-473407811/2000000000 : ℝ)|^133 ≤ (93716032009/625000000000 : ℝ)^101
        have hw : |(-473407811/2000000000 : ℝ)|=(473407811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5030849721/10000000000 : ℝ)|^133 ≤ (8093602388427/20000000000000 : ℝ)^101
        have hw : |(5030849721/10000000000 : ℝ)|=(5030849721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s1_2 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (270528087/500000000 : ℝ)*x 0 + (503084959/1000000000 : ℝ)*x 1 + (-147939951/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270528087/500000000 : ℝ)^133 ≤ (4453742296343/10000000000000 : ℝ)^101 := by
    have hnat : (270528087 : ℕ)^133*10000000000000^101 ≤ 4453742296343^101*500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270528087 500000000 4453742296343 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503084959/1000000000 : ℝ)^133 ≤ (4046801055451/10000000000000 : ℝ)^101 := by
    have hnat : (503084959 : ℕ)^133*10000000000000^101 ≤ 4046801055451^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503084959 1000000000 4046801055451 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147939951/625000000 : ℝ)^133 ≤ (7497283232233/50000000000000 : ℝ)^101 := by
    have hnat : (147939951 : ℕ)^133*50000000000000^101 ≤ 7497283232233^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147939951 625000000 7497283232233 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270528087/500000000 : ℝ), (503084959/1000000000 : ℝ), (-147939951/625000000 : ℝ)] ![(4453742296343/10000000000000 : ℝ), (4046801055451/10000000000000 : ℝ), (7497283232233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270528087/500000000 : ℝ)|^133 ≤ (4453742296343/10000000000000 : ℝ)^101
        have hw : |(270528087/500000000 : ℝ)|=(270528087/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(503084959/1000000000 : ℝ)|^133 ≤ (4046801055451/10000000000000 : ℝ)^101
        have hw : |(503084959/1000000000 : ℝ)|=(503084959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-147939951/625000000 : ℝ)|^133 ≤ (7497283232233/50000000000000 : ℝ)^101
        have hw : |(-147939951/625000000 : ℝ)|=(147939951/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s1_3 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (860087651/2000000000 : ℝ)*x 0 + (3696016653/10000000000 : ℝ)*x 1 + (499806179/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860087651/2000000000 : ℝ)^133 ≤ (32915308783601/100000000000000 : ℝ)^101 := by
    have hnat : (860087651 : ℕ)^133*100000000000000^101 ≤ 32915308783601^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860087651 2000000000 32915308783601 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3696016653/10000000000 : ℝ)^133 ≤ (26963628161389/100000000000000 : ℝ)^101 := by
    have hnat : (3696016653 : ℕ)^133*100000000000000^101 ≤ 26963628161389^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3696016653 10000000000 26963628161389 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (499806179/1000000000 : ℝ)^133 ≤ (10030265760443/25000000000000 : ℝ)^101 := by
    have hnat : (499806179 : ℕ)^133*25000000000000^101 ≤ 10030265760443^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499806179 1000000000 10030265760443 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860087651/2000000000 : ℝ), (3696016653/10000000000 : ℝ), (499806179/1000000000 : ℝ)] ![(32915308783601/100000000000000 : ℝ), (26963628161389/100000000000000 : ℝ), (10030265760443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860087651/2000000000 : ℝ)|^133 ≤ (32915308783601/100000000000000 : ℝ)^101
        have hw : |(860087651/2000000000 : ℝ)|=(860087651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3696016653/10000000000 : ℝ)|^133 ≤ (26963628161389/100000000000000 : ℝ)^101
        have hw : |(3696016653/10000000000 : ℝ)|=(3696016653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(499806179/1000000000 : ℝ)|^133 ≤ (10030265760443/25000000000000 : ℝ)^101
        have hw : |(499806179/1000000000 : ℝ)|=(499806179/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s1_4 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2028748549/10000000000 : ℝ)*x 0 + (2519535939/5000000000 : ℝ)*x 1 + (226201241/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2028748549/10000000000 : ℝ)^133 ≤ (12238724925829/100000000000000 : ℝ)^101 := by
    have hnat : (2028748549 : ℕ)^133*100000000000000^101 ≤ 12238724925829^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028748549 10000000000 12238724925829 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2519535939/5000000000 : ℝ)^133 ≤ (40555128146043/100000000000000 : ℝ)^101 := by
    have hnat : (2519535939 : ℕ)^133*100000000000000^101 ≤ 40555128146043^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2519535939 5000000000 40555128146043 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226201241/400000000 : ℝ)^133 ≤ (47206146921003/100000000000000 : ℝ)^101 := by
    have hnat : (226201241 : ℕ)^133*100000000000000^101 ≤ 47206146921003^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226201241 400000000 47206146921003 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2028748549/10000000000 : ℝ), (2519535939/5000000000 : ℝ), (226201241/400000000 : ℝ)] ![(12238724925829/100000000000000 : ℝ), (40555128146043/100000000000000 : ℝ), (47206146921003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2028748549/10000000000 : ℝ)|^133 ≤ (12238724925829/100000000000000 : ℝ)^101
        have hw : |(-2028748549/10000000000 : ℝ)|=(2028748549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2519535939/5000000000 : ℝ)|^133 ≤ (40555128146043/100000000000000 : ℝ)^101
        have hw : |(2519535939/5000000000 : ℝ)|=(2519535939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226201241/400000000 : ℝ)|^133 ≤ (47206146921003/100000000000000 : ℝ)^101
        have hw : |(226201241/400000000 : ℝ)|=(226201241/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s1_5 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5247072087/10000000000 : ℝ)*x 0 + (-348571451/2000000000 : ℝ)*x 1 + (1413757933/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5247072087/10000000000 : ℝ)^133 ≤ (21386901861459/50000000000000 : ℝ)^101 := by
    have hnat : (5247072087 : ℕ)^133*50000000000000^101 ≤ 21386901861459^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247072087 10000000000 21386901861459 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (348571451/2000000000 : ℝ)^133 ≤ (10020041575151/100000000000000 : ℝ)^101 := by
    have hnat : (348571451 : ℕ)^133*100000000000000^101 ≤ 10020041575151^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348571451 2000000000 10020041575151 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1413757933/2500000000 : ℝ)^133 ≤ (47206154692653/100000000000000 : ℝ)^101 := by
    have hnat : (1413757933 : ℕ)^133*100000000000000^101 ≤ 47206154692653^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1413757933 2500000000 47206154692653 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5247072087/10000000000 : ℝ), (-348571451/2000000000 : ℝ), (1413757933/2500000000 : ℝ)] ![(21386901861459/50000000000000 : ℝ), (10020041575151/100000000000000 : ℝ), (47206154692653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5247072087/10000000000 : ℝ)|^133 ≤ (21386901861459/50000000000000 : ℝ)^101
        have hw : |(5247072087/10000000000 : ℝ)|=(5247072087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-348571451/2000000000 : ℝ)|^133 ≤ (10020041575151/100000000000000 : ℝ)^101
        have hw : |(-348571451/2000000000 : ℝ)|=(348571451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1413757933/2500000000 : ℝ)|^133 ≤ (47206154692653/100000000000000 : ℝ)^101
        have hw : |(1413757933/2500000000 : ℝ)|=(1413757933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s1_6 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5247071999/10000000000 : ℝ)*x 0 + (2827515663/5000000000 : ℝ)*x 1 + (-1742857969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5247071999/10000000000 : ℝ)^133 ≤ (21386901389131/50000000000000 : ℝ)^101 := by
    have hnat : (5247071999 : ℕ)^133*50000000000000^101 ≤ 21386901389131^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247071999 10000000000 21386901389131 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2827515663/5000000000 : ℝ)^133 ≤ (1888246009189/4000000000000 : ℝ)^101 := by
    have hnat : (2827515663 : ℕ)^133*4000000000000^101 ≤ 1888246009189^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2827515663 5000000000 1888246009189 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1742857969/10000000000 : ℝ)^133 ≤ (2004009396131/20000000000000 : ℝ)^101 := by
    have hnat : (1742857969 : ℕ)^133*20000000000000^101 ≤ 2004009396131^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742857969 10000000000 2004009396131 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5247071999/10000000000 : ℝ), (2827515663/5000000000 : ℝ), (-1742857969/10000000000 : ℝ)] ![(21386901389131/50000000000000 : ℝ), (1888246009189/4000000000000 : ℝ), (2004009396131/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5247071999/10000000000 : ℝ)|^133 ≤ (21386901389131/50000000000000 : ℝ)^101
        have hw : |(5247071999/10000000000 : ℝ)|=(5247071999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2827515663/5000000000 : ℝ)|^133 ≤ (1888246009189/4000000000000 : ℝ)^101
        have hw : |(2827515663/5000000000 : ℝ)|=(2827515663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1742857969/10000000000 : ℝ)|^133 ≤ (2004009396131/20000000000000 : ℝ)^101
        have hw : |(-1742857969/10000000000 : ℝ)|=(1742857969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s1_7 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4301731053/10000000000 : ℝ)*x 0 + (622642231/1250000000 : ℝ)*x 1 + (3713259581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301731053/10000000000 : ℝ)^133 ≤ (16464169728149/50000000000000 : ℝ)^101 := by
    have hnat : (4301731053 : ℕ)^133*50000000000000^101 ≤ 16464169728149^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301731053 10000000000 16464169728149 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (622642231/1250000000 : ℝ)^133 ≤ (39942262264343/100000000000000 : ℝ)^101 := by
    have hnat : (622642231 : ℕ)^133*100000000000000^101 ≤ 39942262264343^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622642231 1250000000 39942262264343 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3713259581/10000000000 : ℝ)^133 ≤ (13564699130823/50000000000000 : ℝ)^101 := by
    have hnat : (3713259581 : ℕ)^133*50000000000000^101 ≤ 13564699130823^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3713259581 10000000000 13564699130823 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301731053/10000000000 : ℝ), (622642231/1250000000 : ℝ), (3713259581/10000000000 : ℝ)] ![(16464169728149/50000000000000 : ℝ), (39942262264343/100000000000000 : ℝ), (13564699130823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301731053/10000000000 : ℝ)|^133 ≤ (16464169728149/50000000000000 : ℝ)^101
        have hw : |(4301731053/10000000000 : ℝ)|=(4301731053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(622642231/1250000000 : ℝ)|^133 ≤ (39942262264343/100000000000000 : ℝ)^101
        have hw : |(622642231/1250000000 : ℝ)|=(622642231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3713259581/10000000000 : ℝ)|^133 ≤ (13564699130823/50000000000000 : ℝ)^101
        have hw : |(3713259581/10000000000 : ℝ)|=(3713259581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1296_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13603/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1063/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (403/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9909/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13603/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1063/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13603/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1063/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13603/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1063/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13603/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1063/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13603/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1063/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13603/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1063/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1063/100000 : ℝ) ^ (4255/1024 : ℝ) ≤ (126106098603/20000000000000000000 : ℝ) := by
    have hpowers : (1063/100000 : ℝ)^4255 ≤ (126106098603/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1063 : ℕ)^4255*20000000000000000000^1024 ≤ 126106098603^1024*100000^4255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1063 100000 126106098603 20000000000000000000 4255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1063/100000 : ℝ)) (X := (126106098603/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13603/50000 : ℝ) ^ (4255/1024 : ℝ) ≤ (44758674691395393/10000000000000000000 : ℝ) := by
    have hpowers : (13603/50000 : ℝ)^4255 ≤ (44758674691395393/10000000000000000000 : ℝ)^1024 := by
      have hnat : (13603 : ℕ)^4255*10000000000000000000^1024 ≤ 44758674691395393^1024*50000^4255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13603 50000 44758674691395393 10000000000000000000 4255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13603/50000 : ℝ)) (X := (44758674691395393/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000126106098603/10000000000000000000 : ℝ) ≤ (312500000948389/312500000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (10000000126106098603/10000000000000000000 : ℝ)^1024 ≤ (312500000948389/312500000000000 : ℝ)^4255 := by
      have hnat : (10000000126106098603 : ℕ)^1024*312500000000000^4255 ≤ 312500000948389^4255*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000126106098603 10000000000000000000 312500000948389 312500000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312500000948389/312500000000000 : ℝ)) (X := (10000000126106098603/10000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20089517475488889389/20000000000000000000 : ℝ) ≤ (5005376646840747/5000000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (20089517475488889389/20000000000000000000 : ℝ)^1024 ≤ (5005376646840747/5000000000000000 : ℝ)^4255 := by
      have hnat : (20089517475488889389 : ℕ)^1024*5000000000000000^4255 ≤ 5005376646840747^4255*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20089517475488889389 20000000000000000000 5005376646840747 5000000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005376646840747/5000000000000000 : ℝ)) (X := (20089517475488889389/20000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5044758674691395393/5000000000000000000 : ℝ) ≤ (501075327850727/500000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (5044758674691395393/5000000000000000000 : ℝ)^1024 ≤ (501075327850727/500000000000000 : ℝ)^4255 := by
      have hnat : (5044758674691395393 : ℕ)^1024*500000000000000^4255 ≤ 501075327850727^4255*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5044758674691395393 5000000000000000000 501075327850727 500000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (501075327850727/500000000000000 : ℝ)) (X := (5044758674691395393/5000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(126106098603/20000000000000000000 : ℝ) ≤ ((5027060372222181159/5027500000000000000 : ℝ)+2*(413587051271/100550000000000 : ℝ)*(1063/100000 : ℝ))^(4255/1024 : ℝ) := by
    rw [show (5027060372222181159/5027500000000000000 : ℝ)+2*(413587051271/100550000000000 : ℝ)*(1063/100000 : ℝ)=(312500000948389/312500000000000 : ℝ) by norm_num, show 1+2*(126106098603/20000000000000000000 : ℝ)=(10000000126106098603/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(44758674691395393/10000000000000000000 : ℝ)+(126106098603/20000000000000000000 : ℝ) ≤ ((5027060372222181159/5027500000000000000 : ℝ)+(413587051271/100550000000000 : ℝ)*((13603/50000 : ℝ)+(1063/100000 : ℝ)))^(4255/1024 : ℝ) := by
    rw [show (5027060372222181159/5027500000000000000 : ℝ)+(413587051271/100550000000000 : ℝ)*((13603/50000 : ℝ)+(1063/100000 : ℝ))=(5005376646840747/5000000000000000 : ℝ) by norm_num, show 1+(44758674691395393/10000000000000000000 : ℝ)+(126106098603/20000000000000000000 : ℝ)=(20089517475488889389/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(44758674691395393/10000000000000000000 : ℝ) ≤ ((5027060372222181159/5027500000000000000 : ℝ)+2*(413587051271/100550000000000 : ℝ)*(13603/50000 : ℝ))^(4255/1024 : ℝ) := by
    rw [show (5027060372222181159/5027500000000000000 : ℝ)+2*(413587051271/100550000000000 : ℝ)*(13603/50000 : ℝ)=(501075327850727/500000000000000 : ℝ) by norm_num, show 1+2*(44758674691395393/10000000000000000000 : ℝ)=(5044758674691395393/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5027060372222181159/5027500000000000000 : ℝ)*(X 1 0+X 2 0)+(413587051271/100550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (1063/100000 : ℝ)) (hi := (13603/50000 : ℝ)) (c := (5027060372222181159/5027500000000000000 : ℝ)) (alpha := (413587051271/100550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5027060372222181159/5027500000000000000 : ℝ)*(X 0 1+X 2 1)+(413587051271/100550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (1063/100000 : ℝ)) (hi := (13603/50000 : ℝ)) (c := (5027060372222181159/5027500000000000000 : ℝ)) (alpha := (413587051271/100550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5027060372222181159/5027500000000000000 : ℝ)*(X 0 2+X 1 2)+(413587051271/100550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (1063/100000 : ℝ)) (hi := (13603/50000 : ℝ)) (c := (5027060372222181159/5027500000000000000 : ℝ)) (alpha := (413587051271/100550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1014060051/5000000000 : ℝ)*X 0 0+(2831704197/5000000000 : ℝ)*X 0 1+(5030849631/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((676320217/1250000000 : ℝ)*X 1 0+(-473407811/2000000000 : ℝ)*X 1 1+(5030849721/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((270528087/500000000 : ℝ)*X 2 0+(503084959/1000000000 : ℝ)*X 2 1+(-147939951/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((860087651/2000000000 : ℝ)*X 0 0+(3696016653/10000000000 : ℝ)*X 0 1+(499806179/1000000000 : ℝ)*X 0 2+(860087651/2000000000 : ℝ)*X 1 0+(3696016653/10000000000 : ℝ)*X 1 1+(499806179/1000000000 : ℝ)*X 1 2+(860087651/2000000000 : ℝ)*X 2 0+(3696016653/10000000000 : ℝ)*X 2 1+(499806179/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2028748549/10000000000 : ℝ)*X 0 0+(2519535939/5000000000 : ℝ)*X 0 1+(226201241/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5247072087/10000000000 : ℝ)*X 1 0+(-348571451/2000000000 : ℝ)*X 1 1+(1413757933/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5247071999/10000000000 : ℝ)*X 2 0+(2827515663/5000000000 : ℝ)*X 2 1+(-1742857969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4301731053/10000000000 : ℝ)*X 0 0+(622642231/1250000000 : ℝ)*X 0 1+(3713259581/10000000000 : ℝ)*X 0 2+(4301731053/10000000000 : ℝ)*X 1 0+(622642231/1250000000 : ℝ)*X 1 1+(3713259581/10000000000 : ℝ)*X 1 2+(4301731053/10000000000 : ℝ)*X 2 0+(622642231/1250000000 : ℝ)*X 2 1+(3713259581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (389622118077623956524299601/50275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18646067/25000000000000 : ℝ)*(base1) + (744975893/50000000000000 : ℝ)*(base19) + (745560267/50000000000000 : ℝ)*(base23) + (24995473/12500000000000 : ℝ)*(upper3) + (137726849/100000000000000 : ℝ)*(upper5) + (234892860357213/20000000000000 : ℝ)*(major0) + (234892860357213/20000000000000 : ℝ)*(major1) + (234892860357213/20000000000000 : ℝ)*(major2) + (790444763923887/50000000000000 : ℝ)*(sp0) + (790448124053483/50000000000000 : ℝ)*(sp1) + (790448123469109/50000000000000 : ℝ)*(sp2) + (384013166889459/50000000000000 : ℝ)*(sp3) + (1656959049/20000000000000 : ℝ)*(sp4) + (2099411453/50000000000000 : ℝ)*(sp7) + (768030607186091/100000000000000 : ℝ)*(f.failure) + (1543845447323/97656250000 : ℝ)*(f.sum) + (9258830436759/2011000000000000000000000000 : ℝ)*base66 + (193058712780099867/100550000000000000000000000000000 : ℝ)*base67 + (687468058405749867/100550000000000000000000000000000 : ℝ)*base69 + (442915841871700133/100550000000000000000000000000000 : ℝ)*base72 + (575545852643/1005500000000000000000000000 : ℝ)*base74 + (557311678226100133/100550000000000000000000000000000 : ℝ)*base76 + (621887435760900133/100550000000000000000000000000000 : ℝ)*base78 + (680438800174600133/100550000000000000000000000000000 : ℝ)*base80 + (1763327466437/502750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (9121201/2000000000000000000000 : ℝ)*base90 + (9121201/2000000000000000000000 : ℝ)*base92 + (9121201/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (555598932328336489195663011/125687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (184450163/25000000000000 : ℝ)*(base19) + (186381947/25000000000000 : ℝ)*(base23) + (1491961/4000000000000 : ℝ)*(upper2) + (3761577/2500000000000 : ℝ)*(upper3) + (18411583/20000000000000 : ℝ)*(upper5) + (1206101356690543/100000000000000 : ℝ)*(major0) + (1206101356690543/100000000000000 : ℝ)*(major1) + (1206101356690543/100000000000000 : ℝ)*(major2) + (4564201111/100000000000000 : ℝ)*(sp1) + (6809243/200000000000 : ℝ)*(sp2) + (12683462381759/781250000000 : ℝ)*(sp4) + (405869470715847/25000000000000 : ℝ)*(sp5) + (1623479034715863/100000000000000 : ℝ)*(sp6) + (788719381166633/100000000000000 : ℝ)*(sp7) + (788719381166633/100000000000000 : ℝ)*(f.failure) + (12683462381759/781250000000 : ℝ)*(f.sum) + (52342116305249/10055000000000000000000000000 : ℝ)*base66 + (6054158463654270663/502750000000000000000000000000000 : ℝ)*base68 + (304548751070020663/502750000000000000000000000000000 : ℝ)*base70 + (1079182144247020663/502750000000000000000000000000000 : ℝ)*base72 + (60457161295339/10055000000000000000000000000 : ℝ)*base74 + (187177325500729337/502750000000000000000000000000000 : ℝ)*base75 + (3771655086130770663/502750000000000000000000000000000 : ℝ)*base78 + (1775209917829770663/502750000000000000000000000000000 : ℝ)*base80 + (334572998459/157109375000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (17512437/2000000000000000000000 : ℝ)*base89 + (17512437/2000000000000000000000 : ℝ)*base91 + (17512437/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1296_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13603/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1063/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (403/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9909/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1296_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1296_s2_0 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2072439947/10000000000 : ℝ)*x 0 + (5493031889/10000000000 : ℝ)*x 1 + (5172911309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2072439947/10000000000 : ℝ)^133 ≤ (12586986956727/100000000000000 : ℝ)^101 := by
    have hnat : (2072439947 : ℕ)^133*100000000000000^101 ≤ 12586986956727^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072439947 10000000000 12586986956727 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5493031889/10000000000 : ℝ)^133 ≤ (1817340678389/4000000000000 : ℝ)^101 := by
    have hnat : (5493031889 : ℕ)^133*4000000000000^101 ≤ 1817340678389^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493031889 10000000000 1817340678389 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5172911309/10000000000 : ℝ)^133 ≤ (20989748031407/50000000000000 : ℝ)^101 := by
    have hnat : (5172911309 : ℕ)^133*50000000000000^101 ≤ 20989748031407^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172911309 10000000000 20989748031407 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2072439947/10000000000 : ℝ), (5493031889/10000000000 : ℝ), (5172911309/10000000000 : ℝ)] ![(12586986956727/100000000000000 : ℝ), (1817340678389/4000000000000 : ℝ), (20989748031407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2072439947/10000000000 : ℝ)|^133 ≤ (12586986956727/100000000000000 : ℝ)^101
        have hw : |(-2072439947/10000000000 : ℝ)|=(2072439947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5493031889/10000000000 : ℝ)|^133 ≤ (1817340678389/4000000000000 : ℝ)^101
        have hw : |(5493031889/10000000000 : ℝ)|=(5493031889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5172911309/10000000000 : ℝ)|^133 ≤ (20989748031407/50000000000000 : ℝ)^101
        have hw : |(5172911309/10000000000 : ℝ)|=(5172911309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s2_1 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1073857093/2000000000 : ℝ)*x 0 + (-223829203/1000000000 : ℝ)*x 1 + (646613917/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073857093/2000000000 : ℝ)^133 ≤ (44090546582603/100000000000000 : ℝ)^101 := by
    have hnat : (1073857093 : ℕ)^133*100000000000000^101 ≤ 44090546582603^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073857093 2000000000 44090546582603 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223829203/1000000000 : ℝ)^133 ≤ (13929957052823/100000000000000 : ℝ)^101 := by
    have hnat : (223829203 : ℕ)^133*100000000000000^101 ≤ 13929957052823^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223829203 1000000000 13929957052823 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (646613917/1250000000 : ℝ)^133 ≤ (10494874087837/25000000000000 : ℝ)^101 := by
    have hnat : (646613917 : ℕ)^133*25000000000000^101 ≤ 10494874087837^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646613917 1250000000 10494874087837 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073857093/2000000000 : ℝ), (-223829203/1000000000 : ℝ), (646613917/1250000000 : ℝ)] ![(44090546582603/100000000000000 : ℝ), (13929957052823/100000000000000 : ℝ), (10494874087837/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073857093/2000000000 : ℝ)|^133 ≤ (44090546582603/100000000000000 : ℝ)^101
        have hw : |(1073857093/2000000000 : ℝ)|=(1073857093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-223829203/1000000000 : ℝ)|^133 ≤ (13929957052823/100000000000000 : ℝ)^101
        have hw : |(-223829203/1000000000 : ℝ)|=(223829203/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(646613917/1250000000 : ℝ)|^133 ≤ (10494874087837/25000000000000 : ℝ)^101
        have hw : |(646613917/1250000000 : ℝ)|=(646613917/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s2_2 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2684642689/5000000000 : ℝ)*x 0 + (5172911317/10000000000 : ℝ)*x 1 + (-223829217/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684642689/5000000000 : ℝ)^133 ≤ (44090545641843/100000000000000 : ℝ)^101 := by
    have hnat : (2684642689 : ℕ)^133*100000000000000^101 ≤ 44090545641843^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684642689 5000000000 44090545641843 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5172911317/10000000000 : ℝ)^133 ≤ (8395899229661/20000000000000 : ℝ)^101 := by
    have hnat : (5172911317 : ℕ)^133*20000000000000^101 ≤ 8395899229661^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172911317 10000000000 8395899229661 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223829217/1000000000 : ℝ)^133 ≤ (13929958200161/100000000000000 : ℝ)^101 := by
    have hnat : (223829217 : ℕ)^133*100000000000000^101 ≤ 13929958200161^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223829217 1000000000 13929958200161 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684642689/5000000000 : ℝ), (5172911317/10000000000 : ℝ), (-223829217/1000000000 : ℝ)] ![(44090545641843/100000000000000 : ℝ), (8395899229661/20000000000000 : ℝ), (13929958200161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684642689/5000000000 : ℝ)|^133 ≤ (44090545641843/100000000000000 : ℝ)^101
        have hw : |(2684642689/5000000000 : ℝ)|=(2684642689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5172911317/10000000000 : ℝ)|^133 ≤ (8395899229661/20000000000000 : ℝ)^101
        have hw : |(5172911317/10000000000 : ℝ)|=(5172911317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-223829217/1000000000 : ℝ)|^133 ≤ (13929958200161/100000000000000 : ℝ)^101
        have hw : |(-223829217/1000000000 : ℝ)|=(223829217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s2_3 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (866252377/2000000000 : ℝ)*x 0 + (2006855913/5000000000 : ℝ)*x 1 + (1168162237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866252377/2000000000 : ℝ)^133 ≤ (3322633092517/10000000000000 : ℝ)^101 := by
    have hnat : (866252377 : ℕ)^133*10000000000000^101 ≤ 3322633092517^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866252377 2000000000 3322633092517 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2006855913/5000000000 : ℝ)^133 ≤ (6011281352437/20000000000000 : ℝ)^101 := by
    have hnat : (2006855913 : ℕ)^133*20000000000000^101 ≤ 6011281352437^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006855913 5000000000 6011281352437 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1168162237/2500000000 : ℝ)^133 ≤ (9179315574951/25000000000000 : ℝ)^101 := by
    have hnat : (1168162237 : ℕ)^133*25000000000000^101 ≤ 9179315574951^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1168162237 2500000000 9179315574951 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(866252377/2000000000 : ℝ), (2006855913/5000000000 : ℝ), (1168162237/2500000000 : ℝ)] ![(3322633092517/10000000000000 : ℝ), (6011281352437/20000000000000 : ℝ), (9179315574951/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(866252377/2000000000 : ℝ)|^133 ≤ (3322633092517/10000000000000 : ℝ)^101
        have hw : |(866252377/2000000000 : ℝ)|=(866252377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2006855913/5000000000 : ℝ)|^133 ≤ (6011281352437/20000000000000 : ℝ)^101
        have hw : |(2006855913/5000000000 : ℝ)|=(2006855913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1168162237/2500000000 : ℝ)|^133 ≤ (9179315574951/25000000000000 : ℝ)^101
        have hw : |(1168162237/2500000000 : ℝ)|=(1168162237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s2_4 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-129532543/625000000 : ℝ)*x 0 + (20214947/39062500 : ℝ)*x 1 + (549089707/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129532543/625000000 : ℝ)^133 ≤ (629381635521/5000000000000 : ℝ)^101 := by
    have hnat : (129532543 : ℕ)^133*5000000000000^101 ≤ 629381635521^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129532543 625000000 629381635521 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20214947/39062500 : ℝ)^133 ≤ (5250262578847/12500000000000 : ℝ)^101 := by
    have hnat : (20214947 : ℕ)^133*12500000000000^101 ≤ 5250262578847^101*39062500^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20214947 39062500 5250262578847 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549089707/1000000000 : ℝ)^133 ≤ (11352566661447/25000000000000 : ℝ)^101 := by
    have hnat : (549089707 : ℕ)^133*25000000000000^101 ≤ 11352566661447^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549089707 1000000000 11352566661447 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-129532543/625000000 : ℝ), (20214947/39062500 : ℝ), (549089707/1000000000 : ℝ)] ![(629381635521/5000000000000 : ℝ), (5250262578847/12500000000000 : ℝ), (11352566661447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-129532543/625000000 : ℝ)|^133 ≤ (629381635521/5000000000000 : ℝ)^101
        have hw : |(-129532543/625000000 : ℝ)|=(129532543/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20214947/39062500 : ℝ)|^133 ≤ (5250262578847/12500000000000 : ℝ)^101
        have hw : |(20214947/39062500 : ℝ)|=(20214947/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(549089707/1000000000 : ℝ)|^133 ≤ (11352566661447/25000000000000 : ℝ)^101
        have hw : |(549089707/1000000000 : ℝ)|=(549089707/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s2_5 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5287200217/10000000000 : ℝ)*x 0 + (-480076427/2500000000 : ℝ)*x 1 + (2745448599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287200217/10000000000 : ℝ)^133 ≤ (8641017864197/20000000000000 : ℝ)^101 := by
    have hnat : (5287200217 : ℕ)^133*20000000000000^101 ≤ 8641017864197^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287200217 10000000000 8641017864197 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (480076427/2500000000 : ℝ)^133 ≤ (11384642614789/100000000000000 : ℝ)^101 := by
    have hnat : (480076427 : ℕ)^133*100000000000000^101 ≤ 11384642614789^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480076427 2500000000 11384642614789 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2745448599/5000000000 : ℝ)^133 ≤ (181641072159/400000000000 : ℝ)^101 := by
    have hnat : (2745448599 : ℕ)^133*400000000000^101 ≤ 181641072159^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745448599 5000000000 181641072159 400000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287200217/10000000000 : ℝ), (-480076427/2500000000 : ℝ), (2745448599/5000000000 : ℝ)] ![(8641017864197/20000000000000 : ℝ), (11384642614789/100000000000000 : ℝ), (181641072159/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287200217/10000000000 : ℝ)|^133 ≤ (8641017864197/20000000000000 : ℝ)^101
        have hw : |(5287200217/10000000000 : ℝ)|=(5287200217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-480076427/2500000000 : ℝ)|^133 ≤ (11384642614789/100000000000000 : ℝ)^101
        have hw : |(-480076427/2500000000 : ℝ)|=(480076427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2745448599/5000000000 : ℝ)|^133 ≤ (181641072159/400000000000 : ℝ)^101
        have hw : |(2745448599/5000000000 : ℝ)|=(2745448599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s2_6 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2643600187/5000000000 : ℝ)*x 0 + (5490897077/10000000000 : ℝ)*x 1 + (-1920305661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643600187/5000000000 : ℝ)^133 ≤ (43205091010411/100000000000000 : ℝ)^101 := by
    have hnat : (2643600187 : ℕ)^133*100000000000000^101 ≤ 43205091010411^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643600187 5000000000 43205091010411 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490897077/10000000000 : ℝ)^133 ≤ (2270513336101/5000000000000 : ℝ)^101 := by
    have hnat : (5490897077 : ℕ)^133*5000000000000^101 ≤ 2270513336101^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490897077 10000000000 2270513336101 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1920305661/10000000000 : ℝ)^133 ≤ (1423080280983/12500000000000 : ℝ)^101 := by
    have hnat : (1920305661 : ℕ)^133*12500000000000^101 ≤ 1423080280983^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920305661 10000000000 1423080280983 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643600187/5000000000 : ℝ), (5490897077/10000000000 : ℝ), (-1920305661/10000000000 : ℝ)] ![(43205091010411/100000000000000 : ℝ), (2270513336101/5000000000000 : ℝ), (1423080280983/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643600187/5000000000 : ℝ)|^133 ≤ (43205091010411/100000000000000 : ℝ)^101
        have hw : |(2643600187/5000000000 : ℝ)|=(2643600187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490897077/10000000000 : ℝ)|^133 ≤ (2270513336101/5000000000000 : ℝ)^101
        have hw : |(5490897077/10000000000 : ℝ)|=(5490897077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1920305661/10000000000 : ℝ)|^133 ≤ (1423080280983/12500000000000 : ℝ)^101
        have hw : |(-1920305661/10000000000 : ℝ)|=(1920305661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s2_7 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4331427511/10000000000 : ℝ)*x 0 + (4668293461/10000000000 : ℝ)*x 1 + (4018111103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331427511/10000000000 : ℝ)^133 ≤ (3322800405389/10000000000000 : ℝ)^101 := by
    have hnat : (4331427511 : ℕ)^133*10000000000000^101 ≤ 3322800405389^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331427511 10000000000 3322800405389 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4668293461/10000000000 : ℝ)^133 ≤ (36672200350019/100000000000000 : ℝ)^101 := by
    have hnat : (4668293461 : ℕ)^133*100000000000000^101 ≤ 36672200350019^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4668293461 10000000000 36672200350019 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4018111103/10000000000 : ℝ)^133 ≤ (30099795581217/100000000000000 : ℝ)^101 := by
    have hnat : (4018111103 : ℕ)^133*100000000000000^101 ≤ 30099795581217^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4018111103 10000000000 30099795581217 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331427511/10000000000 : ℝ), (4668293461/10000000000 : ℝ), (4018111103/10000000000 : ℝ)] ![(3322800405389/10000000000000 : ℝ), (36672200350019/100000000000000 : ℝ), (30099795581217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331427511/10000000000 : ℝ)|^133 ≤ (3322800405389/10000000000000 : ℝ)^101
        have hw : |(4331427511/10000000000 : ℝ)|=(4331427511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4668293461/10000000000 : ℝ)|^133 ≤ (36672200350019/100000000000000 : ℝ)^101
        have hw : |(4668293461/10000000000 : ℝ)|=(4668293461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4018111103/10000000000 : ℝ)|^133 ≤ (30099795581217/100000000000000 : ℝ)^101
        have hw : |(4018111103/10000000000 : ℝ)|=(4018111103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1296_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9909/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (403/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (4767/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16299/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9909/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (403/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9909/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (403/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9909/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (403/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9909/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (403/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9909/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (403/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9909/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (403/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (403/6250 : ℝ) ^ (4255/1024 : ℝ) ≤ (564683959328657/50000000000000000000 : ℝ) := by
    have hpowers : (403/6250 : ℝ)^4255 ≤ (564683959328657/50000000000000000000 : ℝ)^1024 := by
      have hnat : (403 : ℕ)^4255*50000000000000000000^1024 ≤ 564683959328657^1024*6250^4255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        403 6250 564683959328657 50000000000000000000 4255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (403/6250 : ℝ)) (X := (564683959328657/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9909/50000 : ℝ) ^ (4255/1024 : ℝ) ≤ (119975165813321171/100000000000000000000 : ℝ) := by
    have hpowers : (9909/50000 : ℝ)^4255 ≤ (119975165813321171/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9909 : ℕ)^4255*100000000000000000000^1024 ≤ 119975165813321171^1024*50000^4255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9909 50000 119975165813321171 100000000000000000000 4255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9909/50000 : ℝ)) (X := (119975165813321171/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000564683959328657/25000000000000000000 : ℝ) ≤ (625003397364369/625000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (25000564683959328657/25000000000000000000 : ℝ)^1024 ≤ (625003397364369/625000000000000 : ℝ)^4255 := by
      have hnat : (25000564683959328657 : ℕ)^1024*625000000000000^4255 ≤ 625003397364369^4255*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000564683959328657 25000000000000000000 625003397364369 625000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625003397364369/625000000000000 : ℝ)) (X := (25000564683959328657/25000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20024220906746395697/20000000000000000000 : ℝ) ≤ (5001456569481553/5000000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (20024220906746395697/20000000000000000000 : ℝ)^1024 ≤ (5001456569481553/5000000000000000 : ℝ)^4255 := by
      have hnat : (20024220906746395697 : ℕ)^1024*5000000000000000^4255 ≤ 5001456569481553^4255*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20024220906746395697 20000000000000000000 5001456569481553 5000000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001456569481553/5000000000000000 : ℝ)) (X := (20024220906746395697/20000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50119975165813321171/50000000000000000000 : ℝ) ≤ (2501442980024077/2500000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (50119975165813321171/50000000000000000000 : ℝ)^1024 ≤ (2501442980024077/2500000000000000 : ℝ)^4255 := by
      have hnat : (50119975165813321171 : ℕ)^1024*2500000000000000^4255 ≤ 2501442980024077^4255*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50119975165813321171 50000000000000000000 2501442980024077 2500000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501442980024077/2500000000000000 : ℝ)) (X := (50119975165813321171/50000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(564683959328657/50000000000000000000 : ℝ) ≤ ((4176995622584126359/4178125000000000000 : ℝ)+2*(1429390566601/668500000000000 : ℝ)*(403/6250 : ℝ))^(4255/1024 : ℝ) := by
    rw [show (4176995622584126359/4178125000000000000 : ℝ)+2*(1429390566601/668500000000000 : ℝ)*(403/6250 : ℝ)=(625003397364369/625000000000000 : ℝ) by norm_num, show 1+2*(564683959328657/50000000000000000000 : ℝ)=(25000564683959328657/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(119975165813321171/100000000000000000000 : ℝ)+(564683959328657/50000000000000000000 : ℝ) ≤ ((4176995622584126359/4178125000000000000 : ℝ)+(1429390566601/668500000000000 : ℝ)*((9909/50000 : ℝ)+(403/6250 : ℝ)))^(4255/1024 : ℝ) := by
    rw [show (4176995622584126359/4178125000000000000 : ℝ)+(1429390566601/668500000000000 : ℝ)*((9909/50000 : ℝ)+(403/6250 : ℝ))=(5001456569481553/5000000000000000 : ℝ) by norm_num, show 1+(119975165813321171/100000000000000000000 : ℝ)+(564683959328657/50000000000000000000 : ℝ)=(20024220906746395697/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(119975165813321171/100000000000000000000 : ℝ) ≤ ((4176995622584126359/4178125000000000000 : ℝ)+2*(1429390566601/668500000000000 : ℝ)*(9909/50000 : ℝ))^(4255/1024 : ℝ) := by
    rw [show (4176995622584126359/4178125000000000000 : ℝ)+2*(1429390566601/668500000000000 : ℝ)*(9909/50000 : ℝ)=(2501442980024077/2500000000000000 : ℝ) by norm_num, show 1+2*(119975165813321171/100000000000000000000 : ℝ)=(50119975165813321171/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4176995622584126359/4178125000000000000 : ℝ)*(X 1 0+X 2 0)+(1429390566601/668500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (403/6250 : ℝ)) (hi := (9909/50000 : ℝ)) (c := (4176995622584126359/4178125000000000000 : ℝ)) (alpha := (1429390566601/668500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4176995622584126359/4178125000000000000 : ℝ)*(X 0 1+X 2 1)+(1429390566601/668500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (403/6250 : ℝ)) (hi := (9909/50000 : ℝ)) (c := (4176995622584126359/4178125000000000000 : ℝ)) (alpha := (1429390566601/668500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4176995622584126359/4178125000000000000 : ℝ)*(X 0 2+X 1 2)+(1429390566601/668500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (403/6250 : ℝ)) (hi := (9909/50000 : ℝ)) (c := (4176995622584126359/4178125000000000000 : ℝ)) (alpha := (1429390566601/668500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2072439947/10000000000 : ℝ)*X 0 0+(5493031889/10000000000 : ℝ)*X 0 1+(5172911309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1073857093/2000000000 : ℝ)*X 1 0+(-223829203/1000000000 : ℝ)*X 1 1+(646613917/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2684642689/5000000000 : ℝ)*X 2 0+(5172911317/10000000000 : ℝ)*X 2 1+(-223829217/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((866252377/2000000000 : ℝ)*X 0 0+(2006855913/5000000000 : ℝ)*X 0 1+(1168162237/2500000000 : ℝ)*X 0 2+(866252377/2000000000 : ℝ)*X 1 0+(2006855913/5000000000 : ℝ)*X 1 1+(1168162237/2500000000 : ℝ)*X 1 2+(866252377/2000000000 : ℝ)*X 2 0+(2006855913/5000000000 : ℝ)*X 2 1+(1168162237/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-129532543/625000000 : ℝ)*X 0 0+(20214947/39062500 : ℝ)*X 0 1+(549089707/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287200217/10000000000 : ℝ)*X 1 0+(-480076427/2500000000 : ℝ)*X 1 1+(2745448599/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643600187/5000000000 : ℝ)*X 2 0+(5490897077/10000000000 : ℝ)*X 2 1+(-1920305661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4331427511/10000000000 : ℝ)*X 0 0+(4668293461/10000000000 : ℝ)*X 0 1+(4018111103/10000000000 : ℝ)*X 0 2+(4331427511/10000000000 : ℝ)*X 1 0+(4668293461/10000000000 : ℝ)*X 1 1+(4018111103/10000000000 : ℝ)*X 1 2+(4331427511/10000000000 : ℝ)*X 2 0+(4668293461/10000000000 : ℝ)*X 2 1+(4018111103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (145997420166037108742632827/52226562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (748215673/50000000000000 : ℝ)*(base19) + (29640361/2500000000000 : ℝ)*(base23) + (139709061/100000000000000 : ℝ)*(lower2) + (261378693/50000000000000 : ℝ)*(upper3) + (198165093/100000000000000 : ℝ)*(upper5) + (290091458680781/12500000000000 : ℝ)*(major0) + (290091458680781/12500000000000 : ℝ)*(major1) + (290091458680781/12500000000000 : ℝ)*(major2) + (3123834626843677/100000000000000 : ℝ)*(sp0) + (1561919836070607/50000000000000 : ℝ)*(sp1) + (3123839982958119/100000000000000 : ℝ)*(sp2) + (379401769306037/25000000000000 : ℝ)*(sp3) + (3270864441/50000000000000 : ℝ)*(sp4) + (3749978419/25000000000000 : ℝ)*(sp7) + (47425689910557/3125000000000 : ℝ)*(f.failure) + (39048014607157/1250000000000 : ℝ)*(f.sum) + (138255623289377/33425000000000000000000000000 : ℝ)*base66 + (909363496629172133/104453125000000000000000000000000 : ℝ)*base67 + (1323176684516047133/104453125000000000000000000000000 : ℝ)*base69 + (27242055122039127/26113281250000000000000000000000 : ℝ)*base71 + (23368450025481/4178125000000000000000000000 : ℝ)*base73 + (313927450374156379/52226562500000000000000000000000 : ℝ)*base75 + (19120234019835873/26113281250000000000000000000000 : ℝ)*base78 + (658121575527453383/104453125000000000000000000000000 : ℝ)*base79 + (105022300749349/16712500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (839527/62500000000000000000 : ℝ)*base90 + (839527/62500000000000000000 : ℝ)*base92 + (839527/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1048146737820987570698398779/208906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (969249999/100000000000000 : ℝ)*(base19) + (1254250877/100000000000000 : ℝ)*(base23) + (32676269/20000000000000 : ℝ)*(upper3) + (68878307/100000000000000 : ℝ)*(lower4) + (23472347/50000000000000 : ℝ)*(upper5) + (2351940766115627/100000000000000 : ℝ)*(major0) + (2351940766115627/100000000000000 : ℝ)*(major1) + (2351940766115627/100000000000000 : ℝ)*(major2) + (9880512497/100000000000000 : ℝ)*(sp1) + (6895776273/50000000000000 : ℝ)*(sp2) + (395731296674453/12500000000000 : ℝ)*(sp4) + (395729940454141/12500000000000 : ℝ)*(sp5) + (1582917663796101/50000000000000 : ℝ)*(sp6) + (1538030991592067/100000000000000 : ℝ)*(sp7) + (1538030991592067/100000000000000 : ℝ)*(f.failure) + (395731296674453/12500000000000 : ℝ)*(f.sum) + (37747484165351/16712500000000000000000000000 : ℝ)*base65 + (727562079566743343/417812500000000000000000000000000 : ℝ)*base67 + (521084834952631657/417812500000000000000000000000000 : ℝ)*base70 + (749124270057055843/417812500000000000000000000000000 : ℝ)*base71 + (66755463537401/16712500000000000000000000000 : ℝ)*base73 + (840176453725131657/417812500000000000000000000000000 : ℝ)*base76 + (3515659661360131657/417812500000000000000000000000000 : ℝ)*base78 + (3375449871032006657/417812500000000000000000000000000 : ℝ)*base80 + (18376431278563/8356250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (11201863/2000000000000000000000 : ℝ)*base89 + (11201863/2000000000000000000000 : ℝ)*base91 + (11201863/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1296_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9909/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (403/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4767/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16299/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1296_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1296_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4767/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16299/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1296_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1296_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1296_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4767/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16299/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1296_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
