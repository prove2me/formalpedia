-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1347_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:06:36.966538+00:00
-- url     : https://prove2.me/submissions/93f60f27-b8c7-44bc-a4a8-dc46172c724f

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
theorem support_rectangle_w1347_s6_0 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-509913983/2500000000 : ℝ)*x 0 + (5412462539/10000000000 : ℝ)*x 1 + (5244749169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (509913983/2500000000 : ℝ)^4307 ≤ (6211134377363/50000000000000 : ℝ)^3283 := by
    have hnat : (509913983 : ℕ)^4307*50000000000000^3283 ≤ 6211134377363^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509913983 2500000000 6211134377363 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412462539/10000000000 : ℝ)^4307 ≤ (22346430197743/50000000000000 : ℝ)^3283 := by
    have hnat : (5412462539 : ℕ)^4307*50000000000000^3283 ≤ 22346430197743^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412462539 10000000000 22346430197743 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244749169/10000000000 : ℝ)^4307 ≤ (42884870834897/100000000000000 : ℝ)^3283 := by
    have hnat : (5244749169 : ℕ)^4307*100000000000000^3283 ≤ 42884870834897^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244749169 10000000000 42884870834897 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-509913983/2500000000 : ℝ), (5412462539/10000000000 : ℝ), (5244749169/10000000000 : ℝ)] ![(6211134377363/50000000000000 : ℝ), (22346430197743/50000000000000 : ℝ), (42884870834897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-509913983/2500000000 : ℝ)|^4307 ≤ (6211134377363/50000000000000 : ℝ)^3283
        have hw : |(-509913983/2500000000 : ℝ)|=(509913983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412462539/10000000000 : ℝ)|^4307 ≤ (22346430197743/50000000000000 : ℝ)^3283
        have hw : |(5412462539/10000000000 : ℝ)|=(5412462539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244749169/10000000000 : ℝ)|^4307 ≤ (42884870834897/100000000000000 : ℝ)^3283
        have hw : |(5244749169/10000000000 : ℝ)|=(5244749169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s6_1 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167153591/312500000 : ℝ)*x 0 + (-2125103337/10000000000 : ℝ)*x 1 + (524474917/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167153591/312500000 : ℝ)^4307 ≤ (22002857636491/50000000000000 : ℝ)^3283 := by
    have hnat : (167153591 : ℕ)^4307*50000000000000^3283 ≤ 22002857636491^3283*312500000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167153591 312500000 22002857636491 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2125103337/10000000000 : ℝ)^4307 ≤ (6554706930529/50000000000000 : ℝ)^3283 := by
    have hnat : (2125103337 : ℕ)^4307*50000000000000^3283 ≤ 6554706930529^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125103337 10000000000 6554706930529 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524474917/1000000000 : ℝ)^4307 ≤ (5360608855703/12500000000000 : ℝ)^3283 := by
    have hnat : (524474917 : ℕ)^4307*12500000000000^3283 ≤ 5360608855703^3283*1000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524474917 1000000000 5360608855703 12500000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167153591/312500000 : ℝ), (-2125103337/10000000000 : ℝ), (524474917/1000000000 : ℝ)] ![(22002857636491/50000000000000 : ℝ), (6554706930529/50000000000000 : ℝ), (5360608855703/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167153591/312500000 : ℝ)|^4307 ≤ (22002857636491/50000000000000 : ℝ)^3283
        have hw : |(167153591/312500000 : ℝ)|=(167153591/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2125103337/10000000000 : ℝ)|^4307 ≤ (6554706930529/50000000000000 : ℝ)^3283
        have hw : |(-2125103337/10000000000 : ℝ)|=(2125103337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524474917/1000000000 : ℝ)|^4307 ≤ (5360608855703/12500000000000 : ℝ)^3283
        have hw : |(524474917/1000000000 : ℝ)|=(524474917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s6_2 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069782983/2000000000 : ℝ)*x 0 + (524474917/1000000000 : ℝ)*x 1 + (-2125103333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069782983/2000000000 : ℝ)^4307 ≤ (44005715305361/100000000000000 : ℝ)^3283 := by
    have hnat : (1069782983 : ℕ)^4307*100000000000000^3283 ≤ 44005715305361^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069782983 2000000000 44005715305361 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524474917/1000000000 : ℝ)^4307 ≤ (5360608855703/12500000000000 : ℝ)^3283 := by
    have hnat : (524474917 : ℕ)^4307*12500000000000^3283 ≤ 5360608855703^3283*1000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524474917 1000000000 5360608855703 12500000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125103333/10000000000 : ℝ)^4307 ≤ (6554706914343/50000000000000 : ℝ)^3283 := by
    have hnat : (2125103333 : ℕ)^4307*50000000000000^3283 ≤ 6554706914343^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125103333 10000000000 6554706914343 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069782983/2000000000 : ℝ), (524474917/1000000000 : ℝ), (-2125103333/10000000000 : ℝ)] ![(44005715305361/100000000000000 : ℝ), (5360608855703/12500000000000 : ℝ), (6554706914343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069782983/2000000000 : ℝ)|^4307 ≤ (44005715305361/100000000000000 : ℝ)^3283
        have hw : |(1069782983/2000000000 : ℝ)|=(1069782983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524474917/1000000000 : ℝ)|^4307 ≤ (5360608855703/12500000000000 : ℝ)^3283
        have hw : |(524474917/1000000000 : ℝ)|=(524474917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2125103333/10000000000 : ℝ)|^4307 ≤ (6554706914343/50000000000000 : ℝ)^3283
        have hw : |(-2125103333/10000000000 : ℝ)|=(2125103333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s6_3 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (865062439/2000000000 : ℝ)*x 0 + (259542247/625000000 : ℝ)*x 1 + (2252312349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865062439/2000000000 : ℝ)^4307 ≤ (333033348721/1000000000000 : ℝ)^3283 := by
    have hnat : (865062439 : ℕ)^4307*1000000000000^3283 ≤ 333033348721^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865062439 2000000000 333033348721 1000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259542247/625000000 : ℝ)^4307 ≤ (15785226165807/50000000000000 : ℝ)^3283 := by
    have hnat : (259542247 : ℕ)^4307*50000000000000^3283 ≤ 15785226165807^3283*625000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259542247 625000000 15785226165807 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252312349/5000000000 : ℝ)^4307 ≤ (35126212778123/100000000000000 : ℝ)^3283 := by
    have hnat : (2252312349 : ℕ)^4307*100000000000000^3283 ≤ 35126212778123^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252312349 5000000000 35126212778123 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865062439/2000000000 : ℝ), (259542247/625000000 : ℝ), (2252312349/5000000000 : ℝ)] ![(333033348721/1000000000000 : ℝ), (15785226165807/50000000000000 : ℝ), (35126212778123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865062439/2000000000 : ℝ)|^4307 ≤ (333033348721/1000000000000 : ℝ)^3283
        have hw : |(865062439/2000000000 : ℝ)|=(865062439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259542247/625000000 : ℝ)|^4307 ≤ (15785226165807/50000000000000 : ℝ)^3283
        have hw : |(259542247/625000000 : ℝ)|=(259542247/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252312349/5000000000 : ℝ)|^4307 ≤ (35126212778123/100000000000000 : ℝ)^3283
        have hw : |(2252312349/5000000000 : ℝ)|=(2252312349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s6_4 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-25495853/125000000 : ℝ)*x 0 + (2622674917/5000000000 : ℝ)*x 1 + (5411858643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25495853/125000000 : ℝ)^4307 ≤ (6211183548007/50000000000000 : ℝ)^3283 := by
    have hnat : (25495853 : ℕ)^4307*50000000000000^3283 ≤ 6211183548007^3283*125000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25495853 125000000 6211183548007 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622674917/5000000000 : ℝ)^4307 ≤ (42891314358981/100000000000000 : ℝ)^3283 := by
    have hnat : (2622674917 : ℕ)^4307*100000000000000^3283 ≤ 42891314358981^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622674917 5000000000 42891314358981 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411858643/10000000000 : ℝ)^4307 ≤ (11171579631663/25000000000000 : ℝ)^3283 := by
    have hnat : (5411858643 : ℕ)^4307*25000000000000^3283 ≤ 11171579631663^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411858643 10000000000 11171579631663 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-25495853/125000000 : ℝ), (2622674917/5000000000 : ℝ), (5411858643/10000000000 : ℝ)] ![(6211183548007/50000000000000 : ℝ), (42891314358981/100000000000000 : ℝ), (11171579631663/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-25495853/125000000 : ℝ)|^4307 ≤ (6211183548007/50000000000000 : ℝ)^3283
        have hw : |(-25495853/125000000 : ℝ)|=(25495853/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622674917/5000000000 : ℝ)|^4307 ≤ (42891314358981/100000000000000 : ℝ)^3283
        have hw : |(2622674917/5000000000 : ℝ)|=(2622674917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411858643/10000000000 : ℝ)|^4307 ≤ (11171579631663/25000000000000 : ℝ)^3283
        have hw : |(5411858643/10000000000 : ℝ)|=(5411858643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s6_5 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061138229/2000000000 : ℝ)*x 0 + (-195799373/1000000000 : ℝ)*x 1 + (541185853/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061138229/2000000000 : ℝ)^4307 ≤ (2176989229317/5000000000000 : ℝ)^3283 := by
    have hnat : (1061138229 : ℕ)^4307*5000000000000^3283 ≤ 2176989229317^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061138229 2000000000 2176989229317 5000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195799373/1000000000 : ℝ)^4307 ≤ (5886949048043/50000000000000 : ℝ)^3283 := by
    have hnat : (195799373 : ℕ)^4307*50000000000000^3283 ≤ 5886949048043^3283*1000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195799373 1000000000 5886949048043 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541185853/1000000000 : ℝ)^4307 ≤ (4468631730257/10000000000000 : ℝ)^3283 := by
    have hnat : (541185853 : ℕ)^4307*10000000000000^3283 ≤ 4468631730257^3283*1000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541185853 1000000000 4468631730257 10000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061138229/2000000000 : ℝ), (-195799373/1000000000 : ℝ), (541185853/1000000000 : ℝ)] ![(2176989229317/5000000000000 : ℝ), (5886949048043/50000000000000 : ℝ), (4468631730257/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061138229/2000000000 : ℝ)|^4307 ≤ (2176989229317/5000000000000 : ℝ)^3283
        have hw : |(1061138229/2000000000 : ℝ)|=(1061138229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-195799373/1000000000 : ℝ)|^4307 ≤ (5886949048043/50000000000000 : ℝ)^3283
        have hw : |(-195799373/1000000000 : ℝ)|=(195799373/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541185853/1000000000 : ℝ)|^4307 ≤ (4468631730257/10000000000000 : ℝ)^3283
        have hw : |(541185853/1000000000 : ℝ)|=(541185853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s6_6 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305691133/10000000000 : ℝ)*x 0 + (676482313/1250000000 : ℝ)*x 1 + (-978996891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305691133/10000000000 : ℝ)^4307 ≤ (870795689143/2000000000000 : ℝ)^3283 := by
    have hnat : (5305691133 : ℕ)^4307*2000000000000^3283 ≤ 870795689143^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305691133 10000000000 870795689143 2000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676482313/1250000000 : ℝ)^4307 ≤ (44686317020923/100000000000000 : ℝ)^3283 := by
    have hnat : (676482313 : ℕ)^4307*100000000000000^3283 ≤ 44686317020923^3283*1250000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676482313 1250000000 44686317020923 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (978996891/5000000000 : ℝ)^4307 ≤ (5886949253153/50000000000000 : ℝ)^3283 := by
    have hnat : (978996891 : ℕ)^4307*50000000000000^3283 ≤ 5886949253153^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978996891 5000000000 5886949253153 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305691133/10000000000 : ℝ), (676482313/1250000000 : ℝ), (-978996891/5000000000 : ℝ)] ![(870795689143/2000000000000 : ℝ), (44686317020923/100000000000000 : ℝ), (5886949253153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305691133/10000000000 : ℝ)|^4307 ≤ (870795689143/2000000000000 : ℝ)^3283
        have hw : |(5305691133/10000000000 : ℝ)|=(5305691133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676482313/1250000000 : ℝ)|^4307 ≤ (44686317020923/100000000000000 : ℝ)^3283
        have hw : |(676482313/1250000000 : ℝ)|=(676482313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-978996891/5000000000 : ℝ)|^4307 ≤ (5886949253153/50000000000000 : ℝ)^3283
        have hw : |(-978996891/5000000000 : ℝ)|=(978996891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s6_7 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (865067529/2000000000 : ℝ)*x 0 + (4503364007/10000000000 : ℝ)*x 1 + (83078863/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865067529/2000000000 : ℝ)^4307 ≤ (8325897987159/25000000000000 : ℝ)^3283 := by
    have hnat : (865067529 : ℕ)^4307*25000000000000^3283 ≤ 8325897987159^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865067529 2000000000 8325897987159 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503364007/10000000000 : ℝ)^4307 ≤ (4389164555047/12500000000000 : ℝ)^3283 := by
    have hnat : (4503364007 : ℕ)^4307*12500000000000^3283 ≤ 4389164555047^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503364007 10000000000 4389164555047 12500000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83078863/200000000 : ℝ)^4307 ≤ (31583091598823/100000000000000 : ℝ)^3283 := by
    have hnat : (83078863 : ℕ)^4307*100000000000000^3283 ≤ 31583091598823^3283*200000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83078863 200000000 31583091598823 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865067529/2000000000 : ℝ), (4503364007/10000000000 : ℝ), (83078863/200000000 : ℝ)] ![(8325897987159/25000000000000 : ℝ), (4389164555047/12500000000000 : ℝ), (31583091598823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865067529/2000000000 : ℝ)|^4307 ≤ (8325897987159/25000000000000 : ℝ)^3283
        have hw : |(865067529/2000000000 : ℝ)|=(865067529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503364007/10000000000 : ℝ)|^4307 ≤ (4389164555047/12500000000000 : ℝ)^3283
        have hw : |(4503364007/10000000000 : ℝ)|=(4503364007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(83078863/200000000 : ℝ)|^4307 ≤ (31583091598823/100000000000000 : ℝ)^3283
        have hw : |(83078863/200000000 : ℝ)|=(83078863/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1347_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (279/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14711/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7359/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11153/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7359/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11153/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7359/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11153/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7359/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11153/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7359/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11153/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7359/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11153/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11153/100000 : ℝ) ^ (2153/512 : ℝ) ≤ (2466878125026713/25000000000000000000 : ℝ) := by
    have hpowers : (11153/100000 : ℝ)^2153 ≤ (2466878125026713/25000000000000000000 : ℝ)^512 := by
      have hnat : (11153 : ℕ)^2153*25000000000000000000^512 ≤ 2466878125026713^512*100000^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11153 100000 2466878125026713 25000000000000000000 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11153/100000 : ℝ)) (X := (2466878125026713/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7359/50000 : ℝ) ^ (2153/512 : ℝ) ≤ (6335329127912827/20000000000000000000 : ℝ) := by
    have hpowers : (7359/50000 : ℝ)^2153 ≤ (6335329127912827/20000000000000000000 : ℝ)^512 := by
      have hnat : (7359 : ℕ)^2153*20000000000000000000^512 ≤ 6335329127912827^512*50000^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7359 50000 6335329127912827 20000000000000000000 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7359/50000 : ℝ)) (X := (6335329127912827/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502466878125026713/12500000000000000000 : ℝ) ≤ (5000234639408899/5000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (12502466878125026713/12500000000000000000 : ℝ)^512 ≤ (5000234639408899/5000000000000000 : ℝ)^2153 := by
      have hnat : (12502466878125026713 : ℕ)^512*5000000000000000^2153 ≤ 5000234639408899^2153*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502466878125026713 12500000000000000000 5000234639408899 5000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000234639408899/5000000000000000 : ℝ)) (X := (12502466878125026713/12500000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041544158139670987/100000000000000000000 : ℝ) ≤ (625061737233391/625000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (100041544158139670987/100000000000000000000 : ℝ)^512 ≤ (625061737233391/625000000000000 : ℝ)^2153 := by
      have hnat : (100041544158139670987 : ℕ)^512*625000000000000^2153 ≤ 625061737233391^2153*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041544158139670987 100000000000000000000 625061737233391 625000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625061737233391/625000000000000 : ℝ)) (X := (100041544158139670987/100000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006335329127912827/10000000000000000000 : ℝ) ≤ (5000753156325357/5000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (10006335329127912827/10000000000000000000 : ℝ)^512 ≤ (5000753156325357/5000000000000000 : ℝ)^2153 := by
      have hnat : (10006335329127912827 : ℕ)^512*5000000000000000^2153 ≤ 5000753156325357^2153*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006335329127912827 10000000000000000000 5000753156325357 5000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000753156325357/5000000000000000 : ℝ)) (X := (10006335329127912827/10000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2466878125026713/25000000000000000000 : ℝ) ≤ ((17820053470323468861/17825000000000000000 : ℝ)+2*(259258458229/178250000000000 : ℝ)*(11153/100000 : ℝ))^(2153/512 : ℝ) := by
    rw [show (17820053470323468861/17825000000000000000 : ℝ)+2*(259258458229/178250000000000 : ℝ)*(11153/100000 : ℝ)=(5000234639408899/5000000000000000 : ℝ) by norm_num, show 1+2*(2466878125026713/25000000000000000000 : ℝ)=(12502466878125026713/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6335329127912827/20000000000000000000 : ℝ)+(2466878125026713/25000000000000000000 : ℝ) ≤ ((17820053470323468861/17825000000000000000 : ℝ)+(259258458229/178250000000000 : ℝ)*((7359/50000 : ℝ)+(11153/100000 : ℝ)))^(2153/512 : ℝ) := by
    rw [show (17820053470323468861/17825000000000000000 : ℝ)+(259258458229/178250000000000 : ℝ)*((7359/50000 : ℝ)+(11153/100000 : ℝ))=(625061737233391/625000000000000 : ℝ) by norm_num, show 1+(6335329127912827/20000000000000000000 : ℝ)+(2466878125026713/25000000000000000000 : ℝ)=(100041544158139670987/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6335329127912827/20000000000000000000 : ℝ) ≤ ((17820053470323468861/17825000000000000000 : ℝ)+2*(259258458229/178250000000000 : ℝ)*(7359/50000 : ℝ))^(2153/512 : ℝ) := by
    rw [show (17820053470323468861/17825000000000000000 : ℝ)+2*(259258458229/178250000000000 : ℝ)*(7359/50000 : ℝ)=(5000753156325357/5000000000000000 : ℝ) by norm_num, show 1+2*(6335329127912827/20000000000000000000 : ℝ)=(10006335329127912827/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17820053470323468861/17825000000000000000 : ℝ)*(X 1 0+X 2 0)+(259258458229/178250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (11153/100000 : ℝ)) (hi := (7359/50000 : ℝ)) (c := (17820053470323468861/17825000000000000000 : ℝ)) (alpha := (259258458229/178250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17820053470323468861/17825000000000000000 : ℝ)*(X 0 1+X 2 1)+(259258458229/178250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (11153/100000 : ℝ)) (hi := (7359/50000 : ℝ)) (c := (17820053470323468861/17825000000000000000 : ℝ)) (alpha := (259258458229/178250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17820053470323468861/17825000000000000000 : ℝ)*(X 0 2+X 1 2)+(259258458229/178250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (11153/100000 : ℝ)) (hi := (7359/50000 : ℝ)) (c := (17820053470323468861/17825000000000000000 : ℝ)) (alpha := (259258458229/178250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-509913983/2500000000 : ℝ)*X 0 0+(5412462539/10000000000 : ℝ)*X 0 1+(5244749169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167153591/312500000 : ℝ)*X 1 0+(-2125103337/10000000000 : ℝ)*X 1 1+(524474917/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069782983/2000000000 : ℝ)*X 2 0+(524474917/1000000000 : ℝ)*X 2 1+(-2125103333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((865062439/2000000000 : ℝ)*X 0 0+(259542247/625000000 : ℝ)*X 0 1+(2252312349/5000000000 : ℝ)*X 0 2+(865062439/2000000000 : ℝ)*X 1 0+(259542247/625000000 : ℝ)*X 1 1+(2252312349/5000000000 : ℝ)*X 1 2+(865062439/2000000000 : ℝ)*X 2 0+(259542247/625000000 : ℝ)*X 2 1+(2252312349/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-25495853/125000000 : ℝ)*X 0 0+(2622674917/5000000000 : ℝ)*X 0 1+(5411858643/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061138229/2000000000 : ℝ)*X 1 0+(-195799373/1000000000 : ℝ)*X 1 1+(541185853/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305691133/10000000000 : ℝ)*X 2 0+(676482313/1250000000 : ℝ)*X 2 1+(-978996891/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((865067529/2000000000 : ℝ)*X 0 0+(4503364007/10000000000 : ℝ)*X 0 1+(83078863/200000000 : ℝ)*X 0 2+(865067529/2000000000 : ℝ)*X 1 0+(4503364007/10000000000 : ℝ)*X 1 1+(83078863/200000000 : ℝ)*X 1 2+(865067529/2000000000 : ℝ)*X 2 0+(4503364007/10000000000 : ℝ)*X 2 1+(83078863/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1567045395678702868045499931/178250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1654909573/100000000000000 : ℝ)*(base19) + (309013777/20000000000000 : ℝ)*(base23) + (15135409/25000000000000 : ℝ)*(lower2) + (110614147/50000000000000 : ℝ)*(upper3) + (143325543/100000000000000 : ℝ)*(upper5) + (880397894869043/20000000000000 : ℝ)*(major0) + (880397894869043/20000000000000 : ℝ)*(major1) + (17195271384161/390625000000 : ℝ)*(major2) + (1192517805278489/20000000000000 : ℝ)*(sp0) + (5962621260583553/100000000000000 : ℝ)*(sp1) + (74532767130303/1250000000000 : ℝ)*(sp2) + (355167300483853/12500000000000 : ℝ)*(sp3) + (847227517/2500000000000 : ℝ)*(sp4) + (8668141929/50000000000000 : ℝ)*(sp7) + (1420677870077341/50000000000000 : ℝ)*(f.failure) + (9540196664789/160000000000 : ℝ)*(f.sum) + (12907671632949/17825000000000000000000000000 : ℝ)*base65 + (304732651794150023/356500000000000000000000000000000 : ℝ)*base67 + (193203767754083109/27851562500000000000000000000000 : ℝ)*base69 + (1011909902636349977/356500000000000000000000000000000 : ℝ)*base72 + (13214760786987/8912500000000000000000000000 : ℝ)*base73 + (715154936198474407/55703125000000000000000000000000 : ℝ)*base76 + (68155067547090001/15500000000000000000000000000000 : ℝ)*base77 + (41458928305090001/15500000000000000000000000000000 : ℝ)*base79 + (2269822336057/1782500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (450231/625000000000000000000 : ℝ)*base90 + (450231/625000000000000000000 : ℝ)*base92 + (6700231/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27570287582643554451150687/3593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1073980417/50000000000000 : ℝ)*(base19) + (1116016537/50000000000000 : ℝ)*(base23) + (27694789/50000000000000 : ℝ)*(upper2) + (197339997/100000000000000 : ℝ)*(upper3) + (28726763/12500000000000 : ℝ)*(upper5) + (554222855938859/12500000000000 : ℝ)*(major0) + (554222855938859/12500000000000 : ℝ)*(major1) + (554222855938859/12500000000000 : ℝ)*(major2) + (336751103/781250000000 : ℝ)*(sp1) + (10569165073/25000000000000 : ℝ)*(sp2) + (6005688004606667/100000000000000 : ℝ)*(sp4) + (6005642752504649/100000000000000 : ℝ)*(sp5) + (60056434959133/1000000000000 : ℝ)*(sp6) + (357734679336333/12500000000000 : ℝ)*(sp7) + (357734679336333/12500000000000 : ℝ)*(f.failure) + (6005688004606667/100000000000000 : ℝ)*(f.sum) + (256511846437/71875000000000000000000000 : ℝ)*base65 + (2772561486338577/312500000000000000000000000000 : ℝ)*base68 + (505985215223923/312500000000000000000000000000 : ℝ)*base69 + (1464918132276077/312500000000000000000000000000 : ℝ)*base72 + (2051369481877/287500000000000000000000000 : ℝ)*base74 + (4894874275088577/312500000000000000000000000000 : ℝ)*base76 + (1149997871963577/312500000000000000000000000000 : ℝ)*base78 + (1381526775536423/312500000000000000000000000000 : ℝ)*base79 + (213217605549/143750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (505097/156250000000000000000 : ℝ)*base89 + (505097/156250000000000000000 : ℝ)*base91 + (505097/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1347_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1347_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1347_s7_0 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1019830839/5000000000 : ℝ)*x 0 + (2706202491/5000000000 : ℝ)*x 1 + (2622401507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1019830839/5000000000 : ℝ)^4307 ≤ (2484462933083/20000000000000 : ℝ)^3283 := by
    have hnat : (1019830839 : ℕ)^4307*20000000000000^3283 ≤ 2484462933083^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019830839 5000000000 2484462933083 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706202491/5000000000 : ℝ)^4307 ≤ (22346118441851/50000000000000 : ℝ)^3283 := by
    have hnat : (2706202491 : ℕ)^4307*50000000000000^3283 ≤ 22346118441851^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706202491 5000000000 22346118441851 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622401507/5000000000 : ℝ)^4307 ≤ (10721362109477/25000000000000 : ℝ)^3283 := by
    have hnat : (2622401507 : ℕ)^4307*25000000000000^3283 ≤ 10721362109477^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622401507 5000000000 10721362109477 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1019830839/5000000000 : ℝ), (2706202491/5000000000 : ℝ), (2622401507/5000000000 : ℝ)] ![(2484462933083/20000000000000 : ℝ), (22346118441851/50000000000000 : ℝ), (10721362109477/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1019830839/5000000000 : ℝ)|^4307 ≤ (2484462933083/20000000000000 : ℝ)^3283
        have hw : |(-1019830839/5000000000 : ℝ)|=(1019830839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706202491/5000000000 : ℝ)|^4307 ≤ (22346118441851/50000000000000 : ℝ)^3283
        have hw : |(2706202491/5000000000 : ℝ)|=(2706202491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622401507/5000000000 : ℝ)|^4307 ≤ (10721362109477/25000000000000 : ℝ)^3283
        have hw : |(2622401507/5000000000 : ℝ)|=(2622401507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s7_1 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674450723/5000000000 : ℝ)*x 0 + (-425010101/2000000000 : ℝ)*x 1 + (2622401289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674450723/5000000000 : ℝ)^4307 ≤ (22002784966379/50000000000000 : ℝ)^3283 := by
    have hnat : (2674450723 : ℕ)^4307*50000000000000^3283 ≤ 22002784966379^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674450723 5000000000 22002784966379 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425010101/2000000000 : ℝ)^4307 ≤ (6554493147817/50000000000000 : ℝ)^3283 := by
    have hnat : (425010101 : ℕ)^4307*50000000000000^3283 ≤ 6554493147817^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425010101 2000000000 6554493147817 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622401289/5000000000 : ℝ)^4307 ≤ (42885443760867/100000000000000 : ℝ)^3283 := by
    have hnat : (2622401289 : ℕ)^4307*100000000000000^3283 ≤ 42885443760867^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622401289 5000000000 42885443760867 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674450723/5000000000 : ℝ), (-425010101/2000000000 : ℝ), (2622401289/5000000000 : ℝ)] ![(22002784966379/50000000000000 : ℝ), (6554493147817/50000000000000 : ℝ), (42885443760867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674450723/5000000000 : ℝ)|^4307 ≤ (22002784966379/50000000000000 : ℝ)^3283
        have hw : |(2674450723/5000000000 : ℝ)|=(2674450723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-425010101/2000000000 : ℝ)|^4307 ≤ (6554493147817/50000000000000 : ℝ)^3283
        have hw : |(-425010101/2000000000 : ℝ)|=(425010101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622401289/5000000000 : ℝ)|^4307 ≤ (42885443760867/100000000000000 : ℝ)^3283
        have hw : |(2622401289/5000000000 : ℝ)|=(2622401289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s7_2 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348900341/10000000000 : ℝ)*x 0 + (2622401601/5000000000 : ℝ)*x 1 + (-2125051151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348900341/10000000000 : ℝ)^4307 ≤ (1100138950159/2500000000000 : ℝ)^3283 := by
    have hnat : (5348900341 : ℕ)^4307*2500000000000^3283 ≤ 1100138950159^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348900341 10000000000 1100138950159 2500000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622401601/5000000000 : ℝ)^4307 ≤ (8577090090923/20000000000000 : ℝ)^3283 := by
    have hnat : (2622401601 : ℕ)^4307*20000000000000^3283 ≤ 8577090090923^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622401601 5000000000 8577090090923 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125051151/10000000000 : ℝ)^4307 ≤ (3277247880911/25000000000000 : ℝ)^3283 := by
    have hnat : (2125051151 : ℕ)^4307*25000000000000^3283 ≤ 3277247880911^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125051151 10000000000 3277247880911 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348900341/10000000000 : ℝ), (2622401601/5000000000 : ℝ), (-2125051151/10000000000 : ℝ)] ![(1100138950159/2500000000000 : ℝ), (8577090090923/20000000000000 : ℝ), (3277247880911/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348900341/10000000000 : ℝ)|^4307 ≤ (1100138950159/2500000000000 : ℝ)^3283
        have hw : |(5348900341/10000000000 : ℝ)|=(5348900341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622401601/5000000000 : ℝ)|^4307 ≤ (8577090090923/20000000000000 : ℝ)^3283
        have hw : |(2622401601/5000000000 : ℝ)|=(2622401601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2125051151/10000000000 : ℝ)|^4307 ≤ (3277247880911/25000000000000 : ℝ)^3283
        have hw : |(-2125051151/10000000000 : ℝ)|=(2125051151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s7_3 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540664457/1250000000 : ℝ)*x 0 + (415279197/1000000000 : ℝ)*x 1 + (450450817/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540664457/1250000000 : ℝ)^4307 ≤ (33303369832461/100000000000000 : ℝ)^3283 := by
    have hnat : (540664457 : ℕ)^4307*100000000000000^3283 ≤ 33303369832461^3283*1250000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540664457 1250000000 33303369832461 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415279197/1000000000 : ℝ)^4307 ≤ (31571609466581/100000000000000 : ℝ)^3283 := by
    have hnat : (415279197 : ℕ)^4307*100000000000000^3283 ≤ 31571609466581^3283*1000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415279197 1000000000 31571609466581 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450450817/1000000000 : ℝ)^4307 ≤ (35125020698557/100000000000000 : ℝ)^3283 := by
    have hnat : (450450817 : ℕ)^4307*100000000000000^3283 ≤ 35125020698557^3283*1000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450450817 1000000000 35125020698557 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540664457/1250000000 : ℝ), (415279197/1000000000 : ℝ), (450450817/1000000000 : ℝ)] ![(33303369832461/100000000000000 : ℝ), (31571609466581/100000000000000 : ℝ), (35125020698557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540664457/1250000000 : ℝ)|^4307 ≤ (33303369832461/100000000000000 : ℝ)^3283
        have hw : |(540664457/1250000000 : ℝ)|=(540664457/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(415279197/1000000000 : ℝ)|^4307 ≤ (31571609466581/100000000000000 : ℝ)^3283
        have hw : |(415279197/1000000000 : ℝ)|=(415279197/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450450817/1000000000 : ℝ)|^4307 ≤ (35125020698557/100000000000000 : ℝ)^3283
        have hw : |(450450817/1000000000 : ℝ)|=(450450817/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s7_4 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2039673591/10000000000 : ℝ)*x 0 + (2622701481/5000000000 : ℝ)*x 1 + (1352950521/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2039673591/10000000000 : ℝ)^4307 ≤ (6211204925361/50000000000000 : ℝ)^3283 := by
    have hnat : (2039673591 : ℕ)^4307*50000000000000^3283 ≤ 6211204925361^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039673591 10000000000 6211204925361 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622701481/5000000000 : ℝ)^4307 ≤ (42891884290977/100000000000000 : ℝ)^3283 := by
    have hnat : (2622701481 : ℕ)^4307*100000000000000^3283 ≤ 42891884290977^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622701481 5000000000 42891884290977 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352950521/2500000000 : ℝ)^4307 ≤ (44685705847453/100000000000000 : ℝ)^3283 := by
    have hnat : (1352950521 : ℕ)^4307*100000000000000^3283 ≤ 44685705847453^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352950521 2500000000 44685705847453 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2039673591/10000000000 : ℝ), (2622701481/5000000000 : ℝ), (1352950521/2500000000 : ℝ)] ![(6211204925361/50000000000000 : ℝ), (42891884290977/100000000000000 : ℝ), (44685705847453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2039673591/10000000000 : ℝ)|^4307 ≤ (6211204925361/50000000000000 : ℝ)^3283
        have hw : |(-2039673591/10000000000 : ℝ)|=(2039673591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622701481/5000000000 : ℝ)|^4307 ≤ (42891884290977/100000000000000 : ℝ)^3283
        have hw : |(2622701481/5000000000 : ℝ)|=(2622701481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352950521/2500000000 : ℝ)|^4307 ≤ (44685705847453/100000000000000 : ℝ)^3283
        have hw : |(1352950521/2500000000 : ℝ)|=(1352950521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s7_5 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305705189/10000000000 : ℝ)*x 0 + (-244756507/1250000000 : ℝ)*x 1 + (5411802097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305705189/10000000000 : ℝ)^4307 ≤ (43539935781991/100000000000000 : ℝ)^3283 := by
    have hnat : (5305705189 : ℕ)^4307*100000000000000^3283 ≤ 43539935781991^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305705189 10000000000 43539935781991 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (244756507/1250000000 : ℝ)^4307 ≤ (735897388907/6250000000000 : ℝ)^3283 := by
    have hnat : (244756507 : ℕ)^4307*6250000000000^3283 ≤ 735897388907^3283*1250000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244756507 1250000000 735897388907 6250000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411802097/10000000000 : ℝ)^4307 ≤ (11171426497069/25000000000000 : ℝ)^3283 := by
    have hnat : (5411802097 : ℕ)^4307*25000000000000^3283 ≤ 11171426497069^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411802097 10000000000 11171426497069 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305705189/10000000000 : ℝ), (-244756507/1250000000 : ℝ), (5411802097/10000000000 : ℝ)] ![(43539935781991/100000000000000 : ℝ), (735897388907/6250000000000 : ℝ), (11171426497069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305705189/10000000000 : ℝ)|^4307 ≤ (43539935781991/100000000000000 : ℝ)^3283
        have hw : |(5305705189/10000000000 : ℝ)|=(5305705189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-244756507/1250000000 : ℝ)|^4307 ≤ (735897388907/6250000000000 : ℝ)^3283
        have hw : |(-244756507/1250000000 : ℝ)|=(244756507/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411802097/10000000000 : ℝ)|^4307 ≤ (11171426497069/25000000000000 : ℝ)^3283
        have hw : |(5411802097/10000000000 : ℝ)|=(5411802097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s7_6 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652852587/5000000000 : ℝ)*x 0 + (338237631/625000000 : ℝ)*x 1 + (-979026039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652852587/5000000000 : ℝ)^4307 ≤ (43539935620503/100000000000000 : ℝ)^3283 := by
    have hnat : (2652852587 : ℕ)^4307*100000000000000^3283 ≤ 43539935620503^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652852587 5000000000 43539935620503 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338237631/625000000 : ℝ)^4307 ≤ (44685705977443/100000000000000 : ℝ)^3283 := by
    have hnat : (338237631 : ℕ)^4307*100000000000000^3283 ≤ 44685705977443^3283*625000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338237631 625000000 44685705977443 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (979026039/5000000000 : ℝ)^4307 ≤ (2943589599017/25000000000000 : ℝ)^3283 := by
    have hnat : (979026039 : ℕ)^4307*25000000000000^3283 ≤ 2943589599017^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979026039 5000000000 2943589599017 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652852587/5000000000 : ℝ), (338237631/625000000 : ℝ), (-979026039/5000000000 : ℝ)] ![(43539935620503/100000000000000 : ℝ), (44685705977443/100000000000000 : ℝ), (2943589599017/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652852587/5000000000 : ℝ)|^4307 ≤ (43539935620503/100000000000000 : ℝ)^3283
        have hw : |(2652852587/5000000000 : ℝ)|=(2652852587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338237631/625000000 : ℝ)|^4307 ≤ (44685705977443/100000000000000 : ℝ)^3283
        have hw : |(338237631/625000000 : ℝ)|=(338237631/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-979026039/5000000000 : ℝ)|^4307 ≤ (2943589599017/25000000000000 : ℝ)^3283
        have hw : |(-979026039/5000000000 : ℝ)|=(979026039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s7_7 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081335381/2500000000 : ℝ)*x 0 + (900649699/2000000000 : ℝ)*x 1 + (51925721/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081335381/2500000000 : ℝ)^4307 ≤ (4162953891423/12500000000000 : ℝ)^3283 := by
    have hnat : (1081335381 : ℕ)^4307*12500000000000^3283 ≤ 4162953891423^3283*2500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081335381 2500000000 4162953891423 12500000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900649699/2000000000 : ℝ)^4307 ≤ (8778033714399/25000000000000 : ℝ)^3283 := by
    have hnat : (900649699 : ℕ)^4307*25000000000000^3283 ≤ 8778033714399^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900649699 2000000000 8778033714399 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51925721/125000000 : ℝ)^4307 ≤ (31584234001491/100000000000000 : ℝ)^3283 := by
    have hnat : (51925721 : ℕ)^4307*100000000000000^3283 ≤ 31584234001491^3283*125000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51925721 125000000 31584234001491 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081335381/2500000000 : ℝ), (900649699/2000000000 : ℝ), (51925721/125000000 : ℝ)] ![(4162953891423/12500000000000 : ℝ), (8778033714399/25000000000000 : ℝ), (31584234001491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081335381/2500000000 : ℝ)|^4307 ≤ (4162953891423/12500000000000 : ℝ)^3283
        have hw : |(1081335381/2500000000 : ℝ)|=(1081335381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900649699/2000000000 : ℝ)|^4307 ≤ (8778033714399/25000000000000 : ℝ)^3283
        have hw : |(900649699/2000000000 : ℝ)|=(900649699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(51925721/125000000 : ℝ)|^4307 ≤ (31584234001491/100000000000000 : ℝ)^3283
        have hw : |(51925721/125000000 : ℝ)|=(51925721/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1347_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (11161/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1471/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14711/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (279/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14711/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (279/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14711/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (279/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14711/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (279/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14711/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (279/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14711/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (279/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (279/2500 : ℝ) ^ (2153/512 : ℝ) ≤ (9893581531223623/100000000000000000000 : ℝ) := by
    have hpowers : (279/2500 : ℝ)^2153 ≤ (9893581531223623/100000000000000000000 : ℝ)^512 := by
      have hnat : (279 : ℕ)^2153*100000000000000000000^512 ≤ 9893581531223623^512*2500^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        279 2500 9893581531223623 100000000000000000000 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (279/2500 : ℝ)) (X := (9893581531223623/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14711/100000 : ℝ) ^ (2153/512 : ℝ) ≤ (31613341592544011/100000000000000000000 : ℝ) := by
    have hpowers : (14711/100000 : ℝ)^2153 ≤ (31613341592544011/100000000000000000000 : ℝ)^512 := by
      have hnat : (14711 : ℕ)^2153*100000000000000000000^512 ≤ 31613341592544011^512*100000^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14711 100000 31613341592544011 100000000000000000000 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14711/100000 : ℝ)) (X := (31613341592544011/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009893581531223623/50000000000000000000 : ℝ) ≤ (5000235259257201/5000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (50009893581531223623/50000000000000000000 : ℝ)^512 ≤ (5000235259257201/5000000000000000 : ℝ)^2153 := by
      have hnat : (50009893581531223623 : ℕ)^512*5000000000000000^2153 ≤ 5000235259257201^2153*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009893581531223623 50000000000000000000 5000235259257201 5000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000235259257201/5000000000000000 : ℝ)) (X := (50009893581531223623/50000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020753461561883817/50000000000000000000 : ℝ) ≤ (156265420477141/156250000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (50020753461561883817/50000000000000000000 : ℝ)^512 ≤ (156265420477141/156250000000000 : ℝ)^2153 := by
      have hnat : (50020753461561883817 : ℕ)^512*156250000000000^2153 ≤ 156265420477141^2153*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020753461561883817 50000000000000000000 156265420477141 156250000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156265420477141/156250000000000 : ℝ)) (X := (50020753461561883817/50000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031613341592544011/50000000000000000000 : ℝ) ≤ (5000751651279823/5000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (50031613341592544011/50000000000000000000 : ℝ)^512 ≤ (5000751651279823/5000000000000000 : ℝ)^2153 := by
      have hnat : (50031613341592544011 : ℕ)^512*5000000000000000^2153 ≤ 5000751651279823^2153*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031613341592544011 50000000000000000000 5000751651279823 5000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000751651279823/5000000000000000 : ℝ)) (X := (50031613341592544011/50000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9893581531223623/100000000000000000000 : ℝ) ≤ ((17750072470649859231/17755000000000000000 : ℝ)+2*(258196011311/177550000000000 : ℝ)*(279/2500 : ℝ))^(2153/512 : ℝ) := by
    rw [show (17750072470649859231/17755000000000000000 : ℝ)+2*(258196011311/177550000000000 : ℝ)*(279/2500 : ℝ)=(5000235259257201/5000000000000000 : ℝ) by norm_num, show 1+2*(9893581531223623/100000000000000000000 : ℝ)=(50009893581531223623/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31613341592544011/100000000000000000000 : ℝ)+(9893581531223623/100000000000000000000 : ℝ) ≤ ((17750072470649859231/17755000000000000000 : ℝ)+(258196011311/177550000000000 : ℝ)*((14711/100000 : ℝ)+(279/2500 : ℝ)))^(2153/512 : ℝ) := by
    rw [show (17750072470649859231/17755000000000000000 : ℝ)+(258196011311/177550000000000 : ℝ)*((14711/100000 : ℝ)+(279/2500 : ℝ))=(156265420477141/156250000000000 : ℝ) by norm_num, show 1+(31613341592544011/100000000000000000000 : ℝ)+(9893581531223623/100000000000000000000 : ℝ)=(50020753461561883817/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31613341592544011/100000000000000000000 : ℝ) ≤ ((17750072470649859231/17755000000000000000 : ℝ)+2*(258196011311/177550000000000 : ℝ)*(14711/100000 : ℝ))^(2153/512 : ℝ) := by
    rw [show (17750072470649859231/17755000000000000000 : ℝ)+2*(258196011311/177550000000000 : ℝ)*(14711/100000 : ℝ)=(5000751651279823/5000000000000000 : ℝ) by norm_num, show 1+2*(31613341592544011/100000000000000000000 : ℝ)=(50031613341592544011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17750072470649859231/17755000000000000000 : ℝ)*(X 1 0+X 2 0)+(258196011311/177550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (279/2500 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (17750072470649859231/17755000000000000000 : ℝ)) (alpha := (258196011311/177550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17750072470649859231/17755000000000000000 : ℝ)*(X 0 1+X 2 1)+(258196011311/177550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (279/2500 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (17750072470649859231/17755000000000000000 : ℝ)) (alpha := (258196011311/177550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17750072470649859231/17755000000000000000 : ℝ)*(X 0 2+X 1 2)+(258196011311/177550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (279/2500 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (17750072470649859231/17755000000000000000 : ℝ)) (alpha := (258196011311/177550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1019830839/5000000000 : ℝ)*X 0 0+(2706202491/5000000000 : ℝ)*X 0 1+(2622401507/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674450723/5000000000 : ℝ)*X 1 0+(-425010101/2000000000 : ℝ)*X 1 1+(2622401289/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348900341/10000000000 : ℝ)*X 2 0+(2622401601/5000000000 : ℝ)*X 2 1+(-2125051151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((540664457/1250000000 : ℝ)*X 0 0+(415279197/1000000000 : ℝ)*X 0 1+(450450817/1000000000 : ℝ)*X 0 2+(540664457/1250000000 : ℝ)*X 1 0+(415279197/1000000000 : ℝ)*X 1 1+(450450817/1000000000 : ℝ)*X 1 2+(540664457/1250000000 : ℝ)*X 2 0+(415279197/1000000000 : ℝ)*X 2 1+(450450817/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2039673591/10000000000 : ℝ)*X 0 0+(2622701481/5000000000 : ℝ)*X 0 1+(1352950521/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305705189/10000000000 : ℝ)*X 1 0+(-244756507/1250000000 : ℝ)*X 1 1+(5411802097/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652852587/5000000000 : ℝ)*X 2 0+(338237631/625000000 : ℝ)*X 2 1+(-979026039/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081335381/2500000000 : ℝ)*X 0 0+(900649699/2000000000 : ℝ)*X 0 1+(51925721/125000000 : ℝ)*X 0 2+(1081335381/2500000000 : ℝ)*X 1 0+(900649699/2000000000 : ℝ)*X 1 1+(51925721/125000000 : ℝ)*X 1 2+(1081335381/2500000000 : ℝ)*X 2 0+(900649699/2000000000 : ℝ)*X 2 1+(51925721/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (431676121714300648797304887/55484375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23138289/781250000000 : ℝ)*(base19) + (493974339/25000000000000 : ℝ)*(base23) + (47874267/25000000000000 : ℝ)*(upper2) + (304423263/100000000000000 : ℝ)*(upper3) + (275309873453309/6250000000000 : ℝ)*(major0) + (275309873453309/6250000000000 : ℝ)*(major1) + (275309873453309/6250000000000 : ℝ)*(major2) + (5966593344377169/100000000000000 : ℝ)*(sp0) + (5966640908607617/100000000000000 : ℝ)*(sp1) + (2983314062200683/50000000000000 : ℝ)*(sp2) + (710809339636181/25000000000000 : ℝ)*(sp3) + (50525931441/100000000000000 : ℝ)*(sp4) + (430312809/3125000000000 : ℝ)*(sp6) + (172311573/500000000000 : ℝ)*(sp7) + (710817955214831/25000000000000 : ℝ)*(f.failure) + (5966643870308609/100000000000000 : ℝ)*(f.sum) + (10060871701737/17755000000000000000000000000 : ℝ)*base66 + (298382569652295379/110968750000000000000000000000000 : ℝ)*base67 + (765248017582392121/110968750000000000000000000000000 : ℝ)*base70 + (189157577485232879/110968750000000000000000000000000 : ℝ)*base71 + (13486669279443/17755000000000000000000000000 : ℝ)*base73 + (505928054864142121/110968750000000000000000000000000 : ℝ)*base76 + (853184334856517121/110968750000000000000000000000000 : ℝ)*base78 + (27434439534579621/110968750000000000000000000000000 : ℝ)*base80 + (10695687215541/8877500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (369821/312500000000000000000 : ℝ)*base90 + (369821/312500000000000000000 : ℝ)*base92 + (369821/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (157961296949304029846250201/13871093750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1994090113/100000000000000 : ℝ)*(base19) + (2147276379/100000000000000 : ℝ)*(base23) + (86213277/12500000000000 : ℝ)*(lower1) + (116517139/50000000000000 : ℝ)*(upper3) + (79932813/100000000000000 : ℝ)*(lower4) + (230042131/100000000000000 : ℝ)*(upper5) + (138646054495789/3125000000000 : ℝ)*(major0) + (138646054495789/3125000000000 : ℝ)*(major1) + (138646054495789/3125000000000 : ℝ)*(major2) + (1198943567/50000000000000 : ℝ)*(sp2) + (6009603684216119/100000000000000 : ℝ)*(sp4) + (3004800845063003/50000000000000 : ℝ)*(sp5) + (3004799569526303/50000000000000 : ℝ)*(sp6) + (2863743423920891/100000000000000 : ℝ)*(sp7) + (2863743423920891/100000000000000 : ℝ)*(f.failure) + (6009603684216119/100000000000000 : ℝ)*(f.sum) + (48575448033769/17755000000000000000000000000 : ℝ)*base66 + (1897325732453762433/27742187500000000000000000000000 : ℝ)*base68 + (343286496696634241/55484375000000000000000000000000 : ℝ)*base70 + (3662022997955834509/55484375000000000000000000000000 : ℝ)*base71 + (37094625851961/17755000000000000000000000000 : ℝ)*base73 + (613572477945772009/55484375000000000000000000000000 : ℝ)*base75 + (540721494469227991/55484375000000000000000000000000 : ℝ)*base78 + (168998103883389029/13871093750000000000000000000000 : ℝ)*base80 + (19795902750567/8877500000000000000000000000 : ℝ)*base82 + (14126719/1250000000000000000000 : ℝ)*base89 + (14126719/1250000000000000000000 : ℝ)*base91 + (14126719/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1347_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11161/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1347_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1347_s8_0 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2039662099/10000000000 : ℝ)*x 0 + (5412397021/10000000000 : ℝ)*x 1 + (262240537/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2039662099/10000000000 : ℝ)^4307 ≤ (12422318029217/100000000000000 : ℝ)^3283 := by
    have hnat : (2039662099 : ℕ)^4307*100000000000000^3283 ≤ 12422318029217^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039662099 10000000000 12422318029217 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412397021/10000000000 : ℝ)^4307 ≤ (22346075321397/50000000000000 : ℝ)^3283 := by
    have hnat : (5412397021 : ℕ)^4307*50000000000000^3283 ≤ 22346075321397^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412397021 10000000000 22346075321397 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262240537/500000000 : ℝ)^4307 ≤ (42885531315967/100000000000000 : ℝ)^3283 := by
    have hnat : (262240537 : ℕ)^4307*100000000000000^3283 ≤ 42885531315967^3283*500000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262240537 500000000 42885531315967 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2039662099/10000000000 : ℝ), (5412397021/10000000000 : ℝ), (262240537/500000000 : ℝ)] ![(12422318029217/100000000000000 : ℝ), (22346075321397/50000000000000 : ℝ), (42885531315967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2039662099/10000000000 : ℝ)|^4307 ≤ (12422318029217/100000000000000 : ℝ)^3283
        have hw : |(-2039662099/10000000000 : ℝ)|=(2039662099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412397021/10000000000 : ℝ)|^4307 ≤ (22346075321397/50000000000000 : ℝ)^3283
        have hw : |(5412397021/10000000000 : ℝ)|=(5412397021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262240537/500000000 : ℝ)|^4307 ≤ (42885531315967/100000000000000 : ℝ)^3283
        have hw : |(262240537/500000000 : ℝ)|=(262240537/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s8_1 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674448987/5000000000 : ℝ)*x 0 + (-2125044271/10000000000 : ℝ)*x 1 + (209792431/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674448987/5000000000 : ℝ)^4307 ≤ (22002766229523/50000000000000 : ℝ)^3283 := by
    have hnat : (2674448987 : ℕ)^4307*50000000000000^3283 ≤ 22002766229523^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674448987 5000000000 22002766229523 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2125044271/10000000000 : ℝ)^4307 ≤ (13108935844557/100000000000000 : ℝ)^3283 := by
    have hnat : (2125044271 : ℕ)^4307*100000000000000^3283 ≤ 13108935844557^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125044271 10000000000 13108935844557 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209792431/400000000 : ℝ)^4307 ≤ (42885531691417/100000000000000 : ℝ)^3283 := by
    have hnat : (209792431 : ℕ)^4307*100000000000000^3283 ≤ 42885531691417^3283*400000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209792431 400000000 42885531691417 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674448987/5000000000 : ℝ), (-2125044271/10000000000 : ℝ), (209792431/400000000 : ℝ)] ![(22002766229523/50000000000000 : ℝ), (13108935844557/100000000000000 : ℝ), (42885531691417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674448987/5000000000 : ℝ)|^4307 ≤ (22002766229523/50000000000000 : ℝ)^3283
        have hw : |(2674448987/5000000000 : ℝ)|=(2674448987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2125044271/10000000000 : ℝ)|^4307 ≤ (13108935844557/100000000000000 : ℝ)^3283
        have hw : |(-2125044271/10000000000 : ℝ)|=(2125044271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209792431/400000000 : ℝ)|^4307 ≤ (42885531691417/100000000000000 : ℝ)^3283
        have hw : |(209792431/400000000 : ℝ)|=(209792431/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s8_2 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348898863/10000000000 : ℝ)*x 0 + (5244810213/10000000000 : ℝ)*x 1 + (-2125043829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348898863/10000000000 : ℝ)^4307 ≤ (44005542054129/100000000000000 : ℝ)^3283 := by
    have hnat : (5348898863 : ℕ)^4307*100000000000000^3283 ≤ 44005542054129^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348898863 10000000000 44005542054129 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244810213/10000000000 : ℝ)^4307 ≤ (42885525662751/100000000000000 : ℝ)^3283 := by
    have hnat : (5244810213 : ℕ)^4307*100000000000000^3283 ≤ 42885525662751^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244810213 10000000000 42885525662751 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125043829/10000000000 : ℝ)^4307 ≤ (6554466133751/50000000000000 : ℝ)^3283 := by
    have hnat : (2125043829 : ℕ)^4307*50000000000000^3283 ≤ 6554466133751^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125043829 10000000000 6554466133751 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348898863/10000000000 : ℝ), (5244810213/10000000000 : ℝ), (-2125043829/10000000000 : ℝ)] ![(44005542054129/100000000000000 : ℝ), (42885525662751/100000000000000 : ℝ), (6554466133751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348898863/10000000000 : ℝ)|^4307 ≤ (44005542054129/100000000000000 : ℝ)^3283
        have hw : |(5348898863/10000000000 : ℝ)|=(5348898863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244810213/10000000000 : ℝ)|^4307 ≤ (42885525662751/100000000000000 : ℝ)^3283
        have hw : |(5244810213/10000000000 : ℝ)|=(5244810213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2125043829/10000000000 : ℝ)|^4307 ≤ (6554466133751/50000000000000 : ℝ)^3283
        have hw : |(-2125043829/10000000000 : ℝ)|=(2125043829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s8_3 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (865063337/2000000000 : ℝ)*x 0 + (519101143/1250000000 : ℝ)*x 1 + (563061301/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865063337/2000000000 : ℝ)^4307 ≤ (3330338022663/10000000000000 : ℝ)^3283 := by
    have hnat : (865063337 : ℕ)^4307*10000000000000^3283 ≤ 3330338022663^3283*2000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865063337 2000000000 3330338022663 10000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (519101143/1250000000 : ℝ)^4307 ≤ (6314356151337/20000000000000 : ℝ)^3283 := by
    have hnat : (519101143 : ℕ)^4307*20000000000000^3283 ≤ 6314356151337^3283*1250000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519101143 1250000000 6314356151337 20000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563061301/1250000000 : ℝ)^4307 ≤ (35124838994427/100000000000000 : ℝ)^3283 := by
    have hnat : (563061301 : ℕ)^4307*100000000000000^3283 ≤ 35124838994427^3283*1250000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563061301 1250000000 35124838994427 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865063337/2000000000 : ℝ), (519101143/1250000000 : ℝ), (563061301/1250000000 : ℝ)] ![(3330338022663/10000000000000 : ℝ), (6314356151337/20000000000000 : ℝ), (35124838994427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865063337/2000000000 : ℝ)|^4307 ≤ (3330338022663/10000000000000 : ℝ)^3283
        have hw : |(865063337/2000000000 : ℝ)|=(865063337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(519101143/1250000000 : ℝ)|^4307 ≤ (6314356151337/20000000000000 : ℝ)^3283
        have hw : |(519101143/1250000000 : ℝ)|=(519101143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563061301/1250000000 : ℝ)|^4307 ≤ (35124838994427/100000000000000 : ℝ)^3283
        have hw : |(563061301/1250000000 : ℝ)|=(563061301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s8_4 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-127479649/625000000 : ℝ)*x 0 + (5245410483/10000000000 : ℝ)*x 1 + (5411794051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127479649/625000000 : ℝ)^4307 ≤ (12422416186827/100000000000000 : ℝ)^3283 := by
    have hnat : (127479649 : ℕ)^4307*100000000000000^3283 ≤ 12422416186827^3283*625000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127479649 625000000 12422416186827 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245410483/10000000000 : ℝ)^4307 ≤ (10722991243211/25000000000000 : ℝ)^3283 := by
    have hnat : (5245410483 : ℕ)^4307*25000000000000^3283 ≤ 10722991243211^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245410483 10000000000 10722991243211 25000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411794051/10000000000 : ℝ)^4307 ≤ (22342809414799/50000000000000 : ℝ)^3283 := by
    have hnat : (5411794051 : ℕ)^4307*50000000000000^3283 ≤ 22342809414799^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411794051 10000000000 22342809414799 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-127479649/625000000 : ℝ), (5245410483/10000000000 : ℝ), (5411794051/10000000000 : ℝ)] ![(12422416186827/100000000000000 : ℝ), (10722991243211/25000000000000 : ℝ), (22342809414799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-127479649/625000000 : ℝ)|^4307 ≤ (12422416186827/100000000000000 : ℝ)^3283
        have hw : |(-127479649/625000000 : ℝ)|=(127479649/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245410483/10000000000 : ℝ)|^4307 ≤ (10722991243211/25000000000000 : ℝ)^3283
        have hw : |(5245410483/10000000000 : ℝ)|=(5245410483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411794051/10000000000 : ℝ)|^4307 ≤ (22342809414799/50000000000000 : ℝ)^3283
        have hw : |(5411794051/10000000000 : ℝ)|=(5411794051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s8_5 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652853621/5000000000 : ℝ)*x 0 + (-979030187/5000000000 : ℝ)*x 1 + (2705896999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652853621/5000000000 : ℝ)^4307 ≤ (435399578843/1000000000000 : ℝ)^3283 := by
    have hnat : (2652853621 : ℕ)^4307*1000000000000^3283 ≤ 435399578843^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652853621 5000000000 435399578843 1000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (979030187/5000000000 : ℝ)^4307 ≤ (11774423842509/100000000000000 : ℝ)^3283 := by
    have hnat : (979030187 : ℕ)^4307*100000000000000^3283 ≤ 11774423842509^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979030187 5000000000 11774423842509 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705896999/5000000000 : ℝ)^4307 ≤ (44685618255473/100000000000000 : ℝ)^3283 := by
    have hnat : (2705896999 : ℕ)^4307*100000000000000^3283 ≤ 44685618255473^3283*5000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705896999 5000000000 44685618255473 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652853621/5000000000 : ℝ), (-979030187/5000000000 : ℝ), (2705896999/5000000000 : ℝ)] ![(435399578843/1000000000000 : ℝ), (11774423842509/100000000000000 : ℝ), (44685618255473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652853621/5000000000 : ℝ)|^4307 ≤ (435399578843/1000000000000 : ℝ)^3283
        have hw : |(2652853621/5000000000 : ℝ)|=(2652853621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-979030187/5000000000 : ℝ)|^4307 ≤ (11774423842509/100000000000000 : ℝ)^3283
        have hw : |(-979030187/5000000000 : ℝ)|=(979030187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705896999/5000000000 : ℝ)|^4307 ≤ (44685618255473/100000000000000 : ℝ)^3283
        have hw : |(2705896999/5000000000 : ℝ)|=(2705896999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s8_6 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663213397/1250000000 : ℝ)*x 0 + (5411794057/10000000000 : ℝ)*x 1 + (-1958060383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663213397/1250000000 : ℝ)^4307 ≤ (43539957173753/100000000000000 : ℝ)^3283 := by
    have hnat : (663213397 : ℕ)^4307*100000000000000^3283 ≤ 43539957173753^3283*1250000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663213397 1250000000 43539957173753 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411794057/10000000000 : ℝ)^4307 ≤ (44685618894593/100000000000000 : ℝ)^3283 := by
    have hnat : (5411794057 : ℕ)^4307*100000000000000^3283 ≤ 44685618894593^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411794057 10000000000 44685618894593 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1958060383/10000000000 : ℝ)^4307 ≤ (11774423913509/100000000000000 : ℝ)^3283 := by
    have hnat : (1958060383 : ℕ)^4307*100000000000000^3283 ≤ 11774423913509^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958060383 10000000000 11774423913509 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663213397/1250000000 : ℝ), (5411794057/10000000000 : ℝ), (-1958060383/10000000000 : ℝ)] ![(43539957173753/100000000000000 : ℝ), (44685618894593/100000000000000 : ℝ), (11774423913509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663213397/1250000000 : ℝ)|^4307 ≤ (43539957173753/100000000000000 : ℝ)^3283
        have hw : |(663213397/1250000000 : ℝ)|=(663213397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411794057/10000000000 : ℝ)|^4307 ≤ (44685618894593/100000000000000 : ℝ)^3283
        have hw : |(5411794057/10000000000 : ℝ)|=(5411794057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1958060383/10000000000 : ℝ)|^4307 ≤ (11774423913509/100000000000000 : ℝ)^3283
        have hw : |(-1958060383/10000000000 : ℝ)|=(1958060383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1347_s8_7 (p : ℝ) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (173013683/400000000 : ℝ)*x 0 + (562904001/1250000000 : ℝ)*x 1 + (4154074029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173013683/400000000 : ℝ)^4307 ≤ (33303636697173/100000000000000 : ℝ)^3283 := by
    have hnat : (173013683 : ℕ)^4307*100000000000000^3283 ≤ 33303636697173^3283*400000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173013683 400000000 33303636697173 100000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562904001/1250000000 : ℝ)^4307 ≤ (1755598310567/5000000000000 : ℝ)^3283 := by
    have hnat : (562904001 : ℕ)^4307*5000000000000^3283 ≤ 1755598310567^3283*1250000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562904001 1250000000 1755598310567 5000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4154074029/10000000000 : ℝ)^4307 ≤ (15792198539351/50000000000000 : ℝ)^3283 := by
    have hnat : (4154074029 : ℕ)^4307*50000000000000^3283 ≤ 15792198539351^3283*10000000000^4307 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154074029 10000000000 15792198539351 50000000000000 4307 3283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4307/1024 : ℝ)) 4307 3283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(173013683/400000000 : ℝ), (562904001/1250000000 : ℝ), (4154074029/10000000000 : ℝ)] ![(33303636697173/100000000000000 : ℝ), (1755598310567/5000000000000 : ℝ), (15792198539351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(173013683/400000000 : ℝ)|^4307 ≤ (33303636697173/100000000000000 : ℝ)^3283
        have hw : |(173013683/400000000 : ℝ)|=(173013683/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562904001/1250000000 : ℝ)|^4307 ≤ (1755598310567/5000000000000 : ℝ)^3283
        have hw : |(562904001/1250000000 : ℝ)|=(562904001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4154074029/10000000000 : ℝ)|^4307 ≤ (15792198539351/50000000000000 : ℝ)^3283
        have hw : |(4154074029/10000000000 : ℝ)|=(4154074029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1347_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11161/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5581/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14709/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1471/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11161/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1471/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11161/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1471/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11161/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1471/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11161/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1471/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11161/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1471/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11161/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11161/100000 : ℝ) ^ (2153/512 : ℝ) ≤ (9897309959338507/100000000000000000000 : ℝ) := by
    have hpowers : (11161/100000 : ℝ)^2153 ≤ (9897309959338507/100000000000000000000 : ℝ)^512 := by
      have hnat : (11161 : ℕ)^2153*100000000000000000000^512 ≤ 9897309959338507^512*100000^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11161 100000 9897309959338507 100000000000000000000 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11161/100000 : ℝ)) (X := (9897309959338507/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1471/10000 : ℝ) ^ (2153/512 : ℝ) ≤ (31604306034764067/100000000000000000000 : ℝ) := by
    have hpowers : (1471/10000 : ℝ)^2153 ≤ (31604306034764067/100000000000000000000 : ℝ)^512 := by
      have hnat : (1471 : ℕ)^2153*100000000000000000000^512 ≤ 31604306034764067^512*10000^2153 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1471 10000 31604306034764067 100000000000000000000 2153 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1471/10000 : ℝ)) (X := (31604306034764067/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009897309959338507/50000000000000000000 : ℝ) ≤ (1250058836977181/1250000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (50009897309959338507/50000000000000000000 : ℝ)^512 ≤ (1250058836977181/1250000000000000 : ℝ)^2153 := by
      have hnat : (50009897309959338507 : ℕ)^512*1250000000000000^2153 ≤ 1250058836977181^2153*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009897309959338507 50000000000000000000 1250058836977181 1250000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250058836977181/1250000000000000 : ℝ)) (X := (50009897309959338507/50000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020750807997051287/50000000000000000000 : ℝ) ≤ (10000986784369299/10000000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (50020750807997051287/50000000000000000000 : ℝ)^512 ≤ (10000986784369299/10000000000000000 : ℝ)^2153 := by
      have hnat : (50020750807997051287 : ℕ)^512*10000000000000000^2153 ≤ 10000986784369299^2153*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020750807997051287 50000000000000000000 10000986784369299 10000000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000986784369299/10000000000000000 : ℝ)) (X := (50020750807997051287/50000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031604306034764067/50000000000000000000 : ℝ) ≤ (200030057458423/200000000000000 : ℝ) ^ (2153/512 : ℝ) := by
    have hpowers : (50031604306034764067/50000000000000000000 : ℝ)^512 ≤ (200030057458423/200000000000000 : ℝ)^2153 := by
      have hnat : (50031604306034764067 : ℕ)^512*200000000000000^2153 ≤ 200030057458423^2153*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031604306034764067 50000000000000000000 200030057458423 200000000000000 512 2153 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200030057458423/200000000000000 : ℝ)) (X := (50031604306034764067/50000000000000000000 : ℝ)) (by norm_num) 2153 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9897309959338507/100000000000000000000 : ℝ) ≤ ((3548015037080170493/3549000000000000000 : ℝ)+2*(516088551851/354900000000000 : ℝ)*(11161/100000 : ℝ))^(2153/512 : ℝ) := by
    rw [show (3548015037080170493/3549000000000000000 : ℝ)+2*(516088551851/354900000000000 : ℝ)*(11161/100000 : ℝ)=(1250058836977181/1250000000000000 : ℝ) by norm_num, show 1+2*(9897309959338507/100000000000000000000 : ℝ)=(50009897309959338507/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31604306034764067/100000000000000000000 : ℝ)+(9897309959338507/100000000000000000000 : ℝ) ≤ ((3548015037080170493/3549000000000000000 : ℝ)+(516088551851/354900000000000 : ℝ)*((1471/10000 : ℝ)+(11161/100000 : ℝ)))^(2153/512 : ℝ) := by
    rw [show (3548015037080170493/3549000000000000000 : ℝ)+(516088551851/354900000000000 : ℝ)*((1471/10000 : ℝ)+(11161/100000 : ℝ))=(10000986784369299/10000000000000000 : ℝ) by norm_num, show 1+(31604306034764067/100000000000000000000 : ℝ)+(9897309959338507/100000000000000000000 : ℝ)=(50020750807997051287/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31604306034764067/100000000000000000000 : ℝ) ≤ ((3548015037080170493/3549000000000000000 : ℝ)+2*(516088551851/354900000000000 : ℝ)*(1471/10000 : ℝ))^(2153/512 : ℝ) := by
    rw [show (3548015037080170493/3549000000000000000 : ℝ)+2*(516088551851/354900000000000 : ℝ)*(1471/10000 : ℝ)=(200030057458423/200000000000000 : ℝ) by norm_num, show 1+2*(31604306034764067/100000000000000000000 : ℝ)=(50031604306034764067/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3548015037080170493/3549000000000000000 : ℝ)*(X 1 0+X 2 0)+(516088551851/354900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (11161/100000 : ℝ)) (hi := (1471/10000 : ℝ)) (c := (3548015037080170493/3549000000000000000 : ℝ)) (alpha := (516088551851/354900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3548015037080170493/3549000000000000000 : ℝ)*(X 0 1+X 2 1)+(516088551851/354900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (11161/100000 : ℝ)) (hi := (1471/10000 : ℝ)) (c := (3548015037080170493/3549000000000000000 : ℝ)) (alpha := (516088551851/354900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3548015037080170493/3549000000000000000 : ℝ)*(X 0 2+X 1 2)+(516088551851/354900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2153/512 : ℝ)) (lo := (11161/100000 : ℝ)) (hi := (1471/10000 : ℝ)) (c := (3548015037080170493/3549000000000000000 : ℝ)) (alpha := (516088551851/354900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2039662099/10000000000 : ℝ)*X 0 0+(5412397021/10000000000 : ℝ)*X 0 1+(262240537/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674448987/5000000000 : ℝ)*X 1 0+(-2125044271/10000000000 : ℝ)*X 1 1+(209792431/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348898863/10000000000 : ℝ)*X 2 0+(5244810213/10000000000 : ℝ)*X 2 1+(-2125043829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((865063337/2000000000 : ℝ)*X 0 0+(519101143/1250000000 : ℝ)*X 0 1+(563061301/1250000000 : ℝ)*X 0 2+(865063337/2000000000 : ℝ)*X 1 0+(519101143/1250000000 : ℝ)*X 1 1+(563061301/1250000000 : ℝ)*X 1 2+(865063337/2000000000 : ℝ)*X 2 0+(519101143/1250000000 : ℝ)*X 2 1+(563061301/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-127479649/625000000 : ℝ)*X 0 0+(5245410483/10000000000 : ℝ)*X 0 1+(5411794051/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652853621/5000000000 : ℝ)*X 1 0+(-979030187/5000000000 : ℝ)*X 1 1+(2705896999/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663213397/1250000000 : ℝ)*X 2 0+(5411794057/10000000000 : ℝ)*X 2 1+(-1958060383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((173013683/400000000 : ℝ)*X 0 0+(562904001/1250000000 : ℝ)*X 0 1+(4154074029/10000000000 : ℝ)*X 0 2+(173013683/400000000 : ℝ)*X 1 0+(562904001/1250000000 : ℝ)*X 1 1+(4154074029/10000000000 : ℝ)*X 1 2+(173013683/400000000 : ℝ)*X 2 0+(562904001/1250000000 : ℝ)*X 2 1+(4154074029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1347_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3752590058434239539858251/1137500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26033629/25000000000000 : ℝ)*(base23) + (309511073/100000000000000 : ℝ)*(lower2) + (32366441/100000000000000 : ℝ)*(upper3) + (8833229/5000000000000 : ℝ)*(upper4) + (1101318602454797/25000000000000 : ℝ)*(major0) + (1101318602454797/25000000000000 : ℝ)*(major1) + (1101318602454797/25000000000000 : ℝ)*(major2) + (1491766297694413/25000000000000 : ℝ)*(sp0) + (745883062897309/12500000000000 : ℝ)*(sp1) + (5967067039406593/100000000000000 : ℝ)*(sp2) + (1421738035068581/50000000000000 : ℝ)*(sp3) + (372437877/5000000000000 : ℝ)*(sp4) + (101704459/1250000000000 : ℝ)*(sp5) + (5495994083/100000000000000 : ℝ)*(sp6) + (1421738035068581/50000000000000 : ℝ)*(f.failure) + (745884079941899/12500000000000 : ℝ)*(f.sum) + (28383953864101/8872500000000000000000000000 : ℝ)*base66 + (1299748023525825079/88725000000000000000000000000000 : ℝ)*base68 + (1585153570688925079/88725000000000000000000000000000 : ℝ)*base70 + (1630351045870875079/88725000000000000000000000000000 : ℝ)*base72 + (2486403721583/4436250000000000000000000000 : ℝ)*base74 + (1949070278980425079/88725000000000000000000000000000 : ℝ)*base76 + (1513097533497150079/88725000000000000000000000000000 : ℝ)*base78 + (1487226834572625079/88725000000000000000000000000000 : ℝ)*base80 + (32655451091519/8872500000000000000000000000 : ℝ)*base81 + (9688929/625000000000000000000 : ℝ)*base89 + (9688929/625000000000000000000 : ℝ)*base91 + (9688929/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (941975409191047099786779/295750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (602650529/100000000000000 : ℝ)*(base19) + (558161823/100000000000000 : ℝ)*(base23) + (90956721/50000000000000 : ℝ)*(lower1) + (43212159/100000000000000 : ℝ)*(upper3) + (21114093/100000000000000 : ℝ)*(lower4) + (43665337/50000000000000 : ℝ)*(upper5) + (22185563486397/500000000000 : ℝ)*(major0) + (22185563486397/500000000000 : ℝ)*(major1) + (22185563486397/500000000000 : ℝ)*(major2) + (584754097/50000000000000 : ℝ)*(sp1) + (751274816606411/12500000000000 : ℝ)*(sp4) + (1202039352138513/20000000000000 : ℝ)*(sp5) + (3005098987344733/50000000000000 : ℝ)*(sp6) + (8950083611061/312500000000 : ℝ)*(sp7) + (8950083611061/312500000000 : ℝ)*(f.failure) + (751274816606411/12500000000000 : ℝ)*(f.sum) + (72871555537/147875000000000000000000000 : ℝ)*base65 + (5280959296761907/591500000000000000000000000000 : ℝ)*base67 + (802798908854093/591500000000000000000000000000 : ℝ)*base70 + (3815606522148907/591500000000000000000000000000 : ℝ)*base71 + (933478302863/295750000000000000000000000 : ℝ)*base73 + (2470486655967907/591500000000000000000000000000 : ℝ)*base75 + (1681028927453907/591500000000000000000000000000 : ℝ)*base77 + (2150677140645093/591500000000000000000000000000 : ℝ)*base80 + (445997867103/591500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (55251/3906250000000000000 : ℝ)*base90 + (55251/3906250000000000000 : ℝ)*base92 + (55251/3906250000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1347_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11161/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5581/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1347_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1347_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5581/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1347_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1347_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1347_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2153/512 : ℝ) ≤ p) (hpb : p ≤ (4307/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19365709/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5581/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1347_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
