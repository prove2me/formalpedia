-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_w1012_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:02:03.601308+00:00
-- url     : https://prove2.me/submissions/5cf80617-4131-4b44-809e-302f9951caef

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
theorem support_rectangle_w1012_s2_0 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2208251749/10000000000 : ℝ)*x 0 + (110736337/200000000 : ℝ)*x 1 + (642047709/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2208251749/10000000000 : ℝ)^8205 ≤ (2672328042041/20000000000000 : ℝ)^6157 := by
    have hnat : (2208251749 : ℕ)^8205*20000000000000^6157 ≤ 2672328042041^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208251749 10000000000 2672328042041 20000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110736337/200000000 : ℝ)^8205 ≤ (45484236138773/100000000000000 : ℝ)^6157 := by
    have hnat : (110736337 : ℕ)^8205*100000000000000^6157 ≤ 45484236138773^6157*200000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110736337 200000000 45484236138773 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (642047709/1250000000 : ℝ)^8205 ≤ (10288530908987/25000000000000 : ℝ)^6157 := by
    have hnat : (642047709 : ℕ)^8205*25000000000000^6157 ≤ 10288530908987^6157*1250000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642047709 1250000000 10288530908987 25000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2208251749/10000000000 : ℝ), (110736337/200000000 : ℝ), (642047709/1250000000 : ℝ)] ![(2672328042041/20000000000000 : ℝ), (45484236138773/100000000000000 : ℝ), (10288530908987/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2208251749/10000000000 : ℝ)|^8205 ≤ (2672328042041/20000000000000 : ℝ)^6157
        have hw : |(-2208251749/10000000000 : ℝ)|=(2208251749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110736337/200000000 : ℝ)|^8205 ≤ (45484236138773/100000000000000 : ℝ)^6157
        have hw : |(110736337/200000000 : ℝ)|=(110736337/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(642047709/1250000000 : ℝ)|^8205 ≤ (10288530908987/25000000000000 : ℝ)^6157
        have hw : |(642047709/1250000000 : ℝ)|=(642047709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_s2_1 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (8405507/15625000 : ℝ)*x 0 + (-2417551399/10000000000 : ℝ)*x 1 + (2568191379/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8405507/15625000 : ℝ)^8205 ≤ (43770484604241/100000000000000 : ℝ)^6157 := by
    have hnat : (8405507 : ℕ)^8205*100000000000000^6157 ≤ 43770484604241^6157*15625000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8405507 15625000 43770484604241 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2417551399/10000000000 : ℝ)^8205 ≤ (7537690072357/50000000000000 : ℝ)^6157 := by
    have hnat : (2417551399 : ℕ)^8205*50000000000000^6157 ≤ 7537690072357^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417551399 10000000000 7537690072357 50000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2568191379/5000000000 : ℝ)^8205 ≤ (8230827046321/20000000000000 : ℝ)^6157 := by
    have hnat : (2568191379 : ℕ)^8205*20000000000000^6157 ≤ 8230827046321^6157*5000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568191379 5000000000 8230827046321 20000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8405507/15625000 : ℝ), (-2417551399/10000000000 : ℝ), (2568191379/5000000000 : ℝ)] ![(43770484604241/100000000000000 : ℝ), (7537690072357/50000000000000 : ℝ), (8230827046321/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8405507/15625000 : ℝ)|^8205 ≤ (43770484604241/100000000000000 : ℝ)^6157
        have hw : |(8405507/15625000 : ℝ)|=(8405507/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2417551399/10000000000 : ℝ)|^8205 ≤ (7537690072357/50000000000000 : ℝ)^6157
        have hw : |(-2417551399/10000000000 : ℝ)|=(2417551399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2568191379/5000000000 : ℝ)|^8205 ≤ (8230827046321/20000000000000 : ℝ)^6157
        have hw : |(2568191379/5000000000 : ℝ)|=(2568191379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_s2_2 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5379524819/10000000000 : ℝ)*x 0 + (5136381691/10000000000 : ℝ)*x 1 + (-2417552329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379524819/10000000000 : ℝ)^8205 ≤ (43770488279997/100000000000000 : ℝ)^6157 := by
    have hnat : (5379524819 : ℕ)^8205*100000000000000^6157 ≤ 43770488279997^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379524819 10000000000 43770488279997 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136381691/10000000000 : ℝ)^8205 ≤ (41154123838819/100000000000000 : ℝ)^6157 := by
    have hnat : (5136381691 : ℕ)^8205*100000000000000^6157 ≤ 41154123838819^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136381691 10000000000 41154123838819 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2417552329/10000000000 : ℝ)^8205 ≤ (1884423484129/12500000000000 : ℝ)^6157 := by
    have hnat : (2417552329 : ℕ)^8205*12500000000000^6157 ≤ 1884423484129^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417552329 10000000000 1884423484129 12500000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379524819/10000000000 : ℝ), (5136381691/10000000000 : ℝ), (-2417552329/10000000000 : ℝ)] ![(43770488279997/100000000000000 : ℝ), (41154123838819/100000000000000 : ℝ), (1884423484129/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379524819/10000000000 : ℝ)|^8205 ≤ (43770488279997/100000000000000 : ℝ)^6157
        have hw : |(5379524819/10000000000 : ℝ)|=(5379524819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136381691/10000000000 : ℝ)|^8205 ≤ (41154123838819/100000000000000 : ℝ)^6157
        have hw : |(5136381691/10000000000 : ℝ)|=(5136381691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2417552329/10000000000 : ℝ)|^8205 ≤ (1884423484129/12500000000000 : ℝ)^6157
        have hw : |(-2417552329/10000000000 : ℝ)|=(2417552329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_s2_3 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4369445877/10000000000 : ℝ)*x 0 + (499857751/1250000000 : ℝ)*x 1 + (238763039/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369445877/10000000000 : ℝ)^8205 ≤ (6635162314673/20000000000000 : ℝ)^6157 := by
    have hnat : (4369445877 : ℕ)^8205*20000000000000^6157 ≤ 6635162314673^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369445877 10000000000 6635162314673 20000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499857751/1250000000 : ℝ)^8205 ≤ (1179203359949/4000000000000 : ℝ)^6157 := by
    have hnat : (499857751 : ℕ)^8205*4000000000000^6157 ≤ 1179203359949^6157*1250000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499857751 1250000000 1179203359949 4000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238763039/500000000 : ℝ)^8205 ≤ (9336026103311/25000000000000 : ℝ)^6157 := by
    have hnat : (238763039 : ℕ)^8205*25000000000000^6157 ≤ 9336026103311^6157*500000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238763039 500000000 9336026103311 25000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369445877/10000000000 : ℝ), (499857751/1250000000 : ℝ), (238763039/500000000 : ℝ)] ![(6635162314673/20000000000000 : ℝ), (1179203359949/4000000000000 : ℝ), (9336026103311/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369445877/10000000000 : ℝ)|^8205 ≤ (6635162314673/20000000000000 : ℝ)^6157
        have hw : |(4369445877/10000000000 : ℝ)|=(4369445877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(499857751/1250000000 : ℝ)|^8205 ≤ (1179203359949/4000000000000 : ℝ)^6157
        have hw : |(499857751/1250000000 : ℝ)|=(499857751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(238763039/500000000 : ℝ)|^8205 ≤ (9336026103311/25000000000000 : ℝ)^6157
        have hw : |(238763039/500000000 : ℝ)|=(238763039/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_s2_4 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2208397093/10000000000 : ℝ)*x 0 + (321212429/625000000 : ℝ)*x 1 + (5533766443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2208397093/10000000000 : ℝ)^8205 ≤ (835175762273/6250000000000 : ℝ)^6157 := by
    have hnat : (2208397093 : ℕ)^8205*6250000000000^6157 ≤ 835175762273^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208397093 10000000000 835175762273 6250000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321212429/625000000 : ℝ)^8205 ≤ (41186342547963/100000000000000 : ℝ)^6157 := by
    have hnat : (321212429 : ℕ)^8205*100000000000000^6157 ≤ 41186342547963^6157*625000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321212429 625000000 41186342547963 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5533766443/10000000000 : ℝ)^8205 ≤ (45450845235457/100000000000000 : ℝ)^6157 := by
    have hnat : (5533766443 : ℕ)^8205*100000000000000^6157 ≤ 45450845235457^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5533766443 10000000000 45450845235457 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2208397093/10000000000 : ℝ), (321212429/625000000 : ℝ), (5533766443/10000000000 : ℝ)] ![(835175762273/6250000000000 : ℝ), (41186342547963/100000000000000 : ℝ), (45450845235457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2208397093/10000000000 : ℝ)|^8205 ≤ (835175762273/6250000000000 : ℝ)^6157
        have hw : |(-2208397093/10000000000 : ℝ)|=(2208397093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(321212429/625000000 : ℝ)|^8205 ≤ (41186342547963/100000000000000 : ℝ)^6157
        have hw : |(321212429/625000000 : ℝ)|=(321212429/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5533766443/10000000000 : ℝ)|^8205 ≤ (45450845235457/100000000000000 : ℝ)^6157
        have hw : |(5533766443/10000000000 : ℝ)|=(5533766443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_s2_5 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (659855331/1250000000 : ℝ)*x 0 + (-1010084069/5000000000 : ℝ)*x 1 + (69172081/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659855331/1250000000 : ℝ)^8205 ≤ (42682210291281/100000000000000 : ℝ)^6157 := by
    have hnat : (659855331 : ℕ)^8205*100000000000000^6157 ≤ 42682210291281^6157*1250000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659855331 1250000000 42682210291281 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1010084069/5000000000 : ℝ)^8205 ≤ (1483368007999/12500000000000 : ℝ)^6157 := by
    have hnat : (1010084069 : ℕ)^8205*12500000000000^6157 ≤ 1483368007999^6157*5000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010084069 5000000000 1483368007999 12500000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69172081/125000000 : ℝ)^8205 ≤ (9090169128087/20000000000000 : ℝ)^6157 := by
    have hnat : (69172081 : ℕ)^8205*20000000000000^6157 ≤ 9090169128087^6157*125000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69172081 125000000 9090169128087 20000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659855331/1250000000 : ℝ), (-1010084069/5000000000 : ℝ), (69172081/125000000 : ℝ)] ![(42682210291281/100000000000000 : ℝ), (1483368007999/12500000000000 : ℝ), (9090169128087/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659855331/1250000000 : ℝ)|^8205 ≤ (42682210291281/100000000000000 : ℝ)^6157
        have hw : |(659855331/1250000000 : ℝ)|=(659855331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1010084069/5000000000 : ℝ)|^8205 ≤ (1483368007999/12500000000000 : ℝ)^6157
        have hw : |(-1010084069/5000000000 : ℝ)|=(1010084069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(69172081/125000000 : ℝ)|^8205 ≤ (9090169128087/20000000000000 : ℝ)^6157
        have hw : |(69172081/125000000 : ℝ)|=(69172081/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_s2_6 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2639421411/5000000000 : ℝ)*x 0 + (5533766489/10000000000 : ℝ)*x 1 + (-505041971/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639421411/5000000000 : ℝ)^8205 ≤ (42682212166133/100000000000000 : ℝ)^6157 := by
    have hnat : (2639421411 : ℕ)^8205*100000000000000^6157 ≤ 42682212166133^6157*5000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639421411 5000000000 42682212166133 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5533766489/10000000000 : ℝ)^8205 ≤ (710169464671/1562500000000 : ℝ)^6157 := by
    have hnat : (5533766489 : ℕ)^8205*1562500000000^6157 ≤ 710169464671^6157*10000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5533766489 10000000000 710169464671 1562500000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (505041971/2500000000 : ℝ)^8205 ≤ (5933471037817/50000000000000 : ℝ)^6157 := by
    have hnat : (505041971 : ℕ)^8205*50000000000000^6157 ≤ 5933471037817^6157*2500000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505041971 2500000000 5933471037817 50000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639421411/5000000000 : ℝ), (5533766489/10000000000 : ℝ), (-505041971/2500000000 : ℝ)] ![(42682212166133/100000000000000 : ℝ), (710169464671/1562500000000 : ℝ), (5933471037817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639421411/5000000000 : ℝ)|^8205 ≤ (42682212166133/100000000000000 : ℝ)^6157
        have hw : |(2639421411/5000000000 : ℝ)|=(2639421411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5533766489/10000000000 : ℝ)|^8205 ≤ (710169464671/1562500000000 : ℝ)^6157
        have hw : |(5533766489/10000000000 : ℝ)|=(5533766489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-505041971/2500000000 : ℝ)|^8205 ≤ (5933471037817/50000000000000 : ℝ)^6157
        have hw : |(-505041971/2500000000 : ℝ)|=(505041971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1012_s2_7 (p : ℝ) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184864963/5000000000 : ℝ)*x 0 + (149043943/312500000 : ℝ)*x 1 + (500597161/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184864963/5000000000 : ℝ)^8205 ≤ (6635737135611/20000000000000 : ℝ)^6157 := by
    have hnat : (2184864963 : ℕ)^8205*20000000000000^6157 ≤ 6635737135611^6157*5000000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184864963 5000000000 6635737135611 20000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149043943/312500000 : ℝ)^8205 ≤ (7456620503739/20000000000000 : ℝ)^6157 := by
    have hnat : (149043943 : ℕ)^8205*20000000000000^6157 ≤ 7456620503739^6157*312500000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149043943 312500000 7456620503739 20000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (500597161/1250000000 : ℝ)^8205 ≤ (29538211791743/100000000000000 : ℝ)^6157 := by
    have hnat : (500597161 : ℕ)^8205*100000000000000^6157 ≤ 29538211791743^6157*1250000000^8205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500597161 1250000000 29538211791743 100000000000000 8205 6157 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8205/2048 : ℝ)) 8205 6157 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184864963/5000000000 : ℝ), (149043943/312500000 : ℝ), (500597161/1250000000 : ℝ)] ![(6635737135611/20000000000000 : ℝ), (7456620503739/20000000000000 : ℝ), (29538211791743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184864963/5000000000 : ℝ)|^8205 ≤ (6635737135611/20000000000000 : ℝ)^6157
        have hw : |(2184864963/5000000000 : ℝ)|=(2184864963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(149043943/312500000 : ℝ)|^8205 ≤ (7456620503739/20000000000000 : ℝ)^6157
        have hw : |(149043943/312500000 : ℝ)|=(149043943/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(500597161/1250000000 : ℝ)|^8205 ≤ (29538211791743/100000000000000 : ℝ)^6157
        have hw : |(500597161/1250000000 : ℝ)|=(500597161/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1012_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29388737/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1229/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (8451/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1057/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (21031/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1229/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (21031/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1229/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (21031/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1229/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (21031/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1229/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (21031/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1229/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (21031/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1229/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1229/25000 : ℝ) ^ (2051/512 : ℝ) ≤ (114765447869507/20000000000000000000 : ℝ) := by
    have hpowers : (1229/25000 : ℝ)^2051 ≤ (114765447869507/20000000000000000000 : ℝ)^512 := by
      have hnat : (1229 : ℕ)^2051*20000000000000000000^512 ≤ 114765447869507^512*25000^2051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1229 25000 114765447869507 20000000000000000000 2051 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1229/25000 : ℝ)) (X := (114765447869507/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2051 512 (by norm_num) hpowers
    exact h
  have hpowhi : (21031/100000 : ℝ) ^ (2051/512 : ℝ) ≤ (193852798920087907/100000000000000000000 : ℝ) := by
    have hpowers : (21031/100000 : ℝ)^2051 ≤ (193852798920087907/100000000000000000000 : ℝ)^512 := by
      have hnat : (21031 : ℕ)^2051*100000000000000000000^512 ≤ 193852798920087907^512*100000^2051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21031 100000 193852798920087907 100000000000000000000 2051 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21031/100000 : ℝ)) (X := (193852798920087907/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2051 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000114765447869507/10000000000000000000 : ℝ) ≤ (10000028649271723/10000000000000000 : ℝ) ^ (2051/512 : ℝ) := by
    have hpowers : (10000114765447869507/10000000000000000000 : ℝ)^512 ≤ (10000028649271723/10000000000000000 : ℝ)^2051 := by
      have hnat : (10000114765447869507 : ℕ)^512*10000000000000000^2051 ≤ 10000028649271723^2051*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000114765447869507 10000000000000000000 10000028649271723 10000000000000000 512 2051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000028649271723/10000000000000000 : ℝ)) (X := (10000114765447869507/10000000000000000000 : ℝ)) (by norm_num) 2051 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50097213313079717721/50000000000000000000 : ℝ) ≤ (10004850019511509/10000000000000000 : ℝ) ^ (2051/512 : ℝ) := by
    have hpowers : (50097213313079717721/50000000000000000000 : ℝ)^512 ≤ (10004850019511509/10000000000000000 : ℝ)^2051 := by
      have hnat : (50097213313079717721 : ℕ)^512*10000000000000000^2051 ≤ 10004850019511509^2051*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50097213313079717721 50000000000000000000 10004850019511509 10000000000000000 512 2051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004850019511509/10000000000000000 : ℝ)) (X := (50097213313079717721/50000000000000000000 : ℝ)) (by norm_num) 2051 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50193852798920087907/50000000000000000000 : ℝ) ≤ (2001934277950259/2000000000000000 : ℝ) ^ (2051/512 : ℝ) := by
    have hpowers : (50193852798920087907/50000000000000000000 : ℝ)^512 ≤ (2001934277950259/2000000000000000 : ℝ)^2051 := by
      have hnat : (50193852798920087907 : ℕ)^512*2000000000000000^2051 ≤ 2001934277950259^2051*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50193852798920087907 50000000000000000000 2001934277950259 2000000000000000 512 2051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001934277950259/2000000000000000 : ℝ)) (X := (50193852798920087907/50000000000000000000 : ℝ)) (by norm_num) 2051 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(114765447869507/20000000000000000000 : ℝ) ≤ ((161103057970816240193/161150000000000000000 : ℝ)+2*(2410685119893/805750000000000 : ℝ)*(1229/25000 : ℝ))^(2051/512 : ℝ) := by
    rw [show (161103057970816240193/161150000000000000000 : ℝ)+2*(2410685119893/805750000000000 : ℝ)*(1229/25000 : ℝ)=(10000028649271723/10000000000000000 : ℝ) by norm_num, show 1+2*(114765447869507/20000000000000000000 : ℝ)=(10000114765447869507/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(193852798920087907/100000000000000000000 : ℝ)+(114765447869507/20000000000000000000 : ℝ) ≤ ((161103057970816240193/161150000000000000000 : ℝ)+(2410685119893/805750000000000 : ℝ)*((21031/100000 : ℝ)+(1229/25000 : ℝ)))^(2051/512 : ℝ) := by
    rw [show (161103057970816240193/161150000000000000000 : ℝ)+(2410685119893/805750000000000 : ℝ)*((21031/100000 : ℝ)+(1229/25000 : ℝ))=(10004850019511509/10000000000000000 : ℝ) by norm_num, show 1+(193852798920087907/100000000000000000000 : ℝ)+(114765447869507/20000000000000000000 : ℝ)=(50097213313079717721/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(193852798920087907/100000000000000000000 : ℝ) ≤ ((161103057970816240193/161150000000000000000 : ℝ)+2*(2410685119893/805750000000000 : ℝ)*(21031/100000 : ℝ))^(2051/512 : ℝ) := by
    rw [show (161103057970816240193/161150000000000000000 : ℝ)+2*(2410685119893/805750000000000 : ℝ)*(21031/100000 : ℝ)=(2001934277950259/2000000000000000 : ℝ) by norm_num, show 1+2*(193852798920087907/100000000000000000000 : ℝ)=(50193852798920087907/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (161103057970816240193/161150000000000000000 : ℝ)*(X 1 0+X 2 0)+(2410685119893/805750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2051/512 : ℝ)) (lo := (1229/25000 : ℝ)) (hi := (21031/100000 : ℝ)) (c := (161103057970816240193/161150000000000000000 : ℝ)) (alpha := (2410685119893/805750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (161103057970816240193/161150000000000000000 : ℝ)*(X 0 1+X 2 1)+(2410685119893/805750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2051/512 : ℝ)) (lo := (1229/25000 : ℝ)) (hi := (21031/100000 : ℝ)) (c := (161103057970816240193/161150000000000000000 : ℝ)) (alpha := (2410685119893/805750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (161103057970816240193/161150000000000000000 : ℝ)*(X 0 2+X 1 2)+(2410685119893/805750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2051/512 : ℝ)) (lo := (1229/25000 : ℝ)) (hi := (21031/100000 : ℝ)) (c := (161103057970816240193/161150000000000000000 : ℝ)) (alpha := (2410685119893/805750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2208251749/10000000000 : ℝ)*X 0 0+(110736337/200000000 : ℝ)*X 0 1+(642047709/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((8405507/15625000 : ℝ)*X 1 0+(-2417551399/10000000000 : ℝ)*X 1 1+(2568191379/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5379524819/10000000000 : ℝ)*X 2 0+(5136381691/10000000000 : ℝ)*X 2 1+(-2417552329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4369445877/10000000000 : ℝ)*X 0 0+(499857751/1250000000 : ℝ)*X 0 1+(238763039/500000000 : ℝ)*X 0 2+(4369445877/10000000000 : ℝ)*X 1 0+(499857751/1250000000 : ℝ)*X 1 1+(238763039/500000000 : ℝ)*X 1 2+(4369445877/10000000000 : ℝ)*X 2 0+(499857751/1250000000 : ℝ)*X 2 1+(238763039/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2208397093/10000000000 : ℝ)*X 0 0+(321212429/625000000 : ℝ)*X 0 1+(5533766443/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((659855331/1250000000 : ℝ)*X 1 0+(-1010084069/5000000000 : ℝ)*X 1 1+(69172081/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639421411/5000000000 : ℝ)*X 2 0+(5533766489/10000000000 : ℝ)*X 2 1+(-505041971/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2184864963/5000000000 : ℝ)*X 0 0+(149043943/312500000 : ℝ)*X 0 1+(500597161/1250000000 : ℝ)*X 0 2+(2184864963/5000000000 : ℝ)*X 1 0+(149043943/312500000 : ℝ)*X 1 1+(500597161/1250000000 : ℝ)*X 1 2+(2184864963/5000000000 : ℝ)*X 2 0+(149043943/312500000 : ℝ)*X 2 1+(500597161/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1012_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (177172358142156513145101/40287500000000000000000000000 : ℝ) := by norm_num
    linear_combination (46966567/50000000000000 : ℝ)*(base19) + (87788133/20000000000000 : ℝ)*(base23) + (85591299/50000000000000 : ℝ)*(upper2) + (35121763/50000000000000 : ℝ)*(upper4) + (282628117/100000000000000 : ℝ)*(lower5) + (1892660685818981/100000000000000 : ℝ)*(major0) + (1892660685818981/100000000000000 : ℝ)*(major1) + (1892660685818981/100000000000000 : ℝ)*(major2) + (312161942634487/12500000000000 : ℝ)*(sp0) + (2497303421596377/100000000000000 : ℝ)*(sp1) + (1248651538294423/50000000000000 : ℝ)*(sp2) + (1288006868799903/100000000000000 : ℝ)*(sp3) + (1594890723/20000000000000 : ℝ)*(sp4) + (1084071853/10000000000000 : ℝ)*(sp7) + (1288017709518433/100000000000000 : ℝ)*(f.failure) + (2497303515529511/100000000000000 : ℝ)*(f.sum) + (48056364928083/40287500000000000000000000000 : ℝ)*base65 + (20602905302861103333/16115000000000000000000000000000000 : ℝ)*base67 + (27701856718533896667/16115000000000000000000000000000000 : ℝ)*base70 + (42907351167056103333/16115000000000000000000000000000000 : ℝ)*base71 + (239636975276491/80575000000000000000000000000 : ℝ)*base73 + (97570827606568896667/16115000000000000000000000000000000 : ℝ)*base76 + (24207754847053896667/16115000000000000000000000000000000 : ℝ)*base78 + (42137359871103333/16115000000000000000000000000000000 : ℝ)*base79 + (1217665684173/10071875000000000000000000000 : ℝ)*base82 + (4089121/2000000000000000000000 : ℝ)*base89 + (4089121/2000000000000000000000 : ℝ)*base91 + (4089121/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4717966643353654078557096603/2014375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (309510823/100000000000000 : ℝ)*(base19) + (1998671/400000000000 : ℝ)*(base23) + (26306133/50000000000000 : ℝ)*(upper3) + (32690261/100000000000000 : ℝ)*(lower4) + (55616429/100000000000000 : ℝ)*(upper5) + (480441222157819/25000000000000 : ℝ)*(major0) + (480441222157819/25000000000000 : ℝ)*(major1) + (480441222157819/25000000000000 : ℝ)*(major2) + (7471101/312500000000 : ℝ)*(sp1) + (236585751/5000000000000 : ℝ)*(sp2) + (633926406131243/25000000000000 : ℝ)*(sp4) + (253570292426183/10000000000000 : ℝ)*(sp5) + (2535700393142203/100000000000000 : ℝ)*(sp6) + (261564814933187/20000000000000 : ℝ)*(sp7) + (261564814933187/20000000000000 : ℝ)*(f.failure) + (633926406131243/25000000000000 : ℝ)*(f.sum) + (207315578244443/40287500000000000000000000000 : ℝ)*base65 + (23665539642349580933/4028750000000000000000000000000000 : ℝ)*base68 + (25617277683954580933/4028750000000000000000000000000000 : ℝ)*base70 + (12642653556957080933/4028750000000000000000000000000000 : ℝ)*base72 + (28488875549641/20143750000000000000000000000 : ℝ)*base74 + (69227861357919580933/4028750000000000000000000000000000 : ℝ)*base76 + (11343699171629580933/4028750000000000000000000000000000 : ℝ)*base78 + (33714459948870830933/4028750000000000000000000000000000 : ℝ)*base80 + (1846837615401/1258984375000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1314819/400000000000000000000 : ℝ)*base89 + (1314819/400000000000000000000 : ℝ)*base91 + (1314819/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1012_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29388737/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1229/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8451/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1057/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1012_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2051/512 : ℝ) ≤ p) (hpb : p ≤ (8205/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29388737/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1229/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8451/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1057/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_w1012_s2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
