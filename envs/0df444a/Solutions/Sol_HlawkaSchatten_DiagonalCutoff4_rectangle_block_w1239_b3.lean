-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1239_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:18:40.053354+00:00
-- url     : https://prove2.me/submissions/ad0bb43b-062e-4f00-b170-858ac31afd91

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
theorem support_rectangle_w1239_s9_0 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-265168753/1250000000 : ℝ)*x 0 + (5391204651/10000000000 : ℝ)*x 1 + (5267219183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265168753/1250000000 : ℝ)^527 ≤ (12899955722423/100000000000000 : ℝ)^399 := by
    have hnat : (265168753 : ℕ)^527*100000000000000^399 ≤ 12899955722423^399*1250000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265168753 1250000000 12899955722423 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391204651/10000000000 : ℝ)^527 ≤ (1381847484093/3125000000000 : ℝ)^399 := by
    have hnat : (5391204651 : ℕ)^527*3125000000000^399 ≤ 1381847484093^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391204651 10000000000 1381847484093 3125000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267219183/10000000000 : ℝ)^527 ≤ (42880924776313/100000000000000 : ℝ)^399 := by
    have hnat : (5267219183 : ℕ)^527*100000000000000^399 ≤ 42880924776313^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267219183 10000000000 42880924776313 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-265168753/1250000000 : ℝ), (5391204651/10000000000 : ℝ), (5267219183/10000000000 : ℝ)] ![(12899955722423/100000000000000 : ℝ), (1381847484093/3125000000000 : ℝ), (42880924776313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-265168753/1250000000 : ℝ)|^527 ≤ (12899955722423/100000000000000 : ℝ)^399
        have hw : |(-265168753/1250000000 : ℝ)|=(265168753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391204651/10000000000 : ℝ)|^527 ≤ (1381847484093/3125000000000 : ℝ)^399
        have hw : |(5391204651/10000000000 : ℝ)|=(5391204651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267219183/10000000000 : ℝ)|^527 ≤ (42880924776313/100000000000000 : ℝ)^399
        have hw : |(5267219183/10000000000 : ℝ)|=(5267219183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s9_1 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344311851/10000000000 : ℝ)*x 0 + (-436842787/2000000000 : ℝ)*x 1 + (5267219159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344311851/10000000000 : ℝ)^527 ≤ (43711824446237/100000000000000 : ℝ)^399 := by
    have hnat : (5344311851 : ℕ)^527*100000000000000^399 ≤ 43711824446237^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344311851 10000000000 43711824446237 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436842787/2000000000 : ℝ)^527 ≤ (13407251015061/100000000000000 : ℝ)^399 := by
    have hnat : (436842787 : ℕ)^527*100000000000000^399 ≤ 13407251015061^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436842787 2000000000 13407251015061 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267219159/10000000000 : ℝ)^527 ≤ (21440462259123/50000000000000 : ℝ)^399 := by
    have hnat : (5267219159 : ℕ)^527*50000000000000^399 ≤ 21440462259123^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267219159 10000000000 21440462259123 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344311851/10000000000 : ℝ), (-436842787/2000000000 : ℝ), (5267219159/10000000000 : ℝ)] ![(43711824446237/100000000000000 : ℝ), (13407251015061/100000000000000 : ℝ), (21440462259123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344311851/10000000000 : ℝ)|^527 ≤ (43711824446237/100000000000000 : ℝ)^399
        have hw : |(5344311851/10000000000 : ℝ)|=(5344311851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-436842787/2000000000 : ℝ)|^527 ≤ (13407251015061/100000000000000 : ℝ)^399
        have hw : |(-436842787/2000000000 : ℝ)|=(436842787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267219159/10000000000 : ℝ)|^527 ≤ (21440462259123/50000000000000 : ℝ)^399
        have hw : |(5267219159/10000000000 : ℝ)|=(5267219159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s9_2 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344311901/10000000000 : ℝ)*x 0 + (2633609567/5000000000 : ℝ)*x 1 + (-1092106951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344311901/10000000000 : ℝ)^527 ≤ (10927956246597/25000000000000 : ℝ)^399 := by
    have hnat : (5344311901 : ℕ)^527*25000000000000^399 ≤ 10927956246597^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344311901 10000000000 10927956246597 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633609567/5000000000 : ℝ)^527 ≤ (42880924249427/100000000000000 : ℝ)^399 := by
    have hnat : (2633609567 : ℕ)^527*100000000000000^399 ≤ 42880924249427^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633609567 5000000000 42880924249427 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092106951/5000000000 : ℝ)^527 ≤ (13407250747517/100000000000000 : ℝ)^399 := by
    have hnat : (1092106951 : ℕ)^527*100000000000000^399 ≤ 13407250747517^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092106951 5000000000 13407250747517 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344311901/10000000000 : ℝ), (2633609567/5000000000 : ℝ), (-1092106951/5000000000 : ℝ)] ![(10927956246597/25000000000000 : ℝ), (42880924249427/100000000000000 : ℝ), (13407250747517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344311901/10000000000 : ℝ)|^527 ≤ (10927956246597/25000000000000 : ℝ)^399
        have hw : |(5344311901/10000000000 : ℝ)|=(5344311901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633609567/5000000000 : ℝ)|^527 ≤ (42880924249427/100000000000000 : ℝ)^399
        have hw : |(2633609567/5000000000 : ℝ)|=(2633609567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1092106951/5000000000 : ℝ)|^527 ≤ (13407250747517/100000000000000 : ℝ)^399
        have hw : |(-1092106951/5000000000 : ℝ)|=(1092106951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s9_3 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (870237417/2000000000 : ℝ)*x 0 + (4227269221/10000000000 : ℝ)*x 1 + (447863713/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870237417/2000000000 : ℝ)^527 ≤ (16658749775013/50000000000000 : ℝ)^399 := by
    have hnat : (870237417 : ℕ)^527*50000000000000^399 ≤ 16658749775013^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870237417 2000000000 16658749775013 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227269221/10000000000 : ℝ)^527 ≤ (32070015961821/100000000000000 : ℝ)^399 := by
    have hnat : (4227269221 : ℕ)^527*100000000000000^399 ≤ 32070015961821^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227269221 10000000000 32070015961821 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447863713/1000000000 : ℝ)^527 ≤ (34612484473413/100000000000000 : ℝ)^399 := by
    have hnat : (447863713 : ℕ)^527*100000000000000^399 ≤ 34612484473413^399*1000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447863713 1000000000 34612484473413 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870237417/2000000000 : ℝ), (4227269221/10000000000 : ℝ), (447863713/1000000000 : ℝ)] ![(16658749775013/50000000000000 : ℝ), (32070015961821/100000000000000 : ℝ), (34612484473413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870237417/2000000000 : ℝ)|^527 ≤ (16658749775013/50000000000000 : ℝ)^399
        have hw : |(870237417/2000000000 : ℝ)|=(870237417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227269221/10000000000 : ℝ)|^527 ≤ (32070015961821/100000000000000 : ℝ)^399
        have hw : |(4227269221/10000000000 : ℝ)|=(4227269221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(447863713/1000000000 : ℝ)|^527 ≤ (34612484473413/100000000000000 : ℝ)^399
        have hw : |(447863713/1000000000 : ℝ)|=(447863713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s9_4 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2121354721/10000000000 : ℝ)*x 0 + (2633765851/5000000000 : ℝ)*x 1 + (5390890967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121354721/10000000000 : ℝ)^527 ≤ (1612499180983/12500000000000 : ℝ)^399 := by
    have hnat : (2121354721 : ℕ)^527*12500000000000^399 ≤ 1612499180983^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121354721 10000000000 1612499180983 12500000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633765851/5000000000 : ℝ)^527 ≤ (1340133914191/3125000000000 : ℝ)^399 := by
    have hnat : (2633765851 : ℕ)^527*3125000000000^399 ≤ 1340133914191^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633765851 5000000000 1340133914191 3125000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390890967/10000000000 : ℝ)^527 ≤ (44215721280253/100000000000000 : ℝ)^399 := by
    have hnat : (5390890967 : ℕ)^527*100000000000000^399 ≤ 44215721280253^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390890967 10000000000 44215721280253 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2121354721/10000000000 : ℝ), (2633765851/5000000000 : ℝ), (5390890967/10000000000 : ℝ)] ![(1612499180983/12500000000000 : ℝ), (1340133914191/3125000000000 : ℝ), (44215721280253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2121354721/10000000000 : ℝ)|^527 ≤ (1612499180983/12500000000000 : ℝ)^399
        have hw : |(-2121354721/10000000000 : ℝ)|=(2121354721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633765851/5000000000 : ℝ)|^527 ≤ (1340133914191/3125000000000 : ℝ)^399
        have hw : |(2633765851/5000000000 : ℝ)|=(2633765851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390890967/10000000000 : ℝ)|^527 ≤ (44215721280253/100000000000000 : ℝ)^399
        have hw : |(5390890967/10000000000 : ℝ)|=(5390890967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_s9_5 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1087799103/2500000000 : ℝ)*x 0 + (2239001907/5000000000 : ℝ)*x 1 + (2113952469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087799103/2500000000 : ℝ)^527 ≤ (6663518775773/20000000000000 : ℝ)^399 := by
    have hnat : (1087799103 : ℕ)^527*20000000000000^399 ≤ 6663518775773^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087799103 2500000000 6663518775773 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2239001907/5000000000 : ℝ)^527 ≤ (692120399383/2000000000000 : ℝ)^399 := by
    have hnat : (2239001907 : ℕ)^527*2000000000000^399 ≤ 692120399383^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239001907 5000000000 692120399383 2000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113952469/5000000000 : ℝ)^527 ≤ (32076386135729/100000000000000 : ℝ)^399 := by
    have hnat : (2113952469 : ℕ)^527*100000000000000^399 ≤ 32076386135729^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113952469 5000000000 32076386135729 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087799103/2500000000 : ℝ), (2239001907/5000000000 : ℝ), (2113952469/5000000000 : ℝ)] ![(6663518775773/20000000000000 : ℝ), (692120399383/2000000000000 : ℝ), (32076386135729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087799103/2500000000 : ℝ)|^527 ≤ (6663518775773/20000000000000 : ℝ)^399
        have hw : |(1087799103/2500000000 : ℝ)|=(1087799103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2239001907/5000000000 : ℝ)|^527 ≤ (692120399383/2000000000000 : ℝ)^399
        have hw : |(2239001907/5000000000 : ℝ)|=(2239001907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113952469/5000000000 : ℝ)|^527 ≤ (32076386135729/100000000000000 : ℝ)^399
        have hw : |(2113952469/5000000000 : ℝ)|=(2113952469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1239_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (2869/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7051/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7051/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (459/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7051/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (459/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7051/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (459/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7051/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (459/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7051/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (459/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7051/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (459/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (459/4000 : ℝ) ^ (8431/2048 : ℝ) ≤ (2693485528272009/20000000000000000000 : ℝ) := by
    have hpowers : (459/4000 : ℝ)^8431 ≤ (2693485528272009/20000000000000000000 : ℝ)^2048 := by
      have hnat : (459 : ℕ)^8431*20000000000000000000^2048 ≤ 2693485528272009^2048*4000^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        459 4000 2693485528272009 20000000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (459/4000 : ℝ)) (X := (2693485528272009/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7051/50000 : ℝ) ^ (8431/2048 : ℝ) ≤ (15733109642225741/50000000000000000000 : ℝ) := by
    have hpowers : (7051/50000 : ℝ)^8431 ≤ (15733109642225741/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7051 : ℕ)^8431*50000000000000000000^2048 ≤ 15733109642225741^2048*50000^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7051 50000 15733109642225741 50000000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7051/50000 : ℝ)) (X := (15733109642225741/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002693485528272009/10000000000000000000 : ℝ) ≤ (5000327108054333/5000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (10002693485528272009/10000000000000000000 : ℝ)^2048 ≤ (5000327108054333/5000000000000000 : ℝ)^8431 := by
      have hnat : (10002693485528272009 : ℕ)^2048*5000000000000000^8431 ≤ 5000327108054333^8431*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002693485528272009 10000000000000000000 5000327108054333 5000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000327108054333/5000000000000000 : ℝ)) (X := (10002693485528272009/10000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044933646925811527/100000000000000000000 : ℝ) ≤ (1953338146749/1953125000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (100044933646925811527/100000000000000000000 : ℝ)^2048 ≤ (1953338146749/1953125000000 : ℝ)^8431 := by
      have hnat : (100044933646925811527 : ℕ)^2048*1953125000000^8431 ≤ 1953338146749^8431*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044933646925811527 100000000000000000000 1953338146749 1953125000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1953338146749/1953125000000 : ℝ)) (X := (100044933646925811527/100000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015733109642225741/25000000000000000000 : ℝ) ≤ (5000764203300547/5000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (25015733109642225741/25000000000000000000 : ℝ)^2048 ≤ (5000764203300547/5000000000000000 : ℝ)^8431 := by
      have hnat : (25015733109642225741 : ℕ)^2048*5000000000000000^8431 ≤ 5000764203300547^8431*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015733109642225741 25000000000000000000 5000764203300547 5000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000764203300547/5000000000000000 : ℝ)) (X := (25015733109642225741/25000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2693485528272009/20000000000000000000 : ℝ) ≤ ((13130843644908427141/13135000000000000000 : ℝ)+2*(218547623107/131350000000000 : ℝ)*(459/4000 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (13130843644908427141/13135000000000000000 : ℝ)+2*(218547623107/131350000000000 : ℝ)*(459/4000 : ℝ)=(5000327108054333/5000000000000000 : ℝ) by norm_num, show 1+2*(2693485528272009/20000000000000000000 : ℝ)=(10002693485528272009/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15733109642225741/50000000000000000000 : ℝ)+(2693485528272009/20000000000000000000 : ℝ) ≤ ((13130843644908427141/13135000000000000000 : ℝ)+(218547623107/131350000000000 : ℝ)*((7051/50000 : ℝ)+(459/4000 : ℝ)))^(8431/2048 : ℝ) := by
    rw [show (13130843644908427141/13135000000000000000 : ℝ)+(218547623107/131350000000000 : ℝ)*((7051/50000 : ℝ)+(459/4000 : ℝ))=(1953338146749/1953125000000 : ℝ) by norm_num, show 1+(15733109642225741/50000000000000000000 : ℝ)+(2693485528272009/20000000000000000000 : ℝ)=(100044933646925811527/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15733109642225741/50000000000000000000 : ℝ) ≤ ((13130843644908427141/13135000000000000000 : ℝ)+2*(218547623107/131350000000000 : ℝ)*(7051/50000 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (13130843644908427141/13135000000000000000 : ℝ)+2*(218547623107/131350000000000 : ℝ)*(7051/50000 : ℝ)=(5000764203300547/5000000000000000 : ℝ) by norm_num, show 1+2*(15733109642225741/50000000000000000000 : ℝ)=(25015733109642225741/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13130843644908427141/13135000000000000000 : ℝ)*(X 1 0+X 2 0)+(218547623107/131350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (459/4000 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (13130843644908427141/13135000000000000000 : ℝ)) (alpha := (218547623107/131350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13130843644908427141/13135000000000000000 : ℝ)*(X 0 1+X 2 1)+(218547623107/131350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (459/4000 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (13130843644908427141/13135000000000000000 : ℝ)) (alpha := (218547623107/131350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13130843644908427141/13135000000000000000 : ℝ)*(X 0 2+X 1 2)+(218547623107/131350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (459/4000 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (13130843644908427141/13135000000000000000 : ℝ)) (alpha := (218547623107/131350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-265168753/1250000000 : ℝ)*X 0 0+(5391204651/10000000000 : ℝ)*X 0 1+(5267219183/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344311851/10000000000 : ℝ)*X 1 0+(-436842787/2000000000 : ℝ)*X 1 1+(5267219159/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344311901/10000000000 : ℝ)*X 2 0+(2633609567/5000000000 : ℝ)*X 2 1+(-1092106951/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870237417/2000000000 : ℝ)*X 0 0+(4227269221/10000000000 : ℝ)*X 0 1+(447863713/1000000000 : ℝ)*X 0 2+(870237417/2000000000 : ℝ)*X 1 0+(4227269221/10000000000 : ℝ)*X 1 1+(447863713/1000000000 : ℝ)*X 1 2+(870237417/2000000000 : ℝ)*X 2 0+(4227269221/10000000000 : ℝ)*X 2 1+(447863713/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2121354721/10000000000 : ℝ)*X 0 0+(2633765851/5000000000 : ℝ)*X 0 1+(5390890967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1087799103/2500000000 : ℝ)*X 0 0+(2239001907/5000000000 : ℝ)*X 0 1+(2113952469/5000000000 : ℝ)*X 0 2+(1087799103/2500000000 : ℝ)*X 1 0+(2239001907/5000000000 : ℝ)*X 1 1+(2113952469/5000000000 : ℝ)*X 1 2+(1087799103/2500000000 : ℝ)*X 2 0+(2239001907/5000000000 : ℝ)*X 2 1+(2113952469/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1635748365086699668199196417/656750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (354804733/100000000000000 : ℝ)*(base19) + (77035313/20000000000000 : ℝ)*(base23) + (12047867/50000000000000 : ℝ)*(lower2) + (4391449/20000000000000 : ℝ)*(upper3) + (7143121/12500000000000 : ℝ)*(upper5) + (6021862381618079/100000000000000 : ℝ)*(major0) + (6021862381618079/100000000000000 : ℝ)*(major1) + (6021862381618079/100000000000000 : ℝ)*(major2) + (8065468229702481/100000000000000 : ℝ)*(sp0) + (8065478112229677/100000000000000 : ℝ)*(sp1) + (2016369520464461/25000000000000 : ℝ)*(sp2) + (994559851927827/25000000000000 : ℝ)*(sp3) + (1023733193/10000000000000 : ℝ)*(sp4) + (6805468053/100000000000000 : ℝ)*(sp5) + (24864038832371/625000000000 : ℝ)*(f.failure) + (806547846703441/10000000000000 : ℝ)*(f.sum) + (1163690130551/205234375000000000000000000 : ℝ)*base66 + (3783839991908317861/1313500000000000000000000000000000 : ℝ)*base68 + (25268880184169317861/1313500000000000000000000000000000 : ℝ)*base70 + (5286145538274682139/1313500000000000000000000000000000 : ℝ)*base71 + (3194708318881/13135000000000000000000000000 : ℝ)*base73 + (26555075553354317861/1313500000000000000000000000000000 : ℝ)*base76 + (17114807964604817861/1313500000000000000000000000000000 : ℝ)*base78 + (13160962679674182139/1313500000000000000000000000000000 : ℝ)*base79 + (21628705764501/3283750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (55487/7812500000000000000 : ℝ)*base89 + (55487/7812500000000000000 : ℝ)*base91 + (55487/7812500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1239_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2869/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1239_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1239_box_0 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-199756639/1000000000 : ℝ)*x 0 + (2687442589/5000000000 : ℝ)*x 1 + (2687442477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (199756639/1000000000 : ℝ)^527 ≤ (11915180116537/100000000000000 : ℝ)^399 := by
    have hnat : (199756639 : ℕ)^527*100000000000000^399 ≤ 11915180116537^399*1000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199756639 1000000000 11915180116537 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687442589/5000000000 : ℝ)^527 ≤ (11010602786679/25000000000000 : ℝ)^399 := by
    have hnat : (2687442589 : ℕ)^527*25000000000000^399 ≤ 11010602786679^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687442589 5000000000 11010602786679 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687442477/5000000000 : ℝ)^527 ≤ (44042408722409/100000000000000 : ℝ)^399 := by
    have hnat : (2687442477 : ℕ)^527*100000000000000^399 ≤ 44042408722409^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687442477 5000000000 44042408722409 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-199756639/1000000000 : ℝ), (2687442589/5000000000 : ℝ), (2687442477/5000000000 : ℝ)] ![(11915180116537/100000000000000 : ℝ), (11010602786679/25000000000000 : ℝ), (44042408722409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-199756639/1000000000 : ℝ)|^527 ≤ (11915180116537/100000000000000 : ℝ)^399
        have hw : |(-199756639/1000000000 : ℝ)|=(199756639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687442589/5000000000 : ℝ)|^527 ≤ (11010602786679/25000000000000 : ℝ)^399
        have hw : |(2687442589/5000000000 : ℝ)|=(2687442589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687442477/5000000000 : ℝ)|^527 ≤ (44042408722409/100000000000000 : ℝ)^399
        have hw : |(2687442477/5000000000 : ℝ)|=(2687442477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_box_1 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (165524239/312500000 : ℝ)*x 0 + (-1051861141/5000000000 : ℝ)*x 1 + (1074977079/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165524239/312500000 : ℝ)^527 ≤ (2699939026511/6250000000000 : ℝ)^399 := by
    have hnat : (165524239 : ℕ)^527*6250000000000^399 ≤ 2699939026511^399*312500000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165524239 312500000 2699939026511 6250000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051861141/5000000000 : ℝ)^527 ≤ (102068496469/800000000000 : ℝ)^399 := by
    have hnat : (1051861141 : ℕ)^527*800000000000^399 ≤ 102068496469^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051861141 5000000000 102068496469 800000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1074977079/2000000000 : ℝ)^527 ≤ (1376325421727/3125000000000 : ℝ)^399 := by
    have hnat : (1074977079 : ℕ)^527*3125000000000^399 ≤ 1376325421727^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074977079 2000000000 1376325421727 3125000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165524239/312500000 : ℝ), (-1051861141/5000000000 : ℝ), (1074977079/2000000000 : ℝ)] ![(2699939026511/6250000000000 : ℝ), (102068496469/800000000000 : ℝ), (1376325421727/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165524239/312500000 : ℝ)|^527 ≤ (2699939026511/6250000000000 : ℝ)^399
        have hw : |(165524239/312500000 : ℝ)|=(165524239/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1051861141/5000000000 : ℝ)|^527 ≤ (102068496469/800000000000 : ℝ)^399
        have hw : |(-1051861141/5000000000 : ℝ)|=(1051861141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1074977079/2000000000 : ℝ)|^527 ≤ (1376325421727/3125000000000 : ℝ)^399
        have hw : |(1074977079/2000000000 : ℝ)|=(1074977079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_box_2 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (529677693/1000000000 : ℝ)*x 0 + (5374885033/10000000000 : ℝ)*x 1 + (-2103721049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529677693/1000000000 : ℝ)^527 ≤ (43199038233999/100000000000000 : ℝ)^399 := by
    have hnat : (529677693 : ℕ)^527*100000000000000^399 ≤ 43199038233999^399*1000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529677693 1000000000 43199038233999 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374885033/10000000000 : ℝ)^527 ≤ (4404240957741/10000000000000 : ℝ)^399 := by
    have hnat : (5374885033 : ℕ)^527*10000000000000^399 ≤ 4404240957741^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374885033 10000000000 4404240957741 10000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2103721049/10000000000 : ℝ)^527 ≤ (6379276090937/50000000000000 : ℝ)^399 := by
    have hnat : (2103721049 : ℕ)^527*50000000000000^399 ≤ 6379276090937^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103721049 10000000000 6379276090937 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529677693/1000000000 : ℝ), (5374885033/10000000000 : ℝ), (-2103721049/10000000000 : ℝ)] ![(43199038233999/100000000000000 : ℝ), (4404240957741/10000000000000 : ℝ), (6379276090937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529677693/1000000000 : ℝ)|^527 ≤ (43199038233999/100000000000000 : ℝ)^399
        have hw : |(529677693/1000000000 : ℝ)|=(529677693/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5374885033/10000000000 : ℝ)|^527 ≤ (4404240957741/10000000000000 : ℝ)^399
        have hw : |(5374885033/10000000000 : ℝ)|=(5374885033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2103721049/10000000000 : ℝ)|^527 ≤ (6379276090937/50000000000000 : ℝ)^399
        have hw : |(-2103721049/10000000000 : ℝ)|=(2103721049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_box_3 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (445773827/1000000000 : ℝ)*x 0 + (4299954869/10000000000 : ℝ)*x 1 + (2149977337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (445773827/1000000000 : ℝ)^527 ≤ (8599829158379/25000000000000 : ℝ)^399 := by
    have hnat : (445773827 : ℕ)^527*25000000000000^399 ≤ 8599829158379^399*1000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445773827 1000000000 8599829158379 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4299954869/10000000000 : ℝ)^527 ≤ (32800342660921/100000000000000 : ℝ)^399 := by
    have hnat : (4299954869 : ℕ)^527*100000000000000^399 ≤ 32800342660921^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299954869 10000000000 32800342660921 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2149977337/5000000000 : ℝ)^527 ≤ (4100042587033/12500000000000 : ℝ)^399 := by
    have hnat : (2149977337 : ℕ)^527*12500000000000^399 ≤ 4100042587033^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149977337 5000000000 4100042587033 12500000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(445773827/1000000000 : ℝ), (4299954869/10000000000 : ℝ), (2149977337/5000000000 : ℝ)] ![(8599829158379/25000000000000 : ℝ), (32800342660921/100000000000000 : ℝ), (4100042587033/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(445773827/1000000000 : ℝ)|^527 ≤ (8599829158379/25000000000000 : ℝ)^399
        have hw : |(445773827/1000000000 : ℝ)|=(445773827/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4299954869/10000000000 : ℝ)|^527 ≤ (32800342660921/100000000000000 : ℝ)^399
        have hw : |(4299954869/10000000000 : ℝ)|=(4299954869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2149977337/5000000000 : ℝ)|^527 ≤ (4100042587033/12500000000000 : ℝ)^399
        have hw : |(2149977337/5000000000 : ℝ)|=(2149977337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_box_4 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2246508409/10000000000 : ℝ)*x 0 + (330141097/625000000 : ℝ)*x 1 + (2641128793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2246508409/10000000000 : ℝ)^527 ≤ (556583748837/4000000000000 : ℝ)^399 := by
    have hnat : (2246508409 : ℕ)^527*4000000000000^399 ≤ 556583748837^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246508409 10000000000 556583748837 4000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (330141097/625000000 : ℝ)^527 ≤ (43042702948229/100000000000000 : ℝ)^399 := by
    have hnat : (330141097 : ℕ)^527*100000000000000^399 ≤ 43042702948229^399*625000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330141097 625000000 43042702948229 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2641128793/5000000000 : ℝ)^527 ≤ (21521351657079/50000000000000 : ℝ)^399 := by
    have hnat : (2641128793 : ℕ)^527*50000000000000^399 ≤ 21521351657079^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641128793 5000000000 21521351657079 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2246508409/10000000000 : ℝ), (330141097/625000000 : ℝ), (2641128793/5000000000 : ℝ)] ![(556583748837/4000000000000 : ℝ), (43042702948229/100000000000000 : ℝ), (21521351657079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2246508409/10000000000 : ℝ)|^527 ≤ (556583748837/4000000000000 : ℝ)^399
        have hw : |(-2246508409/10000000000 : ℝ)|=(2246508409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(330141097/625000000 : ℝ)|^527 ≤ (43042702948229/100000000000000 : ℝ)^399
        have hw : |(330141097/625000000 : ℝ)|=(330141097/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2641128793/5000000000 : ℝ)|^527 ≤ (21521351657079/50000000000000 : ℝ)^399
        have hw : |(2641128793/5000000000 : ℝ)|=(2641128793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_box_5 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5362076207/10000000000 : ℝ)*x 0 + (-2140434859/10000000000 : ℝ)*x 1 + (165070547/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362076207/10000000000 : ℝ)^527 ≤ (8780767048217/20000000000000 : ℝ)^399 := by
    have hnat : (5362076207 : ℕ)^527*20000000000000^399 ≤ 8780767048217^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362076207 10000000000 8780767048217 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2140434859/10000000000 : ℝ)^527 ≤ (13053462305593/100000000000000 : ℝ)^399 := by
    have hnat : (2140434859 : ℕ)^527*100000000000000^399 ≤ 13053462305593^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140434859 10000000000 13053462305593 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165070547/312500000 : ℝ)^527 ≤ (5380337803953/12500000000000 : ℝ)^399 := by
    have hnat : (165070547 : ℕ)^527*12500000000000^399 ≤ 5380337803953^399*312500000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165070547 312500000 5380337803953 12500000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362076207/10000000000 : ℝ), (-2140434859/10000000000 : ℝ), (165070547/312500000 : ℝ)] ![(8780767048217/20000000000000 : ℝ), (13053462305593/100000000000000 : ℝ), (5380337803953/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362076207/10000000000 : ℝ)|^527 ≤ (8780767048217/20000000000000 : ℝ)^399
        have hw : |(5362076207/10000000000 : ℝ)|=(5362076207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2140434859/10000000000 : ℝ)|^527 ≤ (13053462305593/100000000000000 : ℝ)^399
        have hw : |(-2140434859/10000000000 : ℝ)|=(2140434859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(165070547/312500000 : ℝ)|^527 ≤ (5380337803953/12500000000000 : ℝ)^399
        have hw : |(165070547/312500000 : ℝ)|=(165070547/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_box_6 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5362076177/10000000000 : ℝ)*x 0 + (660282203/1250000000 : ℝ)*x 1 + (-2140434739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362076177/10000000000 : ℝ)^527 ≤ (43903834916649/100000000000000 : ℝ)^399 := by
    have hnat : (5362076177 : ℕ)^527*100000000000000^399 ≤ 43903834916649^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362076177 10000000000 43903834916649 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660282203/1250000000 : ℝ)^527 ≤ (43042703723137/100000000000000 : ℝ)^399 := by
    have hnat : (660282203 : ℕ)^527*100000000000000^399 ≤ 43042703723137^399*1250000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660282203 1250000000 43042703723137 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2140434739/10000000000 : ℝ)^527 ≤ (6526730669501/50000000000000 : ℝ)^399 := by
    have hnat : (2140434739 : ℕ)^527*50000000000000^399 ≤ 6526730669501^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140434739 10000000000 6526730669501 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362076177/10000000000 : ℝ), (660282203/1250000000 : ℝ), (-2140434739/10000000000 : ℝ)] ![(43903834916649/100000000000000 : ℝ), (43042703723137/100000000000000 : ℝ), (6526730669501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362076177/10000000000 : ℝ)|^527 ≤ (43903834916649/100000000000000 : ℝ)^399
        have hw : |(5362076177/10000000000 : ℝ)|=(5362076177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(660282203/1250000000 : ℝ)|^527 ≤ (43042703723137/100000000000000 : ℝ)^399
        have hw : |(660282203/1250000000 : ℝ)|=(660282203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2140434739/10000000000 : ℝ)|^527 ≤ (6526730669501/50000000000000 : ℝ)^399
        have hw : |(-2140434739/10000000000 : ℝ)|=(2140434739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_box_7 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (265264701/625000000 : ℝ)*x 0 + (4406686107/10000000000 : ℝ)*x 1 + (4406686263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265264701/625000000 : ℝ)^527 ≤ (8060032050367/25000000000000 : ℝ)^399 := by
    have hnat : (265264701 : ℕ)^527*25000000000000^399 ≤ 8060032050367^399*625000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265264701 625000000 8060032050367 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4406686107/10000000000 : ℝ)^527 ≤ (4234991887327/12500000000000 : ℝ)^399 := by
    have hnat : (4406686107 : ℕ)^527*12500000000000^399 ≤ 4234991887327^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4406686107 10000000000 4234991887327 12500000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4406686263/10000000000 : ℝ)^527 ≤ (33879936682753/100000000000000 : ℝ)^399 := by
    have hnat : (4406686263 : ℕ)^527*100000000000000^399 ≤ 33879936682753^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4406686263 10000000000 33879936682753 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265264701/625000000 : ℝ), (4406686107/10000000000 : ℝ), (4406686263/10000000000 : ℝ)] ![(8060032050367/25000000000000 : ℝ), (4234991887327/12500000000000 : ℝ), (33879936682753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265264701/625000000 : ℝ)|^527 ≤ (8060032050367/25000000000000 : ℝ)^399
        have hw : |(265264701/625000000 : ℝ)|=(265264701/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4406686107/10000000000 : ℝ)|^527 ≤ (4234991887327/12500000000000 : ℝ)^399
        have hw : |(4406686107/10000000000 : ℝ)|=(4406686107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4406686263/10000000000 : ℝ)|^527 ≤ (33879936682753/100000000000000 : ℝ)^399
        have hw : |(4406686263/10000000000 : ℝ)|=(4406686263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_box_8 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1097172969/5000000000 : ℝ)*x 0 + (1043816229/2000000000 : ℝ)*x 1 + (2692248871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097172969/5000000000 : ℝ)^527 ≤ (13489456402051/100000000000000 : ℝ)^399 := by
    have hnat : (1097172969 : ℕ)^527*100000000000000^399 ≤ 13489456402051^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097172969 5000000000 13489456402051 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043816229/2000000000 : ℝ)^527 ≤ (8472813551339/20000000000000 : ℝ)^399 := by
    have hnat : (1043816229 : ℕ)^527*20000000000000^399 ≤ 8472813551339^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043816229 2000000000 8472813551339 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692248871/5000000000 : ℝ)^527 ≤ (8829295166403/20000000000000 : ℝ)^399 := by
    have hnat : (2692248871 : ℕ)^527*20000000000000^399 ≤ 8829295166403^399*5000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692248871 5000000000 8829295166403 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1097172969/5000000000 : ℝ), (1043816229/2000000000 : ℝ), (2692248871/5000000000 : ℝ)] ![(13489456402051/100000000000000 : ℝ), (8472813551339/20000000000000 : ℝ), (8829295166403/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1097172969/5000000000 : ℝ)|^527 ≤ (13489456402051/100000000000000 : ℝ)^399
        have hw : |(-1097172969/5000000000 : ℝ)|=(1097172969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043816229/2000000000 : ℝ)|^527 ≤ (8472813551339/20000000000000 : ℝ)^399
        have hw : |(1043816229/2000000000 : ℝ)|=(1043816229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692248871/5000000000 : ℝ)|^527 ≤ (8829295166403/20000000000000 : ℝ)^399
        have hw : |(2692248871/5000000000 : ℝ)|=(2692248871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_box_9 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5289996567/10000000000 : ℝ)*x 0 + (-209984479/1000000000 : ℝ)*x 1 + (1076899519/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289996567/10000000000 : ℝ)^527 ≤ (10781503632769/25000000000000 : ℝ)^399 := by
    have hnat : (5289996567 : ℕ)^527*25000000000000^399 ≤ 10781503632769^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289996567 10000000000 10781503632769 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209984479/1000000000 : ℝ)^527 ≤ (6363755604637/50000000000000 : ℝ)^399 := by
    have hnat : (209984479 : ℕ)^527*50000000000000^399 ≤ 6363755604637^399*1000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209984479 1000000000 6363755604637 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076899519/2000000000 : ℝ)^527 ≤ (44146474240151/100000000000000 : ℝ)^399 := by
    have hnat : (1076899519 : ℕ)^527*100000000000000^399 ≤ 44146474240151^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076899519 2000000000 44146474240151 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289996567/10000000000 : ℝ), (-209984479/1000000000 : ℝ), (1076899519/2000000000 : ℝ)] ![(10781503632769/25000000000000 : ℝ), (6363755604637/50000000000000 : ℝ), (44146474240151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289996567/10000000000 : ℝ)|^527 ≤ (10781503632769/25000000000000 : ℝ)^399
        have hw : |(5289996567/10000000000 : ℝ)|=(5289996567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-209984479/1000000000 : ℝ)|^527 ≤ (6363755604637/50000000000000 : ℝ)^399
        have hw : |(-209984479/1000000000 : ℝ)|=(209984479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1076899519/2000000000 : ℝ)|^527 ≤ (44146474240151/100000000000000 : ℝ)^399
        have hw : |(1076899519/2000000000 : ℝ)|=(1076899519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_box_10 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5289996501/10000000000 : ℝ)*x 0 + (5384497823/10000000000 : ℝ)*x 1 + (-2099844571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289996501/10000000000 : ℝ)^527 ≤ (4312601382041/10000000000000 : ℝ)^399 := by
    have hnat : (5289996501 : ℕ)^527*10000000000000^399 ≤ 4312601382041^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289996501 10000000000 4312601382041 10000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5384497823/10000000000 : ℝ)^527 ≤ (8829295341833/20000000000000 : ℝ)^399 := by
    have hnat : (5384497823 : ℕ)^527*20000000000000^399 ≤ 8829295341833^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384497823 10000000000 8829295341833 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2099844571/10000000000 : ℝ)^527 ≤ (12727509456047/100000000000000 : ℝ)^399 := by
    have hnat : (2099844571 : ℕ)^527*100000000000000^399 ≤ 12727509456047^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099844571 10000000000 12727509456047 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289996501/10000000000 : ℝ), (5384497823/10000000000 : ℝ), (-2099844571/10000000000 : ℝ)] ![(4312601382041/10000000000000 : ℝ), (8829295341833/20000000000000 : ℝ), (12727509456047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289996501/10000000000 : ℝ)|^527 ≤ (4312601382041/10000000000000 : ℝ)^399
        have hw : |(5289996501/10000000000 : ℝ)|=(5289996501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5384497823/10000000000 : ℝ)|^527 ≤ (8829295341833/20000000000000 : ℝ)^399
        have hw : |(5384497823/10000000000 : ℝ)|=(5384497823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2099844571/10000000000 : ℝ)|^527 ≤ (12727509456047/100000000000000 : ℝ)^399
        have hw : |(-2099844571/10000000000 : ℝ)|=(2099844571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_box_11 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (55995269/125000000 : ℝ)*x 0 + (4288872531/10000000000 : ℝ)*x 1 + (4288872727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (55995269/125000000 : ℝ)^527 ≤ (2163908319347/6250000000000 : ℝ)^399 := by
    have hnat : (55995269 : ℕ)^527*6250000000000^399 ≤ 2163908319347^399*125000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55995269 125000000 2163908319347 6250000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4288872531/10000000000 : ℝ)^527 ≤ (16344366226989/50000000000000 : ℝ)^399 := by
    have hnat : (4288872531 : ℕ)^527*50000000000000^399 ≤ 16344366226989^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288872531 10000000000 16344366226989 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4288872727/10000000000 : ℝ)^527 ≤ (8172183606769/25000000000000 : ℝ)^399 := by
    have hnat : (4288872727 : ℕ)^527*25000000000000^399 ≤ 8172183606769^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288872727 10000000000 8172183606769 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(55995269/125000000 : ℝ), (4288872531/10000000000 : ℝ), (4288872727/10000000000 : ℝ)] ![(2163908319347/6250000000000 : ℝ), (16344366226989/50000000000000 : ℝ), (8172183606769/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(55995269/125000000 : ℝ)|^527 ≤ (2163908319347/6250000000000 : ℝ)^399
        have hw : |(55995269/125000000 : ℝ)|=(55995269/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4288872531/10000000000 : ℝ)|^527 ≤ (16344366226989/50000000000000 : ℝ)^399
        have hw : |(4288872531/10000000000 : ℝ)|=(4288872531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4288872727/10000000000 : ℝ)|^527 ≤ (8172183606769/25000000000000 : ℝ)^399
        have hw : |(4288872727/10000000000 : ℝ)|=(4288872727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_box_12 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2049989983/10000000000 : ℝ)*x 0 + (1359212811/2500000000 : ℝ)*x 1 + (5274179553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049989983/10000000000 : ℝ)^527 ≤ (3082480412127/25000000000000 : ℝ)^399 := by
    have hnat : (2049989983 : ℕ)^527*25000000000000^399 ≤ 3082480412127^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049989983 10000000000 3082480412127 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359212811/2500000000 : ℝ)^527 ≤ (22357147209503/50000000000000 : ℝ)^399 := by
    have hnat : (1359212811 : ℕ)^527*50000000000000^399 ≤ 22357147209503^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359212811 2500000000 22357147209503 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274179553/10000000000 : ℝ)^527 ≤ (1342368247283/3125000000000 : ℝ)^399 := by
    have hnat : (5274179553 : ℕ)^527*3125000000000^399 ≤ 1342368247283^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274179553 10000000000 1342368247283 3125000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2049989983/10000000000 : ℝ), (1359212811/2500000000 : ℝ), (5274179553/10000000000 : ℝ)] ![(3082480412127/25000000000000 : ℝ), (22357147209503/50000000000000 : ℝ), (1342368247283/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2049989983/10000000000 : ℝ)|^527 ≤ (3082480412127/25000000000000 : ℝ)^399
        have hw : |(-2049989983/10000000000 : ℝ)|=(2049989983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359212811/2500000000 : ℝ)|^527 ≤ (22357147209503/50000000000000 : ℝ)^399
        have hw : |(1359212811/2500000000 : ℝ)|=(1359212811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274179553/10000000000 : ℝ)|^527 ≤ (1342368247283/3125000000000 : ℝ)^399
        have hw : |(5274179553/10000000000 : ℝ)|=(5274179553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_box_13 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (268388447/500000000 : ℝ)*x 0 + (-2143580137/10000000000 : ℝ)*x 1 + (210967193/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268388447/500000000 : ℝ)^527 ≤ (8793081978033/20000000000000 : ℝ)^399 := by
    have hnat : (268388447 : ℕ)^527*20000000000000^399 ≤ 8793081978033^399*500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268388447 500000000 8793081978033 20000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2143580137/10000000000 : ℝ)^527 ≤ (3269700812251/25000000000000 : ℝ)^399 := by
    have hnat : (2143580137 : ℕ)^527*25000000000000^399 ≤ 3269700812251^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143580137 10000000000 3269700812251 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210967193/400000000 : ℝ)^527 ≤ (859115736781/2000000000000 : ℝ)^399 := by
    have hnat : (210967193 : ℕ)^527*2000000000000^399 ≤ 859115736781^399*400000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210967193 400000000 859115736781 2000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268388447/500000000 : ℝ), (-2143580137/10000000000 : ℝ), (210967193/400000000 : ℝ)] ![(8793081978033/20000000000000 : ℝ), (3269700812251/25000000000000 : ℝ), (859115736781/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268388447/500000000 : ℝ)|^527 ≤ (8793081978033/20000000000000 : ℝ)^399
        have hw : |(268388447/500000000 : ℝ)|=(268388447/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2143580137/10000000000 : ℝ)|^527 ≤ (3269700812251/25000000000000 : ℝ)^399
        have hw : |(-2143580137/10000000000 : ℝ)|=(2143580137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210967193/400000000 : ℝ)|^527 ≤ (859115736781/2000000000000 : ℝ)^399
        have hw : |(210967193/400000000 : ℝ)|=(210967193/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_box_14 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5367769253/10000000000 : ℝ)*x 0 + (5274179709/10000000000 : ℝ)*x 1 + (-66986871/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367769253/10000000000 : ℝ)^527 ≤ (21982706638131/50000000000000 : ℝ)^399 := by
    have hnat : (5367769253 : ℕ)^527*50000000000000^399 ≤ 21982706638131^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367769253 10000000000 21982706638131 50000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5274179709/10000000000 : ℝ)^527 ≤ (42955785591199/100000000000000 : ℝ)^399 := by
    have hnat : (5274179709 : ℕ)^527*100000000000000^399 ≤ 42955785591199^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274179709 10000000000 42955785591199 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66986871/312500000 : ℝ)^527 ≤ (3269700278361/25000000000000 : ℝ)^399 := by
    have hnat : (66986871 : ℕ)^527*25000000000000^399 ≤ 3269700278361^399*312500000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66986871 312500000 3269700278361 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367769253/10000000000 : ℝ), (5274179709/10000000000 : ℝ), (-66986871/312500000 : ℝ)] ![(21982706638131/50000000000000 : ℝ), (42955785591199/100000000000000 : ℝ), (3269700278361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367769253/10000000000 : ℝ)|^527 ≤ (21982706638131/50000000000000 : ℝ)^399
        have hw : |(5367769253/10000000000 : ℝ)|=(5367769253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5274179709/10000000000 : ℝ)|^527 ≤ (42955785591199/100000000000000 : ℝ)^399
        have hw : |(5274179709/10000000000 : ℝ)|=(5274179709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-66986871/312500000 : ℝ)|^527 ≤ (3269700278361/25000000000000 : ℝ)^399
        have hw : |(-66986871/312500000 : ℝ)|=(66986871/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1239_box_15 (p : ℝ) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ)) (x : Fin 3 → ℝ) :
    (845076741/2000000000 : ℝ)*x 0 + (1103997399/2500000000 : ℝ)*x 1 + (4415988911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (845076741/2000000000 : ℝ)^527 ≤ (8012781010057/25000000000000 : ℝ)^399 := by
    have hnat : (845076741 : ℕ)^527*25000000000000^399 ≤ 8012781010057^399*2000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845076741 2000000000 8012781010057 25000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103997399/2500000000 : ℝ)^527 ≤ (33974441449993/100000000000000 : ℝ)^399 := by
    have hnat : (1103997399 : ℕ)^527*100000000000000^399 ≤ 33974441449993^399*2500000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103997399 2500000000 33974441449993 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4415988911/10000000000 : ℝ)^527 ≤ (33974434489299/100000000000000 : ℝ)^399 := by
    have hnat : (4415988911 : ℕ)^527*100000000000000^399 ≤ 33974434489299^399*10000000000^527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4415988911 10000000000 33974434489299 100000000000000 527 399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (527/128 : ℝ)) 527 399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(845076741/2000000000 : ℝ), (1103997399/2500000000 : ℝ), (4415988911/10000000000 : ℝ)] ![(8012781010057/25000000000000 : ℝ), (33974441449993/100000000000000 : ℝ), (33974434489299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(845076741/2000000000 : ℝ)|^527 ≤ (8012781010057/25000000000000 : ℝ)^399
        have hw : |(845076741/2000000000 : ℝ)|=(845076741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1103997399/2500000000 : ℝ)|^527 ≤ (33974441449993/100000000000000 : ℝ)^399
        have hw : |(1103997399/2500000000 : ℝ)|=(1103997399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4415988911/10000000000 : ℝ)|^527 ≤ (33974434489299/100000000000000 : ℝ)^399
        have hw : |(4415988911/10000000000 : ℝ)|=(4415988911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1239_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2869/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31123/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(19/32 : ℝ) ∧ (801/1000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83339/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7051/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2869/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7051/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2869/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7051/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2869/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7051/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2869/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7051/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2869/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7051/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2869/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2869/25000 : ℝ) ^ (8431/2048 : ℝ) ≤ (13472259787631367/100000000000000000000 : ℝ) := by
    have hpowers : (2869/25000 : ℝ)^8431 ≤ (13472259787631367/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2869 : ℕ)^8431*100000000000000000000^2048 ≤ 13472259787631367^2048*25000^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2869 25000 13472259787631367 100000000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2869/25000 : ℝ)) (X := (13472259787631367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7051/50000 : ℝ) ^ (8431/2048 : ℝ) ≤ (15733109642225741/50000000000000000000 : ℝ) := by
    have hpowers : (7051/50000 : ℝ)^8431 ≤ (15733109642225741/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7051 : ℕ)^8431*50000000000000000000^2048 ≤ 15733109642225741^2048*50000^8431 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7051 50000 15733109642225741 50000000000000000000 8431 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7051/50000 : ℝ)) (X := (15733109642225741/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013472259787631367/50000000000000000000 : ℝ) ≤ (10000654450819083/10000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (50013472259787631367/50000000000000000000 : ℝ)^2048 ≤ (10000654450819083/10000000000000000 : ℝ)^8431 := by
      have hnat : (50013472259787631367 : ℕ)^2048*10000000000000000^8431 ≤ 10000654450819083^8431*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013472259787631367 50000000000000000000 10000654450819083 10000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000654450819083/10000000000000000 : ℝ)) (X := (50013472259787631367/50000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044938479072082849/100000000000000000000 : ℝ) ≤ (5000545714347053/5000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (100044938479072082849/100000000000000000000 : ℝ)^2048 ≤ (5000545714347053/5000000000000000 : ℝ)^8431 := by
      have hnat : (100044938479072082849 : ℕ)^2048*5000000000000000^8431 ≤ 5000545714347053^8431*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044938479072082849 100000000000000000000 5000545714347053 5000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000545714347053/5000000000000000 : ℝ)) (X := (100044938479072082849/100000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015733109642225741/25000000000000000000 : ℝ) ≤ (10001528406569129/10000000000000000 : ℝ) ^ (8431/2048 : ℝ) := by
    have hpowers : (25015733109642225741/25000000000000000000 : ℝ)^2048 ≤ (10001528406569129/10000000000000000 : ℝ)^8431 := by
      have hnat : (25015733109642225741 : ℕ)^2048*10000000000000000^8431 ≤ 10001528406569129^8431*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015733109642225741 25000000000000000000 10001528406569129 10000000000000000 2048 8431 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001528406569129/10000000000000000 : ℝ)) (X := (25015733109642225741/25000000000000000000 : ℝ)) (by norm_num) 8431 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13472259787631367/100000000000000000000 : ℝ) ≤ ((13125844535831692031/13130000000000000000 : ℝ)+2*(436977875023/262600000000000 : ℝ)*(2869/25000 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (13125844535831692031/13130000000000000000 : ℝ)+2*(436977875023/262600000000000 : ℝ)*(2869/25000 : ℝ)=(10000654450819083/10000000000000000 : ℝ) by norm_num, show 1+2*(13472259787631367/100000000000000000000 : ℝ)=(50013472259787631367/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15733109642225741/50000000000000000000 : ℝ)+(13472259787631367/100000000000000000000 : ℝ) ≤ ((13125844535831692031/13130000000000000000 : ℝ)+(436977875023/262600000000000 : ℝ)*((7051/50000 : ℝ)+(2869/25000 : ℝ)))^(8431/2048 : ℝ) := by
    rw [show (13125844535831692031/13130000000000000000 : ℝ)+(436977875023/262600000000000 : ℝ)*((7051/50000 : ℝ)+(2869/25000 : ℝ))=(5000545714347053/5000000000000000 : ℝ) by norm_num, show 1+(15733109642225741/50000000000000000000 : ℝ)+(13472259787631367/100000000000000000000 : ℝ)=(100044938479072082849/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15733109642225741/50000000000000000000 : ℝ) ≤ ((13125844535831692031/13130000000000000000 : ℝ)+2*(436977875023/262600000000000 : ℝ)*(7051/50000 : ℝ))^(8431/2048 : ℝ) := by
    rw [show (13125844535831692031/13130000000000000000 : ℝ)+2*(436977875023/262600000000000 : ℝ)*(7051/50000 : ℝ)=(10001528406569129/10000000000000000 : ℝ) by norm_num, show 1+2*(15733109642225741/50000000000000000000 : ℝ)=(25015733109642225741/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13125844535831692031/13130000000000000000 : ℝ)*(X 1 0+X 2 0)+(436977875023/262600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (2869/25000 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (13125844535831692031/13130000000000000000 : ℝ)) (alpha := (436977875023/262600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13125844535831692031/13130000000000000000 : ℝ)*(X 0 1+X 2 1)+(436977875023/262600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (2869/25000 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (13125844535831692031/13130000000000000000 : ℝ)) (alpha := (436977875023/262600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13125844535831692031/13130000000000000000 : ℝ)*(X 0 2+X 1 2)+(436977875023/262600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8431/2048 : ℝ)) (lo := (2869/25000 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (13125844535831692031/13130000000000000000 : ℝ)) (alpha := (436977875023/262600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-199756639/1000000000 : ℝ)*X 0 0+(2687442589/5000000000 : ℝ)*X 0 1+(2687442477/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((165524239/312500000 : ℝ)*X 1 0+(-1051861141/5000000000 : ℝ)*X 1 1+(1074977079/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((529677693/1000000000 : ℝ)*X 2 0+(5374885033/10000000000 : ℝ)*X 2 1+(-2103721049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((445773827/1000000000 : ℝ)*X 0 0+(4299954869/10000000000 : ℝ)*X 0 1+(2149977337/5000000000 : ℝ)*X 0 2+(445773827/1000000000 : ℝ)*X 1 0+(4299954869/10000000000 : ℝ)*X 1 1+(2149977337/5000000000 : ℝ)*X 1 2+(445773827/1000000000 : ℝ)*X 2 0+(4299954869/10000000000 : ℝ)*X 2 1+(2149977337/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2246508409/10000000000 : ℝ)*X 0 0+(330141097/625000000 : ℝ)*X 0 1+(2641128793/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362076207/10000000000 : ℝ)*X 1 0+(-2140434859/10000000000 : ℝ)*X 1 1+(165070547/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362076177/10000000000 : ℝ)*X 2 0+(660282203/1250000000 : ℝ)*X 2 1+(-2140434739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((265264701/625000000 : ℝ)*X 0 0+(4406686107/10000000000 : ℝ)*X 0 1+(4406686263/10000000000 : ℝ)*X 0 2+(265264701/625000000 : ℝ)*X 1 0+(4406686107/10000000000 : ℝ)*X 1 1+(4406686263/10000000000 : ℝ)*X 1 2+(265264701/625000000 : ℝ)*X 2 0+(4406686107/10000000000 : ℝ)*X 2 1+(4406686263/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1097172969/5000000000 : ℝ)*X 0 0+(1043816229/2000000000 : ℝ)*X 0 1+(2692248871/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289996567/10000000000 : ℝ)*X 1 0+(-209984479/1000000000 : ℝ)*X 1 1+(1076899519/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289996501/10000000000 : ℝ)*X 2 0+(5384497823/10000000000 : ℝ)*X 2 1+(-2099844571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((55995269/125000000 : ℝ)*X 0 0+(4288872531/10000000000 : ℝ)*X 0 1+(4288872727/10000000000 : ℝ)*X 0 2+(55995269/125000000 : ℝ)*X 1 0+(4288872531/10000000000 : ℝ)*X 1 1+(4288872727/10000000000 : ℝ)*X 1 2+(55995269/125000000 : ℝ)*X 2 0+(4288872531/10000000000 : ℝ)*X 2 1+(4288872727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2049989983/10000000000 : ℝ)*X 0 0+(1359212811/2500000000 : ℝ)*X 0 1+(5274179553/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((268388447/500000000 : ℝ)*X 1 0+(-2143580137/10000000000 : ℝ)*X 1 1+(210967193/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5367769253/10000000000 : ℝ)*X 2 0+(5274179709/10000000000 : ℝ)*X 2 1+(-66986871/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((845076741/2000000000 : ℝ)*X 0 0+(1103997399/2500000000 : ℝ)*X 0 1+(4415988911/10000000000 : ℝ)*X 0 2+(845076741/2000000000 : ℝ)*X 1 0+(1103997399/2500000000 : ℝ)*X 1 1+(4415988911/10000000000 : ℝ)*X 1 2+(845076741/2000000000 : ℝ)*X 2 0+(1103997399/2500000000 : ℝ)*X 2 1+(4415988911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1239_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31123/50000 : ℝ) ≤ (-102157161905256701149065951857409/164125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60141179/50000000000000 : ℝ)*(upper0) + (136658893/100000000000000 : ℝ)*(upper1) + (72474007/100000000000000 : ℝ)*(upper3) + (185563689/100000000000000 : ℝ)*(upper5) + (1000232272967413/25000000000000 : ℝ)*(major0) + (1000232272967413/25000000000000 : ℝ)*(major1) + (1000232272967413/25000000000000 : ℝ)*(major2) + (2471398517/100000000000000 : ℝ)*(sp1) + (1154294411/12500000000000 : ℝ)*(sp3) + (537945257299199/10000000000000 : ℝ)*(sp4) + (1344863575997923/25000000000000 : ℝ)*(sp5) + (5379456775390209/100000000000000 : ℝ)*(sp6) + (660785002721867/25000000000000 : ℝ)*(sp7) + (4202398219/100000000000000 : ℝ)*(sp8) + (2643149245242757/100000000000000 : ℝ)*(f.failure) + (5379456775390209/100000000000000 : ℝ)*(f.sum) + (15916620911729/3282500000000000000000000000 : ℝ)*base65 + (6590469843230014197/328250000000000000000000000000000 : ℝ)*base68 + (9313133595379235803/328250000000000000000000000000000 : ℝ)*base69 + (4508602264188735803/328250000000000000000000000000000 : ℝ)*base71 + (21232283472649/820625000000000000000000000 : ℝ)*base74 + (13454480568632985803/328250000000000000000000000000000 : ℝ)*base75 + (4045715690581485803/328250000000000000000000000000000 : ℝ)*base77 + (5962762023143264197/328250000000000000000000000000000 : ℝ)*base80 + (10282422944927/6565000000000000000000000000 : ℝ)*base82 + (455473/625000000000000000000 : ℝ)*base90 + (455473/625000000000000000000 : ℝ)*base92 + (455473/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (19/32 : ℝ) ≤ (389813012280127776252508910042337/656500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (445151283/100000000000000 : ℝ)*(lower1) + (489271653/100000000000000 : ℝ)*(lower2) + (508970859/100000000000000 : ℝ)*(upper4) + (4066702931927509/100000000000000 : ℝ)*(major0) + (4066702931927509/100000000000000 : ℝ)*(major1) + (4066702931927509/100000000000000 : ℝ)*(major2) + (1085398691401837/20000000000000 : ℝ)*(sp0) + (2713389666053119/50000000000000 : ℝ)*(sp1) + (5426989505441181/100000000000000 : ℝ)*(sp2) + (1343291276620977/50000000000000 : ℝ)*(sp3) + (11100521357/50000000000000 : ℝ)*(sp6) + (9559051631/50000000000000 : ℝ)*(sp7) + (1824947471/10000000000000 : ℝ)*(sp8) + (29046797207/12500000000000 : ℝ)*(sp9) + (41978151114769/1562500000000 : ℝ)*(f.failure) + (1085402341296779/20000000000000 : ℝ)*(f.sum) + (43806059736247/13130000000000000000000000000 : ℝ)*base65 + (10192131230129669221/1313000000000000000000000000000000 : ℝ)*base68 + (9395182603265669221/1313000000000000000000000000000000 : ℝ)*base70 + (3011590800833669221/1313000000000000000000000000000000 : ℝ)*base72 + (50042107645813/13130000000000000000000000000 : ℝ)*base74 + (5584934158474330779/1313000000000000000000000000000000 : ℝ)*base75 + (5781859673650330779/1313000000000000000000000000000000 : ℝ)*base77 + (8633853152006669221/1313000000000000000000000000000000 : ℝ)*base80 + (1305841233603/13130000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (252311/39062500000000000000 : ℝ)*base89 + (252311/39062500000000000000 : ℝ)*base91 + (252311/39062500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (801/1000 : ℝ) ≤ (20225895460447626847836952387317/25250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76874571/50000000000000 : ℝ)*(lower3) + (6241713/20000000000000 : ℝ)*(upper4) + (3297293/100000000000000 : ℝ)*(lower5) + (2266764671874599/50000000000000 : ℝ)*(major0) + (2266764671874599/50000000000000 : ℝ)*(major1) + (2266764671874599/50000000000000 : ℝ)*(major2) + (5374796903/100000000000000 : ℝ)*(sp0) + (284668767/390625000000 : ℝ)*(sp1) + (177732997489/100000000000000 : ℝ)*(sp2) + (19032948297/25000000000000 : ℝ)*(sp3) + (1511337363260079/25000000000000 : ℝ)*(sp8) + (3022640976316433/50000000000000 : ℝ)*(sp9) + (6045177094839729/100000000000000 : ℝ)*(sp10) + (149746343788749/5000000000000 : ℝ)*(sp11) + (374375375946021/12500000000000 : ℝ)*(f.failure) + (3022677413918609/50000000000000 : ℝ)*(f.sum) + (925339919081/505000000000000000000000000 : ℝ)*base66 + (329820336771579187/50500000000000000000000000000000 : ℝ)*base68 + (738811898171579187/50500000000000000000000000000000 : ℝ)*base70 + (920251851957579187/50500000000000000000000000000000 : ℝ)*base72 + (1520213700089/505000000000000000000000000 : ℝ)*base73 + (679359883159579187/50500000000000000000000000000000 : ℝ)*base76 + (344568308948079187/50500000000000000000000000000000 : ℝ)*base78 + (548568487546579187/50500000000000000000000000000000 : ℝ)*base80 + (1753022884931/505000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (741331/78125000000000000000 : ℝ)*base89 + (741331/78125000000000000000 : ℝ)*base91 + (741331/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-83339/100000 : ℝ) ≤ (-21042495247978182081219782644359/25250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1388181/800000000000 : ℝ)*(lower0) + (532077/20000000000000 : ℝ)*(upper1) + (38482289/20000000000000 : ℝ)*(lower2) + (41913079/25000000000000 : ℝ)*(upper3) + (18749443/6250000000000 : ℝ)*(upper5) + (2284495428526227/50000000000000 : ℝ)*(major0) + (2284495428526227/50000000000000 : ℝ)*(major1) + (2284495428526227/50000000000000 : ℝ)*(major2) + (2742571701/100000000000000 : ℝ)*(sp4) + (16604641831/10000000000000 : ℝ)*(sp7) + (6147327759025439/100000000000000 : ℝ)*(sp12) + (6147330501597141/100000000000000 : ℝ)*(sp13) + (6147330501597141/100000000000000 : ℝ)*(sp14) + (11790093897281/390625000000 : ℝ)*(sp15) + (1509215042061123/50000000000000 : ℝ)*(f.failure) + (6147330501597141/100000000000000 : ℝ)*(f.sum) + (15248934811389/6565000000000000000000000000 : ℝ)*base66 + (10248606893729552963/656500000000000000000000000000000 : ℝ)*base68 + (4623026018432052963/656500000000000000000000000000000 : ℝ)*base70 + (8423252816988552963/656500000000000000000000000000000 : ℝ)*base72 + (2286283468409/1641250000000000000000000000 : ℝ)*base73 + (9220533445750052963/656500000000000000000000000000000 : ℝ)*base76 + (6453690536803052963/656500000000000000000000000000000 : ℝ)*base78 + (32169850848736052963/656500000000000000000000000000000 : ℝ)*base80 + (6930742534411/6565000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (4176153/312500000000000000000 : ℝ)*base89 + (4176153/312500000000000000000 : ℝ)*base91 + (4176153/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1239_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2869/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31123/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(19/32 : ℝ) else (801/1000 : ℝ) ≤ X j i ∧ X j i ≤ (83339/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1239_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1239_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31123/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(19/32 : ℝ) else (801/1000 : ℝ) ≤ X j i ∧ X j i ≤ (83339/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1239_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1239_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8431/2048 : ℝ) ≤ p) (hpb : p ≤ (527/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9460611/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (459/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31123/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(19/32 : ℝ) else (801/1000 : ℝ) ≤ X j i ∧ X j i ≤ (83339/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1239_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
